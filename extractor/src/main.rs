//! Extracts the constraints and bus interactions of Pico's RV64IM chips into the Lean modules
//! under `PicoFV/RV64IM/Extraction/`.
//!
//!   cargo run --release -- <out_dir>           write one `<Name>.lean` per chip and gadget,
//!                                              except those listed in pending.txt
//!   cargo run --release -- --all <out_dir>     write every file, pending ones included
//!   cargo run --release -- --check <out_dir>   fail unless the files there are up to date
//!   cargo run --release -- --list              print the names of all RISC-V chips in this Pico
//!   cargo run --release -- --compare <dir>     print, per file, whether this Pico's extraction
//!                                              differs from the one in <dir>, first line ignored
//!   cargo run --release -- --lists             print Pico's two RISC-V chip lists and where the
//!                                              extracted chips stand in them
//!
//! `--compare` and `--lists` serve `scripts/ci/drift.sh`, which runs them against a copy of this
//! crate re-pointed at a Pico branch; they make no claim about the pin.

mod gadgets;
mod render;

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

use p3_air::{Air, BaseAir};
use p3_koala_bear::KoalaBear;
use pico_mle_core::air::{
    any_air::BaseAirWithPublicValues,
    symbolic::{get_symbolic_builder, SymbolicRapBuilder},
};
use pico_mle_core::{get_air_name, keygen::types::TraceWidth};
use pico_vm::{
    chips::chips::{
        alu::{
            add::AddChip, addw::AddwChip, bitwise::BitwiseChip, divrem::DivRemChip, lt::LtChip,
            mul::MulChip, sll::SLLChip, sr::traces::ShiftRightChip, sub::SubChip, subw::SubwChip,
        },
        riscv_cpu::CpuChip,
        riscv_memory::{read_write::MemoryReadWriteChip, unaligned::MemoryUnalignedChip},
    },
    compiler::riscv::program::Program,
    instances::chiptype::riscv_chiptype::RiscvChipType,
    machine::chip::ChipBehavior,
    mle::machine::riscv::mle_riscv_air_refs,
};
use render::{pair_interaction_meta, render_module, ExtractedAir};

type F = KoalaBear;

/// The Pico commit that `PICO_TAG` resolves to in `Cargo.lock`.
const PICO_REV: &str = "fcfa504624657d0c417c43f1233d5d891f293ff9";
/// The Pico release tag `Cargo.toml` pins. `pico_pin_matches_cargo` checks it against
/// `Cargo.toml`, and `PICO_REV` against the commit `Cargo.lock` resolves it to.
/// `soundness_facts.py` prints both in the documents' pin blocks.
const PICO_TAG: &str = "v3.2.0";

/// Files in the extraction directory that this tool does not generate.
const HAND_WRITTEN: &[&str] = &["Attributes.lean"];

/// Chips whose committed file still predates this Pico, until their proofs move over. The list
/// only shrinks: `--check` fails once a listed file matches the extractor's output.
const PENDING: &str = include_str!("../pending.txt");

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (check, all, dir) = match args.as_slice() {
        [flag] if flag == "--list" => {
            for chip in RiscvChipType::<F>::all_chip_variants() {
                println!("{}", chip.name());
            }
            return;
        }
        [flag] if flag == "--lists" => {
            print_lists();
            return;
        }
        [flag, dir] if flag == "--compare" => {
            compare(&PathBuf::from(dir));
            return;
        }
        [flag, dir] if flag == "--check" => (true, false, PathBuf::from(dir)),
        [flag, dir] if flag == "--all" => (false, true, PathBuf::from(dir)),
        [dir] => (false, false, PathBuf::from(dir)),
        _ => panic!(
            "usage: pico-fv-extractor [--all] <out_dir> | --check <dir> | --list \
             | --compare <dir> | --lists"
        ),
    };

    let modules = extract_all();
    let pending: BTreeSet<&str> = PENDING
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    if !check {
        fs::create_dir_all(&dir).expect("create output dir");
        for (lean_name, content) in &modules {
            let file = format!("{lean_name}.lean");
            // A pending file's proofs still expect the old extraction; only --all overwrites it.
            if !all && pending.contains(file.as_str()) {
                eprintln!("skipped (pending): {file}");
                continue;
            }
            fs::write(dir.join(file), content).expect("write extraction");
        }
        return;
    }

    let mut problems = vec![];
    for (lean_name, content) in &modules {
        let path = dir.join(format!("{lean_name}.lean"));
        let is_pending = pending.contains(format!("{lean_name}.lean").as_str());
        match fs::read_to_string(&path) {
            Ok(committed) if committed == *content && is_pending => problems.push(format!(
                "up to date, remove it from extractor/pending.txt: {}",
                path.display()
            )),
            Ok(committed) if committed == *content || is_pending => {}
            Ok(_) => problems.push(format!("stale: {}", path.display())),
            Err(e) => problems.push(format!("unreadable: {} ({e})", path.display())),
        }
    }
    let generated: BTreeSet<String> = modules
        .iter()
        .map(|(name, _)| format!("{name}.lean"))
        .collect();
    for file in &pending {
        if !generated.contains(*file) {
            problems.push(format!(
                "extractor/pending.txt names an unknown file: {file}"
            ));
        }
    }
    for entry in fs::read_dir(&dir).expect("read extraction dir") {
        let file = entry
            .expect("read extraction dir")
            .file_name()
            .to_string_lossy()
            .into_owned();
        if file.ends_with(".lean")
            && !generated.contains(&file)
            && !HAND_WRITTEN.contains(&file.as_str())
        {
            problems.push(format!(
                "not generated by this extractor: {}",
                dir.join(file).display()
            ));
        }
    }
    if !problems.is_empty() {
        eprintln!("{} is out of date with pico {PICO_TAG} ({PICO_REV}):", dir.display());
        for problem in &problems {
            eprintln!("  {problem}");
        }
        std::process::exit(1);
    }
}

/// Prints one line per module: `same`, `differs`, `added` (no file in `dir`) or `removed` (a
/// file in `dir` this extractor does not produce), then the name. The first line of each file
/// names the Pico commit, so it is not compared. Fails when `dir` holds no extraction file.
fn compare(dir: &Path) {
    let modules = extract_all();
    let generated: BTreeSet<String> = modules
        .iter()
        .map(|(name, _)| format!("{name}.lean"))
        .collect();
    let mut compared = 0;
    for (lean_name, content) in &modules {
        let status = match fs::read_to_string(dir.join(format!("{lean_name}.lean"))) {
            Ok(theirs) => {
                compared += 1;
                if without_first_line(&theirs) == without_first_line(content) {
                    "same"
                } else {
                    "differs"
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => "added",
            Err(e) => panic!("read {lean_name}.lean in {}: {e}", dir.display()),
        };
        println!("{status} {lean_name}");
    }
    let mut theirs: Vec<String> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|entry| {
            entry
                .expect("read dir")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|f| f.ends_with(".lean") && !HAND_WRITTEN.contains(&f.as_str()))
        .collect();
    theirs.sort();
    for file in theirs.iter().filter(|f| !generated.contains(*f)) {
        println!("removed {}", file.trim_end_matches(".lean"));
    }
    if compared == 0 {
        eprintln!("no extraction file of this extractor in {}", dir.display());
        std::process::exit(1);
    }
}

fn without_first_line(text: &str) -> &str {
    text.split_once('\n').map_or("", |(_, rest)| rest)
}

/// Prints Pico's two RISC-V chip lists, `chiptype <name>` for `RiscvChipType::all_chip_variants`
/// and `air <name>` for the MLE machine's `mle_riscv_air_refs`, then `extracted <Lean name>
/// <chip name> <air name>` for each chip `extract_all` covers.
fn print_lists() {
    for chip in RiscvChipType::<F>::all_chip_variants() {
        println!("chiptype {}", chip.name());
    }
    // The program feeds only the preprocessed tables' traces, which are not built here.
    for air in mle_riscv_air_refs(Arc::new(Program::default()), false) {
        println!("air {}", air.name());
    }
    for (lean_name, chip_name, air_name) in extracted_chip_names() {
        println!("extracted {lean_name} {chip_name} {air_name}");
    }
}

/// `(Lean name, chip name, AIR name)` of each chip `extract_all` covers.
fn extracted_chip_names() -> Vec<(&'static str, String, String)> {
    fn names<A: ChipBehavior<F>>(
        lean_name: &'static str,
        chip: A,
    ) -> (&'static str, String, String) {
        (lean_name, chip.name(), get_air_name(&chip))
    }
    vec![
        names("AddChip", AddChip::<F>::default()),
        names("SubChip", SubChip::<F>::default()),
        names("AddwChip", AddwChip::<F>::default()),
        names("SubwChip", SubwChip::<F>::default()),
        names("BitwiseChip", BitwiseChip::<F>::default()),
        names("LtChip", LtChip::<F>::default()),
        names("SLLChip", SLLChip::<F>::default()),
        names("ShiftRightChip", ShiftRightChip::<F>::default()),
        names("MulChip", MulChip::<F>::default()),
        names("DivRemChip", DivRemChip::<F>::default()),
        names("CpuChip", CpuChip::<F>::default()),
        names("MemoryReadWriteChip", MemoryReadWriteChip::<F>::default()),
        names("MemoryUnalignedChip", MemoryUnalignedChip::<F>::default()),
    ]
}

/// Every `(Lean namespace, module text)` this extractor produces: one per RV64IM chip, then one
/// standalone wrapper per gadget. `extracted_chip_names` lists the same chips.
fn extract_all() -> Vec<(String, String)> {
    let mut modules = vec![
        extract("AddChip", &AddChip::<F>::default()),
        extract("SubChip", &SubChip::<F>::default()),
        extract("AddwChip", &AddwChip::<F>::default()),
        extract("SubwChip", &SubwChip::<F>::default()),
        extract("BitwiseChip", &BitwiseChip::<F>::default()),
        extract("LtChip", &LtChip::<F>::default()),
        extract("SLLChip", &SLLChip::<F>::default()),
        extract("ShiftRightChip", &ShiftRightChip::<F>::default()),
        extract("MulChip", &MulChip::<F>::default()),
        extract("DivRemChip", &DivRemChip::<F>::default()),
        extract("CpuChip", &CpuChip::<F>::default()),
        extract("MemoryReadWriteChip", &MemoryReadWriteChip::<F>::default()),
        extract("MemoryUnalignedChip", &MemoryUnalignedChip::<F>::default()),
    ];
    for gadget in gadgets::ALL {
        modules.push(extract(gadget.lean_name(), &gadget));
    }
    modules
}

/// Evaluates `air` symbolically as Pico's MLE keygen does (`get_symbolic_builder`, with the
/// public-value count the air declares) and renders it as the Lean module `<lean_name>.Extraction`.
fn extract<A>(lean_name: &str, air: &A) -> (String, String)
where
    A: BaseAir<F> + BaseAirWithPublicValues<F> + Air<SymbolicRapBuilder<F>>,
{
    // None of the extracted airs has a preprocessed trace.
    let width = TraceWidth {
        preprocessed: None,
        cached_mains: vec![],
        common_main: air.width(),
    };
    let builder = get_symbolic_builder(air, &width);
    // Copied out because `constraints()` consumes the builder.
    let (looking, looked) = builder.lookup_summaries();
    let (looking, looked) = (looking.to_vec(), looked.to_vec());
    let constraints = builder.constraints();
    let interaction_meta = pair_interaction_meta(&constraints, &looking, &looked);

    let extracted = ExtractedAir {
        name: lean_name.to_string(),
        constraints,
        interaction_meta,
    };
    let module = render_module(&extracted, PICO_REV);
    (extracted.name, module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use pico_mle_core::air::symbolic::{
        symbolic_expression::SymbolicExpression, symbolic_variable::Entry,
    };

    /// `Cargo.toml` pins the tag and `Cargo.lock` records the commit it resolved to, so the
    /// tag and commit printed in the documents are the ones the extractor builds against.
    #[test]
    fn pico_pin_matches_cargo() {
        let manifest = include_str!("../Cargo.toml");
        let pinned = format!("tag = \"{PICO_TAG}\"");
        for krate in ["pico-vm", "pico-mle-core"] {
            let line = manifest
                .lines()
                .find(|line| line.starts_with(&format!("{krate} =")))
                .unwrap_or_else(|| panic!("{krate} missing from Cargo.toml"));
            assert!(line.contains(&pinned), "{krate} is not pinned to PICO_TAG");
        }
        let lock = include_str!("../Cargo.lock");
        let sources: Vec<&str> = lock
            .lines()
            .filter(|line| line.starts_with("source = \"git+https://github.com/brevis-network/pico.git"))
            .collect();
        assert!(!sources.is_empty(), "no Pico crate in Cargo.lock");
        let resolved = format!("?tag={PICO_TAG}#{PICO_REV}\"");
        for source in sources {
            assert!(source.ends_with(&resolved), "{source} does not resolve PICO_TAG to PICO_REV");
        }
    }

    fn max_main_column(e: &SymbolicExpression<F>) -> Option<usize> {
        match e {
            SymbolicExpression::Variable(v) => match v.entry {
                Entry::Main { .. } => Some(v.index),
                _ => None,
            },
            SymbolicExpression::Add { x, y, .. }
            | SymbolicExpression::Sub { x, y, .. }
            | SymbolicExpression::Mul { x, y, .. } => max_main_column(x).max(max_main_column(y)),
            SymbolicExpression::Neg { x, .. } => max_main_column(x),
            _ => None,
        }
    }

    /// A wrapper wider than the columns its layout uses would add unconstrained columns.
    #[test]
    fn gadget_widths_match_their_layouts() {
        for gadget in gadgets::ALL {
            // The unsafe U16->U8 split emits nothing, so it has no columns to measure.
            if let gadgets::Gadget::U16ToU8Unsafe = gadget {
                continue;
            }
            let width = BaseAir::<F>::width(&gadget);
            let constraints = get_symbolic_builder(
                &gadget,
                &TraceWidth {
                    preprocessed: None,
                    cached_mains: vec![],
                    common_main: width,
                },
            )
            .constraints();
            let used = constraints
                .constraints
                .iter()
                .chain(
                    constraints
                        .interactions
                        .iter()
                        .flat_map(|i| i.message.iter().chain([&i.count])),
                )
                .filter_map(max_main_column)
                .max();
            assert_eq!(used, Some(width - 1), "{gadget:?}");
        }
    }
}
