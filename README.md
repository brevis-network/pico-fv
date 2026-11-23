# Formal verification of the Brevis Pico RISC-V zkVM

This repository contains a Lean 4 (v4.28.0-rc1) formalisation of the Brevis Pico
RISC-V zkVM and equivalence proofs between the constraint systems of Pico's RV64IM
CPU, ALU and memory chips (and their gadgets) and the Lean translation
([`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean/tree/bb1e7d45c6a158a5598705eea12cebfee4349b03))
of the official Sail RISC-V model.

The development covers the **RV64IM** variant of Pico. Its 62 opcodes were
equivalence-proven against Pico 2.x. Those proofs have been rewritten, one
instruction class at a time, for Pico 3.x, and are stated against the CPU chip at
Pico v3.2.0, the version `extractor/` pins.

<!-- generated: restored -->
The repository proves all 62 of them against the v3.2.0 chip: `ADD`, `ADDI`,
`ADDIW`, `ADDW`, `AND`, `ANDI`, `AUIPC`, `BEQ`, `BGE`, `BGEU`, `BLT`, `BLTU`,
`BNE`, `DIV`, `DIVU`, `DIVUW`, `DIVW`, `JAL`, `JALR`, `LB`, `LBU`, `LD`, `LH`,
`LHU`, `LUI`, `LW`, `LWU`, `MUL`, `MULH`, `MULHSU`, `MULHU`, `MULW`, `OR`,
`ORI`, `REM`, `REMU`, `REMUW`, `REMW`, `SB`, `SD`, `SH`, `SLL`, `SLLI`, `SLLIW`,
`SLLW`, `SLT`, `SLTI`, `SLTIU`, `SLTU`, `SRA`, `SRAI`, `SRAIW`, `SRAW`, `SRL`,
`SRLI`, `SRLIW`, `SRLW`, `SUB`, `SUBW`, `SW`, `XOR` and `XORI` (see
[SOUNDNESS.md](SOUNDNESS.md)).
<!-- end generated -->

The 62 opcodes:
  - 27 ALU opcodes: `ADD`, `ADDI`, `SUB`, `XOR`, `XORI`, `OR`, `ORI`, `AND`,
    `ANDI`, `SLT`, `SLTI`, `SLTU`, `SLTIU`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`,
    `SRAI`, `MUL`, `MULH`, `MULHU`, `MULHSU`, `DIV`, `DIVU`, `REM`, `REMU`;
  - 10 control-flow opcodes: `AUIPC`, `LUI`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`,
    `BGEU`, `JAL`, `JALR`;
  - 11 memory opcodes: `LW`, `LH`, `LHU`, `LB`, `LBU`, `SW`, `SH`, `SB`, and
    the RV64 additions `LWU`, `LD`, `SD` (`LW` sign-extends per the RV64 spec);
  - 5 word-variant ALU opcodes: `ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`;
  - 4 word-variant immediate opcodes: `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`;
  - 5 word-variant MUL/DIV opcodes: `MULW`, `DIVW`, `DIVUW`, `REMW`, `REMUW`.

`ECALL` is intentionally out of scope. So are the following, by decision of 2026-11-23:
composing the chips into the execution of a whole chunk (that every bus balances across the
chips, so that each chip's assumptions are met by the others' proven promises), the precompile
chips (including the two Blake2b chips v3.2.0 adds), the recursion layers, and completeness. The
theorems go in one direction only: under their hypotheses, rows that satisfy the constraints
behave as the Sail specification says; they do not say that every correct execution has such
rows. [SOUNDNESS.md](SOUNDNESS.md) lists what is not covered (A4, A5).

The extraction tool in `extractor/` is pinned to this Pico revision:

<!-- generated: pin -->
Pico v3.2.0, commit [`fcfa50462`](https://github.com/brevis-network/pico/commit/fcfa504624657d0c417c43f1233d5d891f293ff9).
<!-- end generated -->

Each proof is about the Pico revision named in the first line of the `PicoFV/RV64IM/Extraction/`
file it uses; every file is extracted from the pinned commit (`extractor/pending.txt`, the list of
files that predate it, is empty). Re-extracting the CPU chip, the ten ALU chips and their gadgets at
v3.1.6 gives the same constraints and bus messages as at v3.1.1, so what this README says about
those chips at v3.1.1 holds at v3.1.6. Re-extracting every file at v3.2.0 gives the same
constraints and bus messages as at v3.1.6: v3.2.0 changed nothing an RV64IM chip constrains. This
was checked at v3.2.0; if the pin above names a later version, it has not been checked there yet.
The read/write memory chip changed after v3.1.1, and since v3.1.2 Pico has a second memory chip for
misaligned loads and stores; both are proven at v3.2.0 (see [SOUNDNESS.md](SOUNDNESS.md), A4).
[SOUNDNESS.md](SOUNDNESS.md) says what the proofs establish and what they trust.

For each opcode, the equivalence theorem states: under the chip's row
constraints, bus assumptions, and program well-formedness, executing one Sail
step of the corresponding instruction produces the same post-state as
applying the chip's emitted CPU-bus operations.

In the course of this development, 13 chip-side soundness gaps were found in
the Pico implementation, across `LtChip`, `ShiftRightChip`, `SLLChip`,
`JalrChip`, `DivRemChip`, and `MemoryReadWriteChip` (see `Report.pdf`). Which
Pico 3.x constraint closes each of them is recorded for every one of them at the
pinned commit.

### RV32IM (historical)

An RV32IM development of all 45 RV32IM base opcodes used to live alongside
RV64IM. It matches Pico v1.x only and is no longer maintained here; it is
preserved upstream at
[NethermindEth/pico-fv@a7f9a09](https://github.com/NethermindEth/pico-fv/tree/a7f9a0976e245aeef89c3f02c51ae85023207b53).

## Repository structure

```
PicoFV/
├── Fundamentals/        — shared infrastructure
│   ├── Core.lean        — lemmas about lists, bit-vectors, integers, hash maps
│   ├── Interaction.lean — generic bus interactions (typeclass-driven)
│   ├── KoalaBear.lean   — the KoalaBear finite field (FKB = Fin 2 130 706 433)
│   └── Word.lean        — u32/u64 byte- and limb-level representations
└── RV64IM/              — RV64IM development
    ├── Airs/            — chip column / row layouts
    ├── Constraints/     — extracted constraint definitions per chip
    ├── Extraction/      — auto-extracted chip data from Pico
    ├── RVSail/          — Sail-side glue + per-opcode pure / effectful specs
    ├── Spec/            — hand-written chip specifications & bus equivalences
    ├── Transpiler/      — instruction → chip-row encoding
    └── Equivalence/     — per-opcode equivalence theorems, one file per instruction class
Extensions/              — reserved for syscalls and precompiles (empty)
extractor/               — regenerates RV64IM/Extraction/ from Pico's source
scripts/fv-check/        — theorem, layer, tactic and SOUNDNESS checks
```

Within `RV64IM/Spec/` (and `Constraints/`), each chip used by Pico
has its own file: ALU chips (`AddChip`, `SubChip`, `BitwiseChip`, `LtChip`,
`SLLChip`, `ShiftRightChip`, `MulChip`, `DivRemChip`), the CPU chip
(`CpuChip`), the memory chips (`MemoryReadWriteChip`,
`MemoryUnalignedChip`), and any chip-local gadgets (`AddGadget`, `SubGadget`, `MulGadget`,
`IsZeroGadget`, `LtSignedGadget`, …).

Within `RV64IM/RVSail/Opcodes/`, every opcode has its own file
containing the pure functional spec and the effectful Sail spec, along
with the bridge lemmas between them.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md) (and [AGENTS.md](AGENTS.md) for AI agents) first. Each
chip's files are independent of the other chips', so chips can be moved or extended in parallel.

## Building the repository

Assuming Lean's `lake` package manager is installed:

```
lake exe cache get!
lake build
```

The first command is optional but speeds up the initial build by fetching
mathlib's binary cache.

## Reproducing

The proofs are built from these pinned inputs:

| Input | Pin | Read from |
|---|---|---|
| Pico | v3.2.0, commit `fcfa504624657d0c417c43f1233d5d891f293ff9` | `extractor/Cargo.toml`, `extractor/Cargo.lock` |
| Lean toolchain | `leanprover/lean4:v4.28.0-rc1` | `lean-toolchain` |
| RISC-V specification (Lean) | `sail-riscv-lean` `bb1e7d45c6a158a5598705eea12cebfee4349b03`, on `lean-sail` `535c13d3026c404e283c2e1b7f46c85237382223` | `lake-manifest.json` |
| `riscv/sail-riscv` commit it was generated from | not recorded; its content points to `5f5f02d3`, unconfirmed | [SOUNDNESS.md](SOUNDNESS.md#pinned-inputs) |
| RISC-V unprivileged ISA version | no dated release named; RV64I v2.1, M v2.0 (sail-riscv's `README.md` at `5f5f02d3`) | [SOUNDNESS.md](SOUNDNESS.md#pinned-inputs) |
| Circuit framework | `LeanZKCircuit-Plonky3` `d1f15357a7a999618b80dd110aba955c1f111cf6` (branch `Dom/v4.28.0-rc1`) | `lake-manifest.json` |
| Mathlib | `5352afccd6866369be9de43f5b7ec47203555f44` (tag `v4.28.0-rc1`) | `lake-manifest.json` |
| Extractor's Rust toolchain | `nightly-2026-09-27` | `extractor/rust-toolchain.toml` |

Build from the committed `lake-manifest.json`. `lakefile.toml` names two dependencies by branch
(`sail-riscv-lean`'s `v4.28.0-rc1`, `LeanZKCircuit-Plonky3`'s `Dom/v4.28.0-rc1`), so
`lake update` can move their pins. CI (`.github/workflows/ci.yml`) runs on every pull request
and every push to `main`: its `extractor` job regenerates every generated file in
`PicoFV/RV64IM/Extraction/` from the pinned Pico and fails if one differs from the committed
file, and its `build` job rebuilds the proofs and runs `scripts/fv-check/check.sh`.

## Checking the theorems

After `lake build`, `scripts/fv-check/check.sh` checks the top-level theorems
listed in `scripts/fv-check/theorems.d/`: the two memory chips' specifications at v3.2.0,
and the specifications of the ALU chips already at v3.1.1
(Add, Sub, Addw, Subw, Bitwise, Mul, Lt, DivRem, SLL, ShiftRight), and the
equivalence theorems the branch proves at v3.1.1 (listed above), with
`Equivalence.utype_row_cases`, which shows that the unchecked column forms of the
`LUI` and `AUIPC` theorems (`equivalence_LUI_row`, `equivalence_AUIPC_row`) together
cover the row shape the two instructions share; no checked theorem takes their
shape hypotheses. The theorems of the classes below take the instruction whose
decoding is the row's Program message, and a lemma checked with each class shows
that every real row of the class, given its Program promise, has one:

- the stores: `Equivalence.store_decode_satisfiable`;
- the loads: `Equivalence.load_decode_satisfiable`;
- `RTYPE`: `Equivalence.rtype_decode_satisfiable`, with `imm_c = 0` where an
  immediate form shares the opcode;
- `RTYPEW`: `Equivalence.rtypew_decode_satisfiable`, with `imm_c = 0` where an
  immediate form shares the opcode;
- `ITYPE`: `Equivalence.itype_decode_satisfiable`, with `imm_c = 1`, and
  `imm_b = 0` for `ADDI`;
- `ADDIW`: `Equivalence.addiw_decode_satisfiable`, with `imm_c = 1`;
- `SHIFTIOP`: `Equivalence.shiftiop_decode_satisfiable`, with `imm_c = 1`;
- `SHIFTIWOP`: `Equivalence.shiftiwop_decode_satisfiable`, with `imm_c = 1`;
- the multiplies: `Equivalence.mul_decode_satisfiable` (for opcode 30, `MUL`, at
  every signedness with `result_part := .Low`) and
  `Equivalence.mulw_decode_satisfiable`;
- the divides and remainders: `Equivalence.div_decode_satisfiable`,
  `Equivalence.divw_decode_satisfiable`, `Equivalence.rem_decode_satisfiable` and
  `Equivalence.remw_decode_satisfiable`;
- the branches: `Equivalence.btype_decode_satisfiable`;
- `JAL` and `JALR`: `Equivalence.jal_decode_satisfiable` and
  `Equivalence.jalr_decode_satisfiable`;
- `LUI` and `AUIPC`: `Equivalence.utype_decode_satisfiable`, with `imm_b = 1` (an
  `ADD` or `ADDI` row has no U-type decoding).

`check.sh` fails if a theorem is missing, depends on an axiom (a statement Lean
accepts without proof) outside two lists, or its axioms or statement differ from
the snapshots in `axioms.txt` and `signatures.txt`:

- Lean's core axioms: `propext`, `Classical.choice`, `Quot.sound`, and
  `Lean.ofReduceBool` / `Lean.trustCompiler`, which `native_decide` and
  `bv_decide` rely on (they trust Lean's compiler to evaluate decidable
  propositions);
- `spec-axioms.txt`: functions the Lean RISC-V specification declares as
  axioms (floating point, random bits, reservations, platform output). The
  equivalence theorems hold for any interpretation of them.

So a `sorry`, or an `axiom` declared in this repository, fails the check. A change to a theorem's
statement shows up as a diff of `signatures.txt` for review; once reviewed,
`check.sh --update` records it.

More checks run in CI: `check_layers.sh` (no chip imports another chip),
`check_tactics.sh` (uses of `native_decide` / `bv_decide` / `decide +native` only go down),
`soundness_facts.py --check` (the generated facts in `SOUNDNESS.md`, in this README and in the
parked lists' README are current), and
`extractor --check` (the extraction files match the pinned Pico).

## Soundness audit

The 13 RV64IM soundness gaps found during the formalisation are described in
`Report.pdf` and, for the memory chip, in
[`RV64_MemoryReadWriteChip_soundness_gaps.md`](https://github.com/brevis-network/pico-fv/blob/c8b945581cb4218f0bd72baa81ce7a100e67f33d/RV64_MemoryReadWriteChip_soundness_gaps.md)
(removed from the tree once its three gaps were filled in the mapping below).
[`docs/rv64-bug-mapping.md`](docs/rv64-bug-mapping.md) records the Pico 3.x constraint that closes
each of them at the pinned commit.
