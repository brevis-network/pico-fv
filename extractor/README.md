# extractor

Generates `PicoFV/RV64IM/Extraction/*.lean` from Pico's Rust source. It runs each RV64IM chip's
`eval` through Pico's own symbolic builder, the way Pico's MLE keygen does, along with
standalone wrappers for the gadgets the chips call, and prints the resulting constraints and
bus interactions in the `LeanZKCircuit_Plonky3` format.

The Pico commit is pinned in `Cargo.toml` (and `PICO_REV` in `src/main.rs`, which a test keeps
in step). Each generated file records that commit in its first line. The Lean build does not
need Rust: the generated files are committed.

## Run

```bash
cd extractor
cargo run --release -- ../PicoFV/RV64IM/Extraction           # regenerate (skips pending files)
cargo run --release -- --all /tmp/extract                    # every file, into a scratch dir
cargo run --release -- --check ../PicoFV/RV64IM/Extraction   # fail unless up to date
cargo run --release -- --list                                # list Pico's RISC-V chips
```

The toolchain is pinned in `rust-toolchain.toml`, matching Pico's. The first build fetches Pico
and Plonky3 from GitHub at the pinned revisions and compiles them, which takes a while.

`--check` also fails on a `.lean` file in that directory that the extractor does not produce
(other than the hand-written `Attributes.lean`).

The committed extraction files are moved onto this extractor chip by chip, together with the
Lean proofs that consume them. `pending.txt` lists the files not moved yet. Regenerating leaves
them alone (their proofs still expect the old file; `--all` writes them anyway), and `--check`
skips them but fails once one matches the extractor's output, so the list only shrinks.

## Upgrading Pico

1. Change the `rev` of `pico-vm` / `pico-mle-core` in `Cargo.toml` and `PICO_REV` in
   `src/main.rs`.
2. Regenerate and look at `git diff PicoFV/RV64IM/Extraction`. Files whose constraints did not
   change differ only in their first line. The others show which chips need their Lean proofs
   revisited.

## Output conventions

- A bus interaction is `(multiplicity, [tag, message...])`. `tag` is the Pico `LookupType`
  discriminant, the value Pico's LogUp absorbs into the fingerprint (as `tag + 1`). The
  multiplicity is `+m` for a lookup the chip makes (`looking`) and `-m` for one it serves
  (`looked`), exactly as Pico's symbolic builder records them. A comment above each entry names
  its direction, bus and scope.
- Expressions are fully parenthesised, and constants are printed as canonical KoalaBear values.

## Provenance

The renderer is adapted from an AIR-to-Lean constraint extractor by Nethermind
(MIT/Apache-2.0), adapted to Pico by Brevis.
