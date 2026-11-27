# Moving a chip to the pinned Pico

This is the procedure for moving one chip's proofs onto the Pico commit `extractor/` is pinned
to, worked through on `LtChip`. It applies to a chip listed in `extractor/pending.txt`: the
extractor leaves a listed chip's file alone, since its proofs still expect the old extraction.
Every chip has moved, so the list is empty. Pull requests target `main`. Moving a chip touches
only that chip's files and its entries in the shared registers (see
[CONTRIBUTING.md](../CONTRIBUTING.md)).

A proof that breaks during the move may mean that the new Pico closes one of the recorded
soundness gaps differently or not at all: check the chip's rows in
[`rv64-bug-mapping.md`](rv64-bug-mapping.md) before repairing it.

## 1. Regenerate the extraction and see what changed

```bash
cd extractor
cargo run --release -- --all /tmp/extract    # every file at the pinned commit, pending ones too
diff ../PicoFV/RV64IM/Extraction/LtChip.lean /tmp/extract/LtChip.lean
```

When constraints are inserted, a plain diff is mostly renumbering. Diffing the bodies alone helps:
`grep -A1 'def constraint_' FILE | grep -v 'def constraint_'` for each file, then `diff` the two.

Compare the constraints, not only the line count. For `LtChip` the diff showed one new column
(`is_cmp`), two new constraints inserted after the third (its booleanity and its zero on padding
rows), the old `a_1 = 0` replaced by `a_1 = is_cmp * (Σ u16_flags - bit)`, and `is_cmp * 256`
added to the opcode of the ALU-bus message. Every other constraint only moved by two places.
Diff the bus interactions too: a changed message changes the chip's bus row below. Read the
chip's Rust source (`vm/src/chips/chips/...` at the pinned commit) to learn what the change is
for before touching the proofs.

Then remove the chip from `extractor/pending.txt` and regenerate in place
(`cargo run --release -- ../PicoFV/RV64IM/Extraction`); regenerating leaves the other pending
chips' files alone.

## 2. Airs: the column layout

`Airs/<Chip>.lean` mirrors the Rust column struct. Add, remove or reorder columns to match it,
and update the widths in the `#define_subair` / `#define_air` declarations and the doc comment.
The width must equal the highest column index in the extraction plus one.

## 3. Constraints: the readable restatement

`Constraints/<Chip>.lean` restates each extracted constraint over named columns
(`constraint_N`), proves it equal to the extraction (`constraint_N_equiv`), restates the bus row
(`raw_bus_row` and the typed `AbsBuses`), and decomposes the constraints into gadget and chip
parts (`allHold_abs`).

- If constraints were inserted, renumber the later ones. Rename `constraint_N_equiv` together
  with `constraint_N`: a word-boundary search for `constraint_3` does not match
  `constraint_3_equiv`.
- Restate new or changed constraints from the extraction, not from the Rust source, so that each
  `_equiv` lemma stays a `simp` proof.
- Update `raw_bus_row` and `AbsBuses` when a bus message changes (`LtChip`'s ALU opcode gained
  `is_cmp * 256`), and thread any new column through `bus_row` and `bus_row_abs`.
- Keep the comments' constraint numbers, tags and signs in step with the code.

## 4. Spec: the proofs

Rebuild and repair `Spec/<Chip>.lean`. Repairs should not change a theorem's statement; if a
proof needs a new or stronger hypothesis, or a constraint looks too weak, stop and report it.
It may be a soundness gap in Pico.

A chip may serve a bus message that the bus contract (`RVSail/Buses.lean`) has to specify.
`LtChip`'s merged branch-comparison rows (`is_cmp = 1`) serve ALU opcodes `264` / `265`, which
`ALUBus.validOpcode` lists and `ALUBus.Spec` states piece by piece (the two comparison bits). The
spec proves one theorem per row shape: `spec_SLT` and `spec_SLTU` take `is_cmp = 0`,
`spec_CMP_SLT` and `spec_CMP_SLTU` take `is_cmp = 1`, and `wf_asrt` splits on `is_cmp`. A message
the contract does not specify yet needs a framework change, reviewed as one (see
[CONTRIBUTING.md](../CONTRIBUTING.md)).

## 5. Check the statements did not change

Add the chip's top-level theorems to `scripts/fv-check/theorems.d/<chip>.txt` (kebab-case, e.g.
`lt-chip.txt`) if they are not there. The top-level theorems are the ones the bus contract relies
on: each `spec` / `spec_*` and the chip's `ext_asrt` and `wf_asrt`. Then, after `lake build PicoFV64`:

```bash
scripts/fv-check/check.sh            # the new theorems show up as additions only
```

The definitions those theorems reach are fingerprinted in `scripts/fv-check/definitions.txt`, so
`check.sh` also prints `DEFINITION DRIFT`, `NEW` or `GONE` lines: the regenerated
`<Chip>.Extraction.*` definitions, the chip's new definitions, and every definition above a changed
one. Review that each named definition is one the move meant to change.

If the chip's theorems are new to the list, compare their statements with the ones on `main`:
build `main` with the same `theorems.d/<chip>.txt` and run `check.sh` there, then diff the two
outputs. This costs a second full build. Record the theorems, and the definitions, with
`check.sh --update`.

## 6. Finish

```bash
scripts/fv-check/check_layers.sh
scripts/fv-check/check_tactics.sh
python3 scripts/fv-check/soundness_facts.py          # pending list and facts
(cd extractor && cargo run --release -- --check ../PicoFV/RV64IM/Extraction)
```

If the chip closes one of the gaps in [`rv64-bug-mapping.md`](rv64-bug-mapping.md), bring its
row up to date: the Pico constraint that closes it (file and line at the pinned commit) and the
extracted constraint and theorem that rely on it.
