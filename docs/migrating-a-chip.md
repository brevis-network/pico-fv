# Moving a chip to the pinned Pico

This is the procedure for moving one chip's proofs onto the Pico commit `extractor/` is pinned
to, worked through on `LtChip`. Each chip listed in `extractor/pending.txt` is moved in its own
pull request against `pico-v3`, touching only that chip's files and its entries in the shared
registers (see [CONTRIBUTING.md](../CONTRIBUTING.md)).

The files in `pending.txt` were extracted from a Pico development branch of the 2.x series
(the commit named in each file's first line), which carried fixes for the 13 gaps in
`Report.pdf`. Their proofs verify that branch, not a Pico release. Pico 3.x may implement a fix
differently or not at all, so a proof that breaks during the move needs a look at the gap the
chip used to have (see [`rv64-bug-mapping.md`](rv64-bug-mapping.md)) before it is repaired.

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
Diff the bus interactions too: a changed message changes the chip's bus row below. Read the chip's Rust source (`vm/src/chips/chips/...` at
the pinned commit) to learn what the change is for before touching the proofs.

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

A chip may now serve bus messages that the bus contract (`RVSail/Buses.lean`) does not specify
yet. `LtChip`'s merged branch-comparison rows serve ALU opcodes `264` / `265`, which are not in
`ALUBus.validOpcode`. Under the current contract such a row contradicts the ALU entry's external
assumption, so the proof splits on `is_cmp` and dismisses `is_cmp = 1` (`is_cmp_eq_zero`).
Changing the contract to specify the new opcodes is a framework change, made in its own pull
request; record this contract gap in the chip's issue and in `SOUNDNESS.md` (under A4).

## 5. Check the statements did not change

Add the chip's top-level theorems to `scripts/fv-check/theorems.d/<chip>.txt` (kebab-case, e.g.
`lt-chip.txt`) if they are not there. The top-level theorems are the ones the bus contract relies
on: each `spec_*` and the chip's `ext_asrt` and `wf_asrt`. Then, after `lake build PicoFV64`:

```bash
scripts/fv-check/check.sh            # the new theorems show up as additions only
```

If the chip's theorems are new to the list, compare their statements with the ones on `pico-v3`:
build `pico-v3` with the same `theorems.d/<chip>.txt` and run `check.sh` there, then diff the two
outputs. This costs a second full build. For `LtChip` the four theorems' statements and axioms were identical
before and after. Record them with `check.sh --update`.

## 6. Finish

```bash
scripts/fv-check/check_layers.sh
scripts/fv-check/check_tactics.sh
python3 scripts/fv-check/soundness_facts.py          # pending list and facts
(cd extractor && cargo run --release -- --check ../PicoFV/RV64IM/Extraction)
```

If the chip closes one of the gaps found in the 2.x development, fill in its row in
[`rv64-bug-mapping.md`](rv64-bug-mapping.md): the Pico constraint that closes it (file and line
at the pinned commit) and the extracted constraint and theorem that rely on it.
