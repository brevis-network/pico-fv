# Parked theorem lists

The 12 lists here name 61 of the 62 instruction theorems of
`PicoFV/RV64IM/Equivalence/`. They sit out of `theorems.d/` — and so out of
`check.sh` — while the CPU chip moves to Pico v3.1.1.

The chip's column layout changed shape (58 columns instead of 132), so the 2.x
`Constraints/CpuChipInterpretations.lean` and the `Equivalence/` files that
rest on it no longer compile. The interpretations file and
`Equivalence/Common.lean` are now rewritten at v3.1.1, holding the lemmas every
instruction class shares, and `equivalence-addiw.txt` has moved back up a
directory with `Equivalence/Addiw.lean`. `PicoFV64.lean` still does not import
`Equivalence.Equivalence`, which pulls in all 13 class files; it returns with
the last of them. The tag `pico-v3-before-cpu` holds the 2.x versions.

## Restoring an instruction class

The files are rewritten against the v3.1.1 layout one instruction class at a
time. For each class:

1. Rewrite its `Equivalence/` file, and the rewritten interpretations file and
   `Equivalence/Common.lean` it needs.
2. Make `PicoFV64.lean` import the rewritten modules again. `check.sh` reads
   the theorems through `Report.lean`, which imports only `PicoFV64`, so a
   theorem whose module is not imported there is reported missing.
3. Move the class's list back up a directory and run `check.sh --update` to
   record its theorems.
4. Compare the new lines of `signatures.txt` and `axioms.txt` with the ones
   last checked, at commit `353238a`:

   ```bash
   git show 353238a:scripts/fv-check/signatures.txt
   git show 353238a:scripts/fv-check/axioms.txt
   ```

## How the restored statements may differ

They are expected to differ from those at `353238a` in two ways. The bus
assumptions name the v3.1.1 contracts (`RV64IM_Interactions.V3` in
`RVSail/BusesV3.lean`) instead of the 2.x ones. And the whole-trace assumption
`pico_CpuChip_control_flow_assumptions` gains three conjuncts in its
definition:

- the eight theorems that already name it (the six branches, `JAL` and `JALR`)
  keep their recorded text, because `signatures.txt` records the name and not
  the definition, but their meaning changes;
- the other 54 gain it as a new hypothesis, so their recorded statements change,
  as `ADDIW`'s already has.

Any other difference in a statement, and any new name in `axioms.txt`, is a
change in what the theorem assumes and must be listed in the pull request. See
`docs/cpu-chip-pico-v3-design.md`, "The whole-trace assumption".
