# Parked theorem lists

The 11 lists here name 56 of the 62 instruction theorems of
`PicoFV/RV64IM/Equivalence/`. They sit out of `theorems.d/` — and so out of
`check.sh` — while the CPU chip moves to Pico v3.1.1.

The chip's column layout changed shape (58 columns instead of 132), so the 2.x
`Constraints/CpuChipInterpretations.lean` and the `Equivalence/` files that
rest on it no longer compile. The interpretations file and
`Equivalence/Common.lean` are now rewritten at v3.1.1, holding the lemmas every
instruction class shares, and `equivalence-addiw.txt` and
`equivalence-r-type-w.txt` have moved back up a directory with
`Equivalence/Addiw.lean` and `Equivalence/RTypeW.lean`. `PicoFV64.lean` still
does not import `Equivalence.Equivalence`, which pulls in all 13 class files;
it returns with the last of them. The tag `pico-v3-before-cpu` holds the 2.x versions.

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

They are expected to differ from those at `353238a` in three ways, plus the
dropped hypotheses described at the end of this section. The bus
assumptions name the v3.1.1 contracts (`RV64IM_Interactions.V3` in
`RVSail/BusesV3.lean`) instead of the 2.x ones. The destination register is
read from `instruction.op_a` instead of `instruction.op_a_0`: v3.1.1 keeps the
5-bit index in one column, so every theorem whose `rd` reads it shows this
rename. And the whole-trace assumption `pico_CpuChip_control_flow_assumptions`
gains three conjuncts in its definition:

- the eight theorems that already name it (the six branches, `JAL` and `JALR`)
  keep their recorded text, because `signatures.txt` records the name and not
  the definition, but their meaning changes;
- the other 54 gain it as a new hypothesis, so their recorded statements change,
  as those of the six already restored have.

A restored statement may also drop an immediate-flag hypothesis that the v3.1.1
decoder already fixes for its opcode (`imm_b_of_opcode`, `imm_c_of_opcode` in
`RVSail/BusesV3.lean`): `ADDIW` no longer takes `imm_b = 0`, and `SUBW` no
longer takes `imm_c = 0`. Dropping a hypothesis makes the theorem stronger.

Two definitions every statement names were also rewritten at v3.1.1, and
`signatures.txt` shows only their names: `Equivalence.CPU_bus_operations` (the
operations the row's messages stand for, now with a two-piece pc and the
memory width and direction taken from the opcode) and
`CpuChip.Interpretations.bus_row` (which sorts the row's messages with the
v3.1.1 deserialiser). Their meaning changed for every restored theorem at once.

Any other difference in a statement, and any new name in `axioms.txt`, is a
change in what the theorem assumes and must be listed in the pull request. See
`docs/cpu-chip-pico-v3-design.md`, "The whole-trace assumption".
