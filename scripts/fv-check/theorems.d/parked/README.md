# Parked theorem lists

The 13 lists here name the 62 instruction theorems of
`PicoFV/RV64IM/Equivalence/`. They sit out of `theorems.d/` — and so out of
`check.sh` — while the CPU chip moves to Pico v3.1.1.

The chip's column layout changed shape (58 columns instead of 132), so the 2.x
`Constraints/CpuChipInterpretations.lean` and the 13 `Equivalence/` files that
rest on it no longer compile. They are rewritten against the v3.1.1 layout one
instruction class at a time; each list moves back up a directory with the file
it names, and `check.sh --update` records its theorems again.

The statements to restore them to are the ones recorded at the tag
`pico-v3-before-cpu` (`35259d8`), the last commit before the CPU work:

```bash
git show pico-v3-before-cpu:scripts/fv-check/signatures.txt
git show pico-v3-before-cpu:scripts/fv-check/axioms.txt
```

Eight of the 62 — the six branches, `JAL` and `JALR` — already name
`pico_CpuChip_control_flow_assumptions`, whose definition gains three
conjuncts in the move. Their recorded statements do not change, because
`signatures.txt` records the name and not the definition; the other 54 gain the
assumption as a new hypothesis and their recorded statements do change. See
`docs/cpu-chip-pico-v3-design.md`, "The whole-trace assumption".
