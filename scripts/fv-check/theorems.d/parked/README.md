# Parked theorem lists

<!-- generated: parked -->
No list is parked here: all 62 instruction theorems of
`PicoFV/RV64IM/Equivalence/` are checked from `theorems.d/`.
<!-- end generated -->

The lists sat here, out of `theorems.d/` and so out of `check.sh`, while the CPU
chip moved to Pico v3.1.1: the chip's column layout changed shape (58 columns
instead of 132), so the 2.x `Equivalence/` files no longer compiled. Each
instruction class was rewritten against the v3.1.1 layout and its list moved
back up a directory; `PicoFV64.lean` imports `Equivalence.Equivalence`, which
pulls in all 13 class files. The tag `pico-v3-before-cpu` holds the 2.x
versions. This file stays as the record of how the restored statements differ
from those last checked, at commit `353238a`:

```bash
git show 353238a:scripts/fv-check/signatures.txt
git show 353238a:scripts/fv-check/axioms.txt
```

## How the restored statements differ

They differ from those at `353238a` in three ways, plus the dropped
hypotheses, the immediate of the register-immediate theorems and the operand
shapes of `LUI` and `AUIPC`, described after them. The bus assumptions name the
v3.1.1 contracts (`RV64IM_Interactions.V3` in `RVSail/BusesV3.lean`) instead of the
2.x ones. The register held in `op_a` (the destination, `rs1` for a branch,
or `rs2` for a store) is read from `instruction.op_a` instead of
`instruction.op_a_0`: v3.1.1 keeps the 5-bit index in one column, so every
theorem whose `rd`, branch `rs1` or store `rs2` reads it shows this rename; the
classes in decoded form (listed below) have since gone further and name no
column. And the whole-trace assumption `pico_CpuChip_control_flow_assumptions`
gains three conjuncts in its definition:

- the eight theorems that already named it (the six branches, `JAL` and `JALR`)
  keep that part of their recorded text, because `signatures.txt` records the
  name and not the definition, but their meaning changed. They changed for the
  other reasons in this section: at the restoration the six branches changed only
  in the contract names and in reading `rs1` from `op_a`; they have since moved to
  decoded form and dropped three bus assumptions, as the jumps have (below);
- the other 54 gain it as a new hypothesis, so their recorded statements
  changed.

Some restored statements also drop an immediate-flag hypothesis that the v3.1.1
decoder already fixes for its opcode (`imm_b_of_opcode`, `imm_c_of_opcode` in
`RVSail/BusesV3.lean`): `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`, `XORI`, `ORI`,
`ANDI`, `SLTI`, `SLTIU`, `SLLI`, `SRLI` and `SRAI` no longer take `imm_b = 0`,
and `SUBW` and `SUB` no longer take `imm_c = 0`. Dropping a hypothesis makes the
theorem stronger. `ADDI` kept `imm_b = 0` (its column form still does): the
decoder does not fix it for opcode 0, which `LUI` and `AUIPC` share. `ADD` does not take `imm_b = 0`,
although the decoder does not fix it for opcode 0: on a row with `imm_c = 0` the
flag is 0 whatever the opcode (`imm_b_eq_zero_of_imm_c_eq_zero`). Where an
immediate form and a register-register opcode share an opcode, the decoder does
not fix `imm_c`, so the immediate form keeps `imm_c = 1` and the
register-register one keeps `imm_c = 0` (for a class in decoded form, listed
below, only its unchecked column form `equivalence_<OP>_row` keeps it):
opcode 40 (`ADDIW`, `ADDW`), 42 to 44
(`SLLIW`, `SRLIW`, `SRAIW` and `SLLW`, `SRLW`, `SRAW`), 5 to 7 (`SLLI`, `SRLI`,
`SRAI` and `SLL`, `SRL`, `SRA`), and 0, 2 to 4, 8 and 9 (the six `ITYPE`
theorems and `ADD`, `XOR`, `OR`, `AND`, `SLT`, `SLTU`).

The statements of the classes in decoded form (listed below: the stores, the
loads, `RTYPE`, `RTYPEW`, `ITYPE`, `ADDIW`, `SHIFTIOP`, `SHIFTIWOP`, the
multiply and divide classes, the branches, the jumps and `UTYPE`) also drop, in both the checked and the column
form, the three bus assumptions their proofs do not use: `bus_row_axioms`,
`bus_row_ext_asm` and `bus_row_wf_asrt` (they keep `bus_row_wf_asm`). Of those
classes, `RTYPE`, `RTYPEW`, `ITYPE`, `ADDIW`, `SHIFTIOP`, `SHIFTIWOP`, the
multiply and divide classes (`MUL`, `MULW`, `DIV`, `DIVW`, `REM`, `REMW`) and
`UTYPE` (`LUI` and `AUIPC`) also drop `RISC_V_assumptions`, which their proofs
do not use; the stores, the loads, the branches and the jumps keep it. Dropping
a hypothesis makes the theorem stronger.

Some restored statements also drop the row's class selector, which the opcode
fixes: `JAL` and `JALR` no longer take `is_jal` / `is_jalr`, nor either
immediate flag, because opcodes 24 and 25 are the two jumps alone. The six
branches, the four stores and the seven loads never took theirs, for the same
reason, so their statements lose nothing here.

`LUI` and `AUIPC` are the one case where the v3.1.1 decoder gives two
instructions the same opcode and flags (opcode 0 with `imm_b = 1` and
`imm_c = 1`; there is no opcode 27 and no `is_auipc` column), so their
statements gain hypotheses instead: each takes its instruction's operand shape,
with the 20-bit immediate as a parameter instead of cut out of an operand
value. `LUI` takes `op_b` zero and `op_c` the immediate `signExtend 64 (imm ++
0#12)`; `AUIPC` takes `op_b` the immediate and `op_c` the row's pc, and is
keyed on opcode 0 instead of 27, without `is_auipc = 1`. The new
`Equivalence.utype_row_cases`, in the same list, proves that every real row of
opcode 0 with both flags has one of the two shapes. The checked `LUI` and
`AUIPC` have since moved to decoded form (below), where the decoding gives the
shape; the shape hypotheses stay on their column forms, `equivalence_LUI_row`
and `equivalence_AUIPC_row`.

A restored memory theorem also names what the Memory message promises it
(`MemoryBus.Spec` in `RVSail/BusesV3.lean`) only through the bus assumptions,
as the ALU classes name `ALUBus.Spec`. The promise's serving side is proven only
for the dispatches the read/write memory chip takes, not for those the unaligned
chip takes: `SOUNDNESS.md` A3 says so for the stores and the loads, and a pull
request that changes what a memory theorem assumes should keep those two
paragraphs true.

The column forms of the register-immediate theorems (`equivalence_<OP>_row`)
read their immediate from the row's encoded `instruction.op_c_0` instead of the
`op_c` value the row sends to the ALU chip (`op_c_value`), as they read `rd` and
`rs1`: the shifts `SLLIW`, `SRLIW`, `SRAIW`, `SLLI`, `SRLI` and `SRAI`, and
`ADDI`, `XORI`, `ORI`, `ANDI`, `SLTI`, `SLTIU` and `ADDIW`. The statement at
`353238a` read it from the value the ALU chip works on, so it held whatever tied
that value to the instruction. The column form names the low 6 bits (5 for the
32-bit shifts) of the row's encoded `op_c_0`, that is `op_c_0` modulo 64 (or 32), or its low
12 bits for the other seven, and the proof needs the constraint that ties the
two (`op_c_value_setWidth_eq_op_c_0`). The decoder sign-extends the program's
12-bit immediates and zero-extends its shift amounts
(`Transpiler.V3.imm_operand` with its sign flag `true` or `false`), and writes
the low 16 bits of the result into `op_c_0`, so on a row the program decoded
those bits are the program's immediate, but the column form does not tie
`op_c_0` to the decoder. The classes in decoded form do, and tie their
register columns to it in the same way: each theorem takes the instruction and
the hypothesis `h_decode` that the decoder (`Transpiler.V3.transpile_op`, at
multiplicity 1) turns it into the row's Program message, in place of
`is_real = 1`, the opcode and the immediate flags it took (for `LUI` and
`AUIPC`, also the operand shape), and the class's lemma derives that hypothesis
from those and the row's Program promise:

- the four stores: `Equivalence.store_decode_satisfiable`;
- the seven loads: `Equivalence.load_decode_satisfiable`;
- the ten `RTYPE` theorems (no immediate):
  `Equivalence.rtype_decode_satisfiable`;
- the five `RTYPEW` theorems (no immediate):
  `Equivalence.rtypew_decode_satisfiable`;
- the six `ITYPE` theorems: `Equivalence.itype_decode_satisfiable`;
- `ADDIW`: `Equivalence.addiw_decode_satisfiable`;
- the three `SHIFTIOP` theorems: `Equivalence.shiftiop_decode_satisfiable`;
- the three `SHIFTIWOP` theorems: `Equivalence.shiftiwop_decode_satisfiable`;
- the five multiply theorems (no immediate):
  `Equivalence.mul_decode_satisfiable` and `Equivalence.mulw_decode_satisfiable`;
- the eight divide and remainder theorems (no immediate):
  `Equivalence.div_decode_satisfiable`, `Equivalence.divw_decode_satisfiable`,
  `Equivalence.rem_decode_satisfiable` and `Equivalence.remw_decode_satisfiable`;
- the six branches: `Equivalence.btype_decode_satisfiable`;
- `JAL` and `JALR`: `Equivalence.jal_decode_satisfiable` and
  `Equivalence.jalr_decode_satisfiable`;
- `LUI` and `AUIPC`: `Equivalence.utype_decode_satisfiable`, from opcode 0 with
  `imm_b = 1`, for one of the two (the row does not say which).

Two definitions every statement names were also rewritten at v3.1.1, and
`signatures.txt` shows only their names: `Equivalence.CPU_bus_operations` (the
operations the row's messages stand for, now with a two-piece pc and the
memory width and direction taken from the opcode) and
`CpuChip.Interpretations.bus_row` (which sorts the row's messages with the
v3.1.1 deserialiser). Their meaning changed for every restored theorem at once.

Any other difference in a statement, and any new name in `axioms.txt`, is a
change in what the theorem assumes and must be listed in the pull request. See
`docs/cpu-chip-pico-v3-design.md`, "The whole-trace assumption".
