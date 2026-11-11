# Moving the CPU chip to Pico v3.1.1: design

Draft for review. Pico at the commit `extractor/` is pinned to (`2acc7c1828fb`, v3.1.1);
pico-fv branch `pico-v3-cpu` at `f16f474`. Pico paths below are under `vm/src/chips/chips/`
unless they say otherwise.

## What changed and why it is a redesign

The v3.1.1 CPU chip has 65 constraints instead of 218, 58 columns instead of 132 and 17 messages
per row instead of 36. It checks less itself. The 2.x proofs took the pc's 16-bit range, the
next pc's range and the branch and jump arithmetic from range checks and ALU messages inside the
chip; v3.1.1 takes them from the Program table (the pc), from the next row (the next pc) or from
the public values (the last row's next pc), and proves the jump additions in place. Three
message formats changed: the instruction fetch (43 → 26 fields), the memory dispatch (25 → 17)
and a new Ecall message (tag 13, 20 fields). So the CPU chip's Lean files are rewritten, not
renumbered, and the bus contracts the chip relies on are restated.

## The draft contracts

Branch `tommy/cpu-3x-contracts`, two new files beside the old ones:

- `PicoFV/RV64IM/Transpiler/TranspilerV3.lean`: the decoder. `transpile_op inst mult pc` maps a
  Sail instruction at address `pc` to the 26-field Program message, following
  `compiler/riscv/disassembler/rrs.rs` and `riscv_program/traces.rs`: the pc in two 16-bit
  pieces; register `a` as one field; `b` and `c` as two 16-bit pieces plus a sign bit
  (`SignExtImm`, `riscv_cpu/instruction/columns.rs:43-70`); 13 selectors; `op_a_0` is
  `[op_a = x0]` for every instruction, stores and branches included
  (`instruction/columns.rs:92`); `AUIPC rd, imm` is `ADD rd, imm, pc` with both immediate flags
  (`rrs.rs:357-366`); `ECALL` reads `x5`, `x10`, `x11` (`rrs.rs:368-377`); trap instructions
  return `none`.
- `PicoFV/RV64IM/RVSail/BusesV3.lean`, namespace `RV64IM_Interactions.V3`: the Program and
  memory-dispatch entries and contracts, the row type `BusRow`, the five row predicates, the
  sorting of a raw row by tag and length, and `bus_operations`, the register and memory
  operations a row stands for. The register-access message keeps its 2.x shape
  `[chunk, clk, addr(3), value(4)]`, so the 2.x `StateBusEntry` contract is reused (a value read
  from a register has four 16-bit pieces). The ALU and Byte entries are reused too.

The Program contract, the central one:

```lean
def ProgramBusEntry.operand_properties (entry : ProgramBusEntry FKB) : Prop :=
  ∃ instruction pc data props,
    pc % 4 = 0 ∧ pc < Transpiler.V3.code_address_bound ∧          -- 0x7800_0000
    (.some ⟨ data, props ⟩ = Transpiler.V3.transpile_op instruction entry.multiplicity pc) ∧
    (entry = ProgramBusEntry.deserialise data) ∧ props
```

It says a real row's fetch message is a row of the table Pico builds at keygen: an address
`pc_base + 4i` with `pc_base` 4-aligned (`riscv_program/traces.rs:83-87`), below `0x7800_0000`
(`traces.rs:107-110`), its two 16-bit pieces, the decoded instruction, and
`pc_carry = [pc[0] >= 0xFFFC]` (`traces.rs:121-128`). Trap rows and padding repeat row 0
(`traces.rs:116-120, 140-150`). The CPU sends with multiplicity `is_real` and the table is
preprocessed, so the whole message matches one such row (`riscv_cpu/constraints.rs:51-75`).

The memory-dispatch contract keeps the 2.x content keyed on the opcode, since the width
selectors are gone, with the address bound the v3.1.1 memory chip proves: `2^16 <= b + c < 2^32`
(`riscv_memory/read_write/constraints.rs:209-255`). Its `chunk` and `clk` fields carry no
promise yet.

Two deliberate differences from the 2.x decoder, both about which traces the theorems apply to:
the 2.x decoder has no row for `ECALL`, so the hypothesis "every real row decodes to some
instruction" fails on any trace with an `ECALL` row; and it requires an even `JALR` offset,
which RISC-V does not. The 3.x decoder gives `ECALL` its row and drops the evenness condition;
the chip clears the low bit itself (`riscv_cpu/jump/constraints.rs:79-126`).

## The eight questions

1. **Where the contracts live.** In the two new files above. The 2.x `Buses.lean` and
   `Transpiler.lean` stay unchanged because the memory chip's proofs use them until the memory
   chip moves; `Transpiler.lean` cannot be rewritten in place for the same reason. *Prototype:*
   used both files unchanged.
2. **What the instruction fetch promises.** The decoded instruction plus the pc facts, through the
   contract above: two 16-bit pieces, 4-aligned, below `0x7800_0000`, and the carry bit's
   meaning. *Prototype:* `pc_facts` derives all four for every instruction; `next_pc_facts`
   uses them on the next row.
3. **The stronger whole-trace assumption.** See the next section. *Prototype:* needed, and
   sufficient for the three trial theorems.
4. **ALU opcodes 264 and 265.** Add them to `ALUBus.validOpcode` and `ALUBus.Spec`: result piece
   0 is `[b < c]`, piece 1 is `[b > c]` (signed for 264, unsigned for 265), and prove the
   less-than chip meets them. *Prototype:* the BEQ trial takes the 265 case as a hypothesis
   (`cmp_unsigned_spec`) and needs nothing else from the ALU side; pieces 2 and 3 are zeros
   the CPU writes itself.
5. **The memory contract.** As drafted: one predicate keyed on the opcode, address in
   `[2^16, 2^32)`, load results gated on `op_a_0 = 0`; what the CPU guarantees in return is the
   opcode, `is_memory = 1`, 16-bit operand pieces, a store's 16-bit value and `a = 0` when
   `op_a_0 = 1`. *Prototype:* not exercised; no trial loads or stores.
6. **The Ecall message.** Ignored when a row is sorted, as tag 8 was; ECALL stays outside the
   theorems. *Prototype:* confirmed. On every other row the chip forces `is_halt` and
   `num_extra_clk` to zero (extracted constraints 31 and 32), which is all the trials needed.
7. **Keeping `pico-v3-cpu` buildable.** Take the 13 instruction-theorem files out of the
   top-level build and move their 13 lists out of `scripts/fv-check/theorems.d/` until each is
   repaired. Only `Constraints/CpuChipInterpretations.lean` and the `Equivalence/` files import
   the CPU modules, so nothing else breaks. *Prototype:* did this; see the last section for what
   was built.
8. **CI.** Add `pico-v3-cpu` beside `main` and `pico-v3` in `.github/workflows/ci.yml`: the
   push trigger (line 8), the cancellation rule (line 14) and the cache-save condition
   (line 77). Not prototyped.

## The whole-trace assumption

Before (`Equivalence/Common.lean:68-71`):

```lean
def pico_CpuChip_control_flow_assumptions (air : Valid_CpuChip FKB ExtF) :=
  (air.public_values 43).val % 4 = 0
```

After, as the trial proofs use it:

```lean
def pico_CpuChip_control_flow_assumptions (air : Valid_CpuChip FKB ExtF) : Prop :=
  (air.public_values 43).val % 4 = 0 ∧
  (air.public_values 43).val < 65536 ∧
  (air.public_values 44).val < 65536 ∧
  (air.public_values 43).val + 65536 * (air.public_values 44).val < 0x7800_0000
```

Public values 43 and 44 are the two pieces of the chunk's final pc; the chip pins 45 to zero
itself. On the last real row the chip sets its `next_pc` to them (extracted constraints 41-43,
`riscv_cpu/public_values/constraints.rs:35-50`), and nothing in the chip range-checks them. The
trial proofs need each part: the 16-bit pieces and the alignment for the JALR addition, its
cleared low bit and BEQ's aligned target, and a bound on the value to read the `pc + 4` and
branch-target field equations as integer equations. The weakest bound the three trials need is `p - 4096` (`p` the KoalaBear
prime, `4096` the largest backward branch); `0x7800_0000` is slightly stronger, is the guest
address bound Pico itself uses, and also covers JAL's 21-bit offsets, which need `p - 2^20`.

Where Pico enforces it, outside the chips, in the recursion circuit
(`vm/src/mle/compiler/recursion/lowering.rs`): each chunk's final pc equals the next chunk's
first pc (`assert_child_continuity`, 1081-1090); a chunk that runs no CPU passes its pc through
unchanged (1436-1440); the root requires the last chunk's final pc to be zero
(`assert_root_complete`, 1748-1754). A chunk's first pc is its row 0's pc
(`riscv_cpu/public_values/constraints.rs:26-33`), row 0 is real
(`riscv_cpu/constraints.rs:340-341`) and its fetch matches the Program table, whose pcs are
4-aligned and below `0x7800_0000` (`riscv_program/traces.rs:83-110`). So in an accepted proof the
final pc is either zero or a Program-table pc, which satisfies the new wording. We found no
check of its own on the public value outside the chips (no range or alignment check in the
recursion circuit or the verifiers).

This strengthens a hypothesis of all 62 instruction theorems. They refer to it by name, so the
recorded statements in `signatures.txt` will not change; the pull request has to say so.

## Framework files the real work touches

- New: `RVSail/BusesV3.lean`, `Transpiler/TranspilerV3.lean`.
- `Airs/SubAirs.lean`: the lite register-access layouts (6 and 10 columns), beside the 2.x
  ones the memory chip uses. The prototype defines them in `Airs/CpuChip.lean`.
- `RVSail/Buses.lean`: the ALU cases 264 and 265.
- `Equivalence/Common.lean`: the whole-trace assumption, `CPU_bus_operations` (the next pc now
  has two pieces) and the operand helpers.
- `scripts/fv-check/theorems.d/`, `axioms.txt`, `signatures.txt`: parking and restoring the 13
  lists; `scripts/ci/heavy-modules.txt` if the interpretations module's memory use changes.
- `.github/workflows/ci.yml`: the branch lists.

`Fundamentals/` and `RVSail/Operations.lean` need no change: the trials used the existing
operation lemmas.

## The prototype

A local branch, not for merging. It regenerates `Extraction/CpuChip.lean` with the pinned
extractor (65 constraints, 17 messages), restates the 58 columns and the constraints over
named columns (each restatement proven equal to the extracted one), and adds
`Equivalence/TrialV3.lean` with three theorems in the 2.x form ("the row's operations change
the Sail state as one step of the instruction does"):

- `equivalence_ADD` (register form): operand reads, the ALU message, `pc + 4`, and the
  destination `x0` case, where the ALU message is not sent.
- `equivalence_BEQ`: the compare message with opcode 265, and the one-equation branch target
  read over the integers, for both outcomes.
- `equivalence_JALR`: the four-carry addition `rs1 + imm = next_pc + lsb` (`jalr_sum`), the
  cleared low bit, bit 1 of the target, and the return address `pc + 4` from `pc_carry`.

Hypotheses: the contracts on every row, the 65 constraints on every row, the new whole-trace
assumption, the instruction's opcode, the bus reads, and for BEQ and JALR the RISC-V state
assumptions the Sail specifications need. BEQ also takes the 265 stand-in. All three build with
no `sorry`, no new axiom and no `native_decide` or `bv_decide`; their axioms are exactly those
`axioms.txt` records for the 2.x theorems of the same names. With the 13 instruction-theorem
files and the 2.x interpretations file out of the build, `lake build PicoFV64` succeeds on the
prototype branch, so the rest of the repository is unaffected. The lemmas meant to carry over to
the interpretations file are `next_pc_facts`, `pc_facts`, `jalr_sum`, `jump_return_address`,
`branch_target_arith`, `imm_operand_sext`, `clear_low_bit` and `bit_one_zero`.
