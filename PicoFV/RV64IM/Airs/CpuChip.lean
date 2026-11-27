import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs

open Plonky3

set_option linter.unusedVariables false

/-!
# CpuChip (64-bit)

Lean formalisation of `CpuCols` and its sub-structures from
`vm/src/chips/chips/riscv_cpu/columns.rs`, which pins the width itself
(`riscv_cpu/columns.rs:20`):

```rust
const _: () = assert!(NUM_CPU_COLS == 58);
```

Citations read at Pico v3.2.0.

- **No committed `chunk`, one `clk` column.** Every message that names
  the chunk carries the `execution_chunk` public value, and `clk` is one
  free witness bounded by the row chain (`riscv_cpu/columns.rs:28-38`).
- **Two-limb addresses and sign-extended operands.** `Pc<T>` is
  `[T; 2]` (`vm/src/compiler/addr.rs:287`), and an instruction operand
  is a `SignExtImm<T>`: two u16 limbs plus one sign bit
  (`instruction/columns.rs:41-48`). `op_a` is a 5-bit register index in
  a single column.
- **Lite register accesses.** `MemoryAccessLiteCols` holds `value` plus
  the two difference limbs, with no committed `prev_clk`
  (`riscv_memory/read_write/columns.rs:399-419`). The three
  register-access groups are 10, 6 and 6 columns.

The branch bits `a_gt_b` / `a_lt_b` and the jump witness `jalr_lsb` are
plain columns, and `a_eq_b` is derived as `1 - a_lt_b - a_gt_b`. The
per-variant memory selectors live in the memory chip, leaving
`is_memory` and `is_store`; `is_alu` is derived as the one-hot
complement of the other class selectors.

```rust
pub struct SignExtImm<T> { pub limb: [T; 2], pub sign: T }          //  3

pub struct InstructionCols<T> {
    pub opcode: T,
    pub op_a: T,                                                     //  1
    pub op_b: SignExtImm<T>,                                         //  3
    pub op_c: SignExtImm<T>,                                         //  3
    pub op_a_0: T,
}                                                                    // total: 9

pub struct OpcodeSelectorCols<T> {
    pub imm_b: T, pub imm_c: T,
    pub is_ecall: T,
    pub is_memory: T, pub is_store: T,
    pub is_beq: T, pub is_bne: T, pub is_blt: T,
    pub is_bge: T, pub is_bltu: T, pub is_bgeu: T,
    pub is_jalr: T, pub is_jal: T,
}                                                                    // total: 13

pub struct MemoryAccessLiteCols<T> {
    pub value: Word<T>,                                              //  4
    pub diff_16bit_limb: T,
    pub diff_hi9: T,
}                                                                    // total: 6

pub struct MemoryReadLiteCols<T> { pub access: MemoryAccessLiteCols<T> }      //  6
pub struct MemoryReadWriteLiteCols<T> {
    pub prev_value: Word<T>,                                         //  4
    pub access: MemoryAccessLiteCols<T>,                             //  6
}                                                                    // total: 10
```

Top-level `CpuCols` (58 columns):
```rust
pub struct CpuCols<T> {
    pub clk: T,
    pub num_extra_clk: T,
    pub pc: Pc<T>,                                     //  2
    pub next_pc: Pc<T>,                                //  2
    pub instruction: InstructionCols<T>,               //  9
    pub opcode_selector: OpcodeSelectorCols<T>,        // 13
    pub op_a_access: MemoryReadWriteLiteCols<T>,       // 10
    pub op_b_access: MemoryReadLiteCols<T>,            //  6
    pub op_c_access: MemoryReadLiteCols<T>,            //  6
    pub a_gt_b: T,
    pub a_lt_b: T,
    pub is_halt: T,
    pub is_real: T,
    pub is_last: T,
    pub is_alu_not_x0: T,
    pub jalr_lsb: T,
    pub pc_carry: T,
}
```

Layout: 1 + 1 + 2 + 2 + 9 + 13 + 10 + 6 + 6 + 8 = **58 columns**.
This matches `Extraction/CpuChip.lean`, which uses every index in
`0..57`.

The three register accesses use the lite layouts `MemoryReadWriteLiteCols`
(10 columns) and `MemoryReadLiteCols` (6), defined in `Airs/SubAirs.lean`,
because Pico's memory chip uses the same lite
layout (`riscv_memory/read_write/columns.rs:72-74`).
-/

-- ============================================================================
-- InstructionCols (9 columns)
--
-- `instruction/columns.rs:13-29`. `op_a` is a 5-bit register index in one
-- column; `op_b` and `op_c` are `SignExtImm` — two u16 limbs and a sign
-- bit standing for the all-zero or all-one fill of bits 32..64.
-- ============================================================================

#define_subair "InstructionCols" using "pico_encapsulation" where
  Column["opcode"]
  Column["op_a"]
  Column["op_b_0"]
  Column["op_b_1"]
  Column["op_b_sign"]
  Column["op_c_0"]
  Column["op_c_1"]
  Column["op_c_sign"]
  Column["op_a_is_x0"]

-- ============================================================================
-- OpcodeSelectorCols (13 columns)
--
-- `opcode_selector/columns.rs:12-66`. `is_alu` is derived, not committed:
-- `is_alu = is_real - (is_ecall + is_memory + Σbranch + is_jal + is_jalr)`.
-- The per-variant memory selectors live in the memory chip.
-- ============================================================================

#define_subair "OpcodeSelectorCols" using "pico_encapsulation" where
  Column["imm_b"]
  Column["imm_c"]
  Column["is_ecall"]
  Column["is_memory"]
  Column["is_store"]
  Column["is_beq"]
  Column["is_bne"]
  Column["is_blt"]
  Column["is_bge"]
  Column["is_bltu"]
  Column["is_bgeu"]
  Column["is_jalr"]
  Column["is_jal"]

-- ============================================================================
-- CpuCols (58 columns)
-- ============================================================================

#define_subair "CpuCols" using "pico_encapsulation" where
  Column["clk"]
  Column["num_extra_clk"]
  -- pc: Pc<T> = [T; 2]
  Column["pc_0"]
  Column["pc_1"]
  -- next_pc: Pc<T> = [T; 2]
  Column["next_pc_0"]
  Column["next_pc_1"]
  SubAir["instruction": "InstructionCols" width := 9]
  SubAir["opcode_selector": "OpcodeSelectorCols" width := 13]
  SubAir["op_a_access": "MemoryReadWriteLiteCols" width := 10]
  SubAir["op_b_access": "MemoryReadLiteCols" width := 6]
  SubAir["op_c_access": "MemoryReadLiteCols" width := 6]
  -- Branch comparison bits; `a_eq_b` is `1 - a_lt_b - a_gt_b`.
  Column["a_gt_b"]
  Column["a_lt_b"]
  Column["is_halt"]
  Column["is_real"]
  Column["is_last"]
  Column["is_alu_not_x0"]
  Column["jalr_lsb"]
  Column["pc_carry"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "CpuChip" using "pico_encapsulation" where
  MainSubAir["cols": "CpuCols" width := 58]
