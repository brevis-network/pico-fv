import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# Shared sub-air definitions (64-bit memory)

The column layouts from `vm/src/chips/chips/riscv_memory/read_write/columns.rs` at Pico v3.1.6
(`6aa644efeff9ddbec6beb538200f98f2a70f5d8e`) that more than one chip uses. The memory-access
layouts are shared by the CPU chip (its three register accesses), `MemoryReadWriteChip` (its data
access, `riscv_memory/read_write/columns.rs:74`) and `MemoryUnalignedChip` (its two dword
accesses, `riscv_memory/unaligned/columns.rs:41-45`); `MemoryInstructionCols` by the two memory
chips.

```rust
pub struct MemoryAccessLiteCols<T> {      // riscv_memory/read_write/columns.rs:410-419
    pub value: Word<T>,                   // 4 limbs
    pub diff_16bit_limb: T,
    pub diff_hi9: T,
}                                         // 6 cols total

pub struct MemoryReadLiteCols<T> {        // riscv_memory/read_write/columns.rs:387-389
    pub access: MemoryAccessLiteCols<T>,
}                                         // 6 cols total

pub struct MemoryReadWriteLiteCols<T> {   // riscv_memory/read_write/columns.rs:394-397
    pub prev_value: Word<T>,
    pub access: MemoryAccessLiteCols<T>,
}                                         // 10 cols total
```
-/

-- ============================================================================
-- MemoryAccessLiteCols (6 columns)
--
-- `riscv_memory/read_write/columns.rs:410-419`. No committed `prev_clk`:
-- the AIR defines it as `clk - (diff_16bit_limb + diff_hi9 * 2^16) - 1`,
-- so the two difference limbs carry the timestamp argument alone.
-- ============================================================================

#define_subair "MemoryAccessLiteCols" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  Column["value_2"]
  Column["value_3"]
  Column["diff_16bit_limb"]
  Column["diff_hi9"]

-- ============================================================================
-- MemoryReadLiteCols (6 columns) — same shape as MemoryAccessLiteCols
-- ============================================================================

#define_subair "MemoryReadLiteCols" using "pico_encapsulation" where
  SubAir["access": "MemoryAccessLiteCols" width := 6]

-- ============================================================================
-- MemoryReadWriteLiteCols (10 columns)
-- ============================================================================

#define_subair "MemoryReadWriteLiteCols" using "pico_encapsulation" where
  Column["prev_value_0"]
  Column["prev_value_1"]
  Column["prev_value_2"]
  Column["prev_value_3"]
  SubAir["access": "MemoryAccessLiteCols" width := 6]

-- ============================================================================
-- MemoryInstructionCols (24 columns)
--
-- `riscv_memory/read_write/columns.rs:146-179`. Both memory chips have one: `MemoryReadWriteChip`
-- and `MemoryUnalignedChip`, which imports it from the read/write chip's module
-- (`riscv_memory/unaligned/columns.rs:3-5`). It lives here because a chip's files may not import
-- another chip's.
-- ============================================================================

#define_subair "MemoryInstructionCols" using "pico_encapsulation" where
  Column["op_a_0"]
  Column["is_lb"]
  Column["is_lbu"]
  Column["is_lh"]
  Column["is_lhu"]
  Column["is_lw"]
  Column["is_lwu"]
  Column["is_ld"]
  Column["is_sb"]
  Column["is_sh"]
  Column["is_sw"]
  Column["is_sd"]
  Column["op_a_value_0"]
  Column["op_a_value_1"]
  Column["op_a_value_2"]
  Column["op_a_value_3"]
  Column["op_b_value_0"]
  Column["op_b_value_1"]
  Column["op_b_value_2"]
  Column["op_b_value_3"]
  Column["op_c_value_0"]
  Column["op_c_value_1"]
  Column["op_c_value_2"]
  Column["op_c_value_3"]
