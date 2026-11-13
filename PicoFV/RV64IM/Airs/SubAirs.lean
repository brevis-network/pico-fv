import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# Shared Sub-air definitions (64-bit memory)

Common column structures from
`vm/src/chips/chips/riscv_memory/read_write/columns.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. These are reused across chips
(`CpuChip`, `MemoryReadWriteChip`, …).

The Lite layouts at the end of the file are the v3.1.1 shapes from
`riscv_memory/read_write/columns.rs:395-415` at commit
`2acc7c1828fb4ec1bed5963511bb370870c5b608` (Pico v3.1.1). The CPU chip
uses them for its three register accesses, and the memory chip's data
access uses `MemoryReadWriteLiteCols` (`columns.rs:73`). The 2.x layouts
above stay until the memory chip's proofs move.

```rust
pub struct MemoryAccessCols<T> {
    pub value: Word<T>,           // 4 limbs
    pub prev_chunk: T,
    pub prev_clk: T,
    pub compare_clk: T,
    pub diff_16bit_limb: T,
    pub diff_8bit_limb: T,
}                                 // 9 cols total

pub struct MemoryReadCols<T> {
    pub access: MemoryAccessCols<T>,
}                                 // 9 cols total

pub struct MemoryWriteCols<T> {
    pub prev_value: Word<T>,
    pub access: MemoryAccessCols<T>,
}                                 // 13 cols total

pub struct MemoryReadWriteCols<T> {
    pub prev_value: Word<T>,
    pub access: MemoryAccessCols<T>,
}                                 // 13 cols total
```
-/

-- ============================================================================
-- MemoryAccessCols (9 columns)
-- ============================================================================

#define_subair "MemoryAccessCols" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  Column["value_2"]
  Column["value_3"]
  Column["prev_chunk"]
  Column["prev_clk"]
  Column["compare_clk"]
  Column["diff_16bit_limb"]
  Column["diff_8bit_limb"]

-- ============================================================================
-- MemoryReadCols (9 columns) — same shape as MemoryAccessCols
-- ============================================================================

#define_subair "MemoryReadCols" using "pico_encapsulation" where
  SubAir["access": "MemoryAccessCols" width := 9]

-- ============================================================================
-- MemoryWriteCols (13 columns)
-- ============================================================================

#define_subair "MemoryWriteCols" using "pico_encapsulation" where
  Column["prev_value_0"]
  Column["prev_value_1"]
  Column["prev_value_2"]
  Column["prev_value_3"]
  SubAir["access": "MemoryAccessCols" width := 9]

-- ============================================================================
-- MemoryReadWriteCols (13 columns) — same shape as MemoryWriteCols
-- ============================================================================

#define_subair "MemoryReadWriteCols" using "pico_encapsulation" where
  Column["prev_value_0"]
  Column["prev_value_1"]
  Column["prev_value_2"]
  Column["prev_value_3"]
  SubAir["access": "MemoryAccessCols" width := 9]

-- ============================================================================
-- MemoryAccessLiteCols (6 columns)
--
-- `riscv_memory/read_write/columns.rs:404-415`. No committed `prev_clk`:
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
