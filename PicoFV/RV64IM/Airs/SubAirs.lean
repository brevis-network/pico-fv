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
