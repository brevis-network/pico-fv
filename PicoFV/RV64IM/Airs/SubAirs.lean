import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# Shared sub-air definitions (64-bit memory)

The memory-access column layouts from `vm/src/chips/chips/riscv_memory/read_write/columns.rs` at
Pico v3.1.6 (`6aa644efeff9ddbec6beb538200f98f2a70f5d8e`), shared by the CPU chip (its three
register accesses) and `MemoryReadWriteChip` (its data access,
`riscv_memory/read_write/columns.rs:74`).

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
