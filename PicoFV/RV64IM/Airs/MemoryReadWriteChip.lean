import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs
import PicoFV.RV64IM.Airs.CodeRangeGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# MemoryReadWriteChip (64-bit)

Lean formalisation of `MemoryChipCols` / `MemoryChipValueCols` from
`vm/src/chips/chips/riscv_memory/read_write/columns.rs`. `MemoryInstructionCols`, quoted below for the
table, is formalised in `Airs/SubAirs.lean`: `MemoryUnalignedChip` has one too, and a chip's files
may not import another chip's.

Citations read at Pico v3.2.0.

```rust
pub struct MemoryChipCols<F> {
    pub values: [MemoryChipValueCols<F>; MEMORY_RW_DATAPAR],   // MEMORY_RW_DATAPAR = 1
}

pub struct MemoryChipValueCols<F> {
    pub chunk: F,
    pub clk: F,
    pub addr_word: [F; 2],
    pub offset_bit: [F; 3],
    pub addr_limb1_inv: F,
    pub memory_access: MemoryReadWriteLiteCols<F>,   // 10
    pub selected_limb: F,
    pub selected_byte: F,
    pub msb: F,
    pub lhw_val: F,
    pub register_low_byte: F,
    pub mem_limb_low_byte: F,
    pub shift: F,
    pub instruction: MemoryInstructionCols<F>,       // 24
    pub code_range: CodeRangeCols<F>,                //  8
}

pub struct MemoryInstructionCols<T> {
    pub op_a_0: T,
    pub is_lb: T, pub is_lbu: T, pub is_lh: T, pub is_lhu: T,
    pub is_lw: T, pub is_lwu: T, pub is_ld: T,
    pub is_sb: T, pub is_sh: T, pub is_sw: T, pub is_sd: T,
    pub op_a_value: Word<T>,
    pub op_b_value: Word<T>,
    pub op_c_value: Word<T>,
}
```

Layout: 1 + 1 + 2 + 3 + 1 + 10 + 7 + 24 + 8 = 57 columns, the width
`riscv_memory/read_write/columns.rs:30` asserts and the extraction at
`Extraction/MemoryReadWriteChip.lean` uses.

| columns | name (under `values`) | meaning |
|---------|-----------------------|---------|
| 0, 1    | `chunk`, `clk` | the row's chunk and clock, bound to the CPU row by the dispatch message |
| 2, 3    | `addr_word_0`, `_1` | the address `b + c`, two 16-bit pieces |
| 4..6    | `offset_bit_0..2` | the address's three low bits |
| 7       | `addr_limb1_inv` | inverse of `addr_word_1`: the address is at least 2^16 |
| 8..11   | `memory_access.prev_value_0..3` | the aligned double word before the access |
| 12..15  | `memory_access.access.value_0..3` | the aligned double word after the access |
| 16, 17  | `memory_access.access.diff_16bit_limb`, `diff_hi9` | `clk - prev_clk - 1` as a 16-bit and a 9-bit piece |
| 18      | `selected_limb` | the 16-bit piece of the double word the offset selects |
| 19      | `selected_byte` | the byte a byte load reads |
| 20      | `msb` | the sign bit of a signed load |
| 21      | `lhw_val` | the operand of the sign-bit check; the high half of a word load |
| 22      | `register_low_byte` | a byte store's byte |
| 23      | `mem_limb_low_byte` | the low byte of `selected_limb` |
| 24      | `shift` | what a byte or half-word store adds to the selected piece |
| 25      | `instruction.op_a_0` | 1 when register `a` is `x0` |
| 26..36  | `instruction.is_lb` … `is_sd` | one flag per memory instruction |
| 37..48  | `instruction.op_{a,b,c}_value_0..3` | the three operands, four 16-bit pieces each |
| 49..56  | `code_range.*` | the `code_range` gadget (`Airs/CodeRangeGadget.lean`) |
-/

-- ============================================================================
-- MemoryChipValueCols (57 columns)
-- ============================================================================

#define_subair "MemoryChipValueCols" using "pico_encapsulation" where
  Column["chunk"]
  Column["clk"]
  Column["addr_word_0"]
  Column["addr_word_1"]
  Column["offset_bit_0"]
  Column["offset_bit_1"]
  Column["offset_bit_2"]
  Column["addr_limb1_inv"]
  SubAir["memory_access": "MemoryReadWriteLiteCols" width := 10]
  Column["selected_limb"]
  Column["selected_byte"]
  Column["msb"]
  Column["lhw_val"]
  Column["register_low_byte"]
  Column["mem_limb_low_byte"]
  Column["shift"]
  SubAir["instruction": "MemoryInstructionCols" width := 24]
  SubAir["code_range": "CodeRangeGadget" width := 8]

-- ============================================================================
-- MemoryChipCols (57 columns, MEMORY_RW_DATAPAR = 1)
-- ============================================================================

#define_subair "MemoryChipCols" using "pico_encapsulation" where
  SubAir["values": "MemoryChipValueCols" width := 57]

#define_air "MemoryReadWriteChip" using "pico_encapsulation" where
  MainSubAir["cols": "MemoryChipCols" width := 57]

-- ============================================================================
-- Computed values
-- ============================================================================

/-- The number of bytes a store writes: 1, 2, 4 or 8 on a store row, 0 on any other row.
    `width` in `MemoryReadWriteChip::eval` (`riscv_memory/read_write/constraints.rs:97-101`),
    the width it hands the `code_range` gadget. -/
def Valid_MemoryChipValueCols.store_width
  [Field F]
  (c : Valid_MemoryChipValueCols F) (row rotation : ℕ)
: F :=
  c.instruction.is_sb row rotation +
  2 * c.instruction.is_sh row rotation +
  4 * c.instruction.is_sw row rotation +
  8 * c.instruction.is_sd row rotation
