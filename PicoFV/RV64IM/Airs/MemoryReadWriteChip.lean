import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs

open Plonky3

set_option linter.unusedVariables false

/-!
# MemoryReadWriteChip (64-bit)

Lean formalisation of `MemoryChipCols` / `MemoryChipValueCols` /
`MemoryInstructionCols` from
`vm/src/chips/chips/riscv_memory/read_write/columns.rs` at commit
`0ecd943c3dba682e1848d1f2d52ac50a24949d8a` (Pico PR #101 head).

```rust
pub struct MemoryChipCols<F> {
    pub values: [MemoryChipValueCols<F>; MEMORY_RW_DATAPAR],   // = 1
}

pub struct MemoryChipValueCols<F> {
    pub chunk: F,
    pub clk: F,
    pub addr_word: Word<F>,
    pub offset_bit: [F; 3],
    pub limb_select: [F; 4],
    pub addr_top_two_limb_inv: F,
    pub memory_access: MemoryReadWriteCols<F>,            // 13
    pub selected_limb: F,
    pub selected_limb_low_byte: F,
    pub selected_byte: F,
    pub selected_word: [F; 2],
    pub msb: F,
    pub register_low_byte: F,
    pub mem_limb_low_byte: F,
    pub increment: F,
    pub store_value: Word<F>,
    pub unsigned_mem_val: Word<F>,
    pub mem_value_is_pos_not_x0: F,
    pub mem_value_is_neg_not_x0: F,
    pub instruction: MemoryInstructionCols<F>,            // 34
}

pub struct MemoryInstructionCols<T> {
    pub opcode: T,
    pub op_a_0: T,
    pub is_lb: T, pub is_lbu: T,
    pub is_lh: T, pub is_lhu: T,
    pub is_lw: T, pub is_lwu: T,
    pub is_ld: T,
    pub is_sb: T, pub is_sh: T, pub is_sw: T, pub is_sd: T,
    pub op_a_access: MemoryReadWriteCols<T>,              // 13
    pub op_b_access: Word<T>,                             //  4
    pub op_c_access: Word<T>,                             //  4
}
```

Layout: 1 + 1 + 4 + 3 + 4 + 1 + 13 + 1 + 1 + 1 + 2 + 1 + 1 + 1 + 1 + 4 +
4 + 1 + 1 + 34 = **80 columns** total (matches Pico's
`BaseAir<F>::width = NUM_MEMORY_CHIP_COLS = size_of::<MemoryChipValueCols<u8>>()`).

Post-PR #101 column layout deltas from the prior `b6f2de04` baseline:
* `addr_aligned: Word<F>` removed (4 cols) — aligned address now computed
  inline as `addr_word_0 - offset_sum` in the State/Memory bus lookup tuples.
  See commit `db682d9c`.
* `op_b_access`/`op_c_access` changed from `MemoryReadCols<T>` (9 cols each)
  to `Word<T>` (4 cols each), removing 10 unused metadata cols (5 per operand:
  `prev_chunk`, `prev_clk`, `compare_clk`, `diff_16bit_limb`, `diff_8bit_limb`).
  See commit `0ecd943c`.
-/

-- ============================================================================
-- MemoryInstructionCols (34 columns)
-- ============================================================================
-- Post-Pico PR #101 commit `0ecd943c`: op_b_access and op_c_access changed from
-- MemoryReadCols (9 cols each) to plain Word (4 cols each), removing 10 unused
-- metadata cols total.

#define_subair "MemoryInstructionCols" using "pico_encapsulation" where
  Column["opcode"]
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
  SubAir["op_a_access": "MemoryReadWriteCols" width := 13]
  -- op_b_access (Word = 4)
  Column["op_b_access_0"]
  Column["op_b_access_1"]
  Column["op_b_access_2"]
  Column["op_b_access_3"]
  -- op_c_access (Word = 4)
  Column["op_c_access_0"]
  Column["op_c_access_1"]
  Column["op_c_access_2"]
  Column["op_c_access_3"]

-- ============================================================================
-- MemoryChipValueCols (80 columns)
-- ============================================================================
-- Post-Pico PR #101 commit `db682d9c`: addr_aligned (4 cols) removed; the
-- aligned address is computed inline as `addr_word_0 - offset_sum` in the
-- State-bus / Memory-bus lookup tuples.

#define_subair "MemoryChipValueCols" using "pico_encapsulation" where
  Column["chunk"]
  Column["clk"]
  -- addr_word (Word = 4)
  Column["addr_word_0"]
  Column["addr_word_1"]
  Column["addr_word_2"]
  Column["addr_word_3"]
  -- offset_bit ([F; 3])
  Column["offset_bit_0"]
  Column["offset_bit_1"]
  Column["offset_bit_2"]
  -- limb_select ([F; 4])
  Column["limb_select_0"]
  Column["limb_select_1"]
  Column["limb_select_2"]
  Column["limb_select_3"]
  Column["addr_top_two_limb_inv"]
  -- memory_access (MemoryReadWriteCols = 13)
  SubAir["memory_access": "MemoryReadWriteCols" width := 13]
  Column["selected_limb"]
  Column["selected_limb_low_byte"]
  Column["selected_byte"]
  -- selected_word ([F; 2])
  Column["selected_word_0"]
  Column["selected_word_1"]
  Column["msb"]
  Column["register_low_byte"]
  Column["mem_limb_low_byte"]
  Column["increment"]
  -- store_value (Word = 4)
  Column["store_value_0"]
  Column["store_value_1"]
  Column["store_value_2"]
  Column["store_value_3"]
  -- unsigned_mem_val (Word = 4)
  Column["unsigned_mem_val_0"]
  Column["unsigned_mem_val_1"]
  Column["unsigned_mem_val_2"]
  Column["unsigned_mem_val_3"]
  Column["mem_value_is_pos_not_x0"]
  Column["mem_value_is_neg_not_x0"]
  -- instruction (MemoryInstructionCols = 34)
  SubAir["instruction": "MemoryInstructionCols" width := 34]

-- ============================================================================
-- MemoryChipCols (80 columns — single value, MEMORY_RW_DATAPAR = 1)
-- ============================================================================

#define_subair "MemoryChipCols" using "pico_encapsulation" where
  SubAir["values": "MemoryChipValueCols" width := 80]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "MemoryReadWriteChip" using "pico_encapsulation" where
  MainSubAir["cols": "MemoryChipCols" width := 80]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: sum of instruction selectors (the "is_real" multiplier)
def Valid_MemoryChipValueCols.is_real
  [Field F]
  (c : Valid_MemoryChipValueCols F) (row rotation : ℕ)
: F :=
  c.instruction.is_lb row rotation +
  c.instruction.is_lbu row rotation +
  c.instruction.is_lh row rotation +
  c.instruction.is_lhu row rotation +
  c.instruction.is_lw row rotation +
  c.instruction.is_lwu row rotation +
  c.instruction.is_ld row rotation +
  c.instruction.is_sb row rotation +
  c.instruction.is_sh row rotation +
  c.instruction.is_sw row rotation +
  c.instruction.is_sd row rotation

@[pico_encapsulation]
lemma MemoryChipValueCols.is_real_def
  [Field F]
  (c : Valid_MemoryChipValueCols F) (row rotation : ℕ)
:
  c.instruction.is_lb row rotation +
  c.instruction.is_lbu row rotation +
  c.instruction.is_lh row rotation +
  c.instruction.is_lhu row rotation +
  c.instruction.is_lw row rotation +
  c.instruction.is_lwu row rotation +
  c.instruction.is_ld row rotation +
  c.instruction.is_sb row rotation +
  c.instruction.is_sh row rotation +
  c.instruction.is_sw row rotation +
  c.instruction.is_sd row rotation =
  c.is_real row rotation
:= rfl
