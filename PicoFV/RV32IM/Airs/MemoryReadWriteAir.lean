import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV32IM.Extraction.Attributes
import PicoFV.RV32IM.Airs.Attributes
import PicoFV.RV32IM.Airs.SubAirs  -- reuse MemoryAccessCols, MemoryReadWriteCols

open Plonky3

set_option linter.unusedVariables false

/-!
# MemoryReadWriteAir

Lean formalisation of the Pico RISC-V memory read/write chip AIR.

Rust sources:
- MemoryChipValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/riscv_memory/read_write/columns.rs
- MemoryInstructionCols:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/riscv_memory/read_write/columns.rs

## Nested types (reused from CpuAir)

- MemoryAccessCols = 9 columns (value:4, prev_chunk, prev_clk, compare_clk, diff_16bit_limb, diff_8bit_limb)
- MemoryReadWriteCols = 13 columns (prev_value:4, access:MemoryAccessCols:9)
- FieldWordRangeChecker = 10 columns (most_sig_byte_decomp:8, upper_all_one:IsZeroGadget:2)

## New types

- MemoryInstructionCols = 41 columns
  opcode, op_a_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw,
  op_a_access:MemoryReadWriteCols:13, op_b_access:MemoryAccessCols:9,
  op_c_access:MemoryAccessCols:9

## Column layout (95 columns total)

| Group                    | Columns                          | Count |
|--------------------------|----------------------------------|-------|
| chunk, clk               | chunk, clk                       | 2     |
| addr_word (Word)         | addr_word_{0..3}                 | 4     |
| addr_word_range_checker  | addr_wrc_*                       | 10    |
| addr_aligned             | addr_aligned                     | 1     |
| aa_least_sig_byte_decomp | aa_lsb_decomp_{0..5}            | 6     |
| addr_offset              | addr_offset                      | 1     |
| memory_access            | MemoryReadWriteCols              | 13    |
| offset_is_*              | offset_is_one/two/three          | 3     |
| most_sig_byte_decomp     | msb_decomp_{0..7}               | 8     |
| unsigned_mem_val (Word)  | unsigned_mem_val_{0..3}          | 4     |
| mem_value flags          | mem_value_is_pos_not_x0, mem_value_is_neg_not_x0 | 2 |
| instruction              | MemoryInstructionCols            | 41    |
-/

-- ============================================================================
-- Sub-air definitions
-- ============================================================================

-- Rust: FieldWordRangeChecker (10 columns)
-- Fields: most_sig_byte_decomp (8), upper_all_one.inverse, upper_all_one.result
#define_subair "FieldWordRangeChecker" using "pico_encapsulation" where
  Column["most_sig_byte_decomp_0"]
  Column["most_sig_byte_decomp_1"]
  Column["most_sig_byte_decomp_2"]
  Column["most_sig_byte_decomp_3"]
  Column["most_sig_byte_decomp_4"]
  Column["most_sig_byte_decomp_5"]
  Column["most_sig_byte_decomp_6"]
  Column["most_sig_byte_decomp_7"]
  Column["upper_all_one_inverse"]
  Column["upper_all_one_result"]

-- Rust: MemoryInstructionCols (41 columns)
-- Fields: opcode, op_a_0, is_lb..is_sw (8 flags),
--         op_a_access (MemoryReadWriteCols:13),
--         op_b_access (MemoryAccessCols:9),
--         op_c_access (MemoryAccessCols:9)
#define_subair "MemoryInstructionCols" using "pico_encapsulation" where
  Column["opcode"]
  Column["op_a_0"]
  Column["is_lb"]
  Column["is_lbu"]
  Column["is_lh"]
  Column["is_lhu"]
  Column["is_lw"]
  Column["is_sb"]
  Column["is_sh"]
  Column["is_sw"]
  SubAir["op_a_access": "MemoryReadWriteCols" width := 13]
  SubAir["op_b_access": "MemoryAccessCols" width := 9]
  SubAir["op_c_access": "MemoryAccessCols" width := 9]

-- ============================================================================
-- MemoryChipCols (95 columns total)
-- ============================================================================

#define_subair "MemoryChipCols" using "pico_encapsulation" where
  -- chunk, clk
  Column["chunk"]
  Column["clk"]
  -- addr_word (Word)
  Column["addr_word_0"]
  Column["addr_word_1"]
  Column["addr_word_2"]
  Column["addr_word_3"]
  -- addr_word_range_checker (FieldWordRangeChecker = 10)
  SubAir["addr_word_range_checker": "FieldWordRangeChecker" width := 10]
  -- addr_aligned
  Column["addr_aligned"]
  -- aa_least_sig_byte_decomp[6]
  Column["aa_lsb_decomp_0"]
  Column["aa_lsb_decomp_1"]
  Column["aa_lsb_decomp_2"]
  Column["aa_lsb_decomp_3"]
  Column["aa_lsb_decomp_4"]
  Column["aa_lsb_decomp_5"]
  -- addr_offset
  Column["addr_offset"]
  -- memory_access (MemoryReadWriteCols = 13)
  SubAir["memory_access": "MemoryReadWriteCols" width := 13]
  -- offset_is_one, offset_is_two, offset_is_three
  Column["offset_is_one"]
  Column["offset_is_two"]
  Column["offset_is_three"]
  -- most_sig_byte_decomp[8]
  Column["msb_decomp_0"]
  Column["msb_decomp_1"]
  Column["msb_decomp_2"]
  Column["msb_decomp_3"]
  Column["msb_decomp_4"]
  Column["msb_decomp_5"]
  Column["msb_decomp_6"]
  Column["msb_decomp_7"]
  -- unsigned_mem_val (Word)
  Column["unsigned_mem_val_0"]
  Column["unsigned_mem_val_1"]
  Column["unsigned_mem_val_2"]
  Column["unsigned_mem_val_3"]
  -- mem_value flags
  Column["mem_value_is_pos_not_x0"]
  Column["mem_value_is_neg_not_x0"]
  -- instruction (MemoryInstructionCols = 41)
  SubAir["instruction": "MemoryInstructionCols" width := 41]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "MemoryReadWriteAir" using "pico_encapsulation" where
  MainSubAir["cols": "MemoryChipCols" width := 95]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: sum of instruction flags (the "is_real" multiplier)
def Valid_MemoryChipCols.is_real
  [Field F]
  (c : Valid_MemoryChipCols F) (row rotation : ℕ)
: F :=
  c.instruction.is_lb row rotation +
  c.instruction.is_lbu row rotation +
  c.instruction.is_lh row rotation +
  c.instruction.is_lhu row rotation +
  c.instruction.is_lw row rotation +
  c.instruction.is_sb row rotation +
  c.instruction.is_sh row rotation +
  c.instruction.is_sw row rotation

@[pico_encapsulation]
lemma MemoryChipCols.is_real_def
  [Field F]
  (c : Valid_MemoryChipCols F) (row rotation : ℕ)
:
  c.instruction.is_lb row rotation +
  c.instruction.is_lbu row rotation +
  c.instruction.is_lh row rotation +
  c.instruction.is_lhu row rotation +
  c.instruction.is_lw row rotation +
  c.instruction.is_sb row rotation +
  c.instruction.is_sh row rotation +
  c.instruction.is_sw row rotation =
  c.is_real row rotation
:= rfl

-- ============================================================================
-- Lifted to Air level
-- ============================================================================

@[pico_encapsulation]
lemma MemoryReadWriteAir.is_real_def
  [Field F] [Field ExtF]
  (air : Valid_MemoryReadWriteAir F ExtF) (row rotation : ℕ)
:
  air.cols.instruction.is_lb row rotation +
  air.cols.instruction.is_lbu row rotation +
  air.cols.instruction.is_lh row rotation +
  air.cols.instruction.is_lhu row rotation +
  air.cols.instruction.is_lw row rotation +
  air.cols.instruction.is_sb row rotation +
  air.cols.instruction.is_sh row rotation +
  air.cols.instruction.is_sw row rotation =
  air.cols.is_real row rotation
:= rfl
