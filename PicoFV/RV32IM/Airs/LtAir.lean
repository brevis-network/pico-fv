import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV32IM.Extraction.Attributes
import PicoFV.RV32IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# LtAir

Lean formalisation of the Pico RISC-V comparison chip AIR (SLT, SLTU).

Rust sources:
- LtValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/lt/columns.rs

## Column layout (30 columns total)

| Group              | Columns                      | Count |
|--------------------|------------------------------|-------|
| Operation selectors| is_slt, is_slt_u             | 2     |
| a (Word)           | a_{0..3}                     | 4     |
| b (Word)           | b_{0..3}                     | 4     |
| c (Word)           | c_{0..3}                     | 4     |
| Byte flags         | byte_flags_{0..3}            | 4     |
| Masked values      | b_masked, c_masked           | 2     |
| Bit values         | bit_b, bit_c                 | 2     |
| Comparison helpers | not_eq_inv, msb_b, msb_c, slt_u, is_cmp_eq, is_sign_bit_same | 6 |
| Comparison bytes   | cmp_bytes_{0..1}             | 2     |
-/

-- ============================================================================
-- LtCols (30 columns total)
-- ============================================================================

#define_subair "LtCols" using "pico_encapsulation" where
  -- Operation selectors
  Column["is_slt"]
  Column["is_slt_u"]
  -- a (Word)
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  -- b (Word)
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  -- c (Word)
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  -- Byte flags
  Column["byte_flags_0"]
  Column["byte_flags_1"]
  Column["byte_flags_2"]
  Column["byte_flags_3"]
  -- Masked values
  Column["b_masked"]
  Column["c_masked"]
  -- Bit values
  Column["bit_b"]
  Column["bit_c"]
  -- Comparison helpers
  Column["not_eq_inv"]
  Column["msb_b"]
  Column["msb_c"]
  Column["slt_u"]
  Column["is_cmp_eq"]
  Column["is_sign_bit_same"]
  -- Comparison bytes
  Column["cmp_bytes_0"]
  Column["cmp_bytes_1"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "LtAir" using "pico_encapsulation" where
  MainSubAir["cols": "LtCols" width := 30]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_slt + is_slt_u (the "is_real" multiplier)
def Valid_LtCols.is_real
  [Field F]
  (c : Valid_LtCols F) (row rotation : ℕ)
: F :=
  c.is_slt row rotation +
  c.is_slt_u row rotation

@[pico_encapsulation]
lemma LtCols.is_real_def
  [Field F]
  (c : Valid_LtCols F) (row rotation : ℕ)
:
  c.is_slt row rotation +
  c.is_slt_u row rotation =
  c.is_real row rotation
:= rfl

-- ============================================================================
-- Lifted to Air level
-- ============================================================================

@[pico_encapsulation]
lemma LtAir.is_real_def
  [Field F] [Field ExtF]
  (air : Valid_LtAir F ExtF) (row rotation : ℕ)
:
  air.cols.is_slt row rotation +
  air.cols.is_slt_u row rotation =
  air.cols.is_real row rotation
:= rfl
