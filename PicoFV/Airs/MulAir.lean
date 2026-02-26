import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.Extraction.Attributes
import PicoFV.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# MulAir

Lean formalisation of the Pico RISC-V multiplication chip AIR (MUL, MULH, MULHU, MULHSU).

Rust sources:
- MulValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/mul/columns.rs

## Column layout (37 columns total)

| Group              | Columns                      | Count |
|--------------------|------------------------------|-------|
| a (Word)           | a_{0..3}                     | 4     |
| b (Word)           | b_{0..3}                     | 4     |
| c (Word)           | c_{0..3}                     | 4     |
| carry              | carry_{0..7}                 | 8     |
| product            | product_{0..7}               | 8     |
| Sign bits          | b_msb, c_msb, b_sign_extend, c_sign_extend | 4 |
| Operation selectors| is_mul, is_mulh, is_mulhu, is_mulhsu | 4 |
| Control            | is_real                      | 1     |
-/

-- ============================================================================
-- MulCols (37 columns total)
-- ============================================================================

#define_subair "MulCols" using "pico_encapsulation" where
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
  -- carry[8]
  Column["carry_0"]
  Column["carry_1"]
  Column["carry_2"]
  Column["carry_3"]
  Column["carry_4"]
  Column["carry_5"]
  Column["carry_6"]
  Column["carry_7"]
  -- product[8] (LONG_WORD_SIZE = 2 * WORD_SIZE)
  Column["product_0"]
  Column["product_1"]
  Column["product_2"]
  Column["product_3"]
  Column["product_4"]
  Column["product_5"]
  Column["product_6"]
  Column["product_7"]
  -- Sign bits
  Column["b_msb"]
  Column["c_msb"]
  Column["b_sign_extend"]
  Column["c_sign_extend"]
  -- Operation selectors
  Column["is_mul"]
  Column["is_mulh"]
  Column["is_mulhu"]
  Column["is_mulhsu"]
  -- Control
  Column["is_real"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "MulAir" using "pico_encapsulation" where
  MainSubAir["cols": "MulCols" width := 37]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_mulh + is_mulhu + is_mulhsu (upper-word multiplication ops)
def Valid_MulCols.is_upper
  [Field F]
  (c : Valid_MulCols F) (row rotation : ℕ)
: F :=
  c.is_mulh row rotation +
  c.is_mulhu row rotation +
  c.is_mulhsu row rotation

@[pico_encapsulation]
lemma MulCols.is_upper_def
  [Field F]
  (c : Valid_MulCols F) (row rotation : ℕ)
:
  c.is_mulh row rotation +
  c.is_mulhu row rotation +
  c.is_mulhsu row rotation =
  c.is_upper row rotation
:= rfl

-- ============================================================================
-- Lifted to Air level
-- ============================================================================

@[pico_encapsulation]
lemma MulAir.is_upper_def
  [Field F] [Field ExtF]
  (air : Valid_MulAir F ExtF) (row rotation : ℕ)
:
  air.cols.is_mulh row rotation +
  air.cols.is_mulhu row rotation +
  air.cols.is_mulhsu row rotation =
  air.cols.is_upper row rotation
:= rfl
