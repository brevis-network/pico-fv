import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.Extraction.Attributes
import PicoFV.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# DivRemAir

Lean formalisation of the Pico RISC-V division/remainder chip AIR (DIV, DIVU, REM, REMU).

Rust sources:
- DivRemValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/divrem/columns.rs

## Nested types

- IsZeroGadget = (inverse, result) = 2 columns
- IsZeroWordGadget = is_zero_byte (4 * IsZeroGadget) + is_lower_half_zero +
                     is_upper_half_zero + result = 11 columns
- IsEqualWordGadget = is_diff_zero (IsZeroWordGadget) = 11 columns

## Column layout (96 columns total)

| Group                  | Columns              | Count |
|------------------------|----------------------|-------|
| a (Word)               | a_{0..3}             | 4     |
| b (Word)               | b_{0..3}             | 4     |
| c (Word)               | c_{0..3}             | 4     |
| quotient (Word)        | quotient_{0..3}      | 4     |
| remainder (Word)       | remainder_{0..3}     | 4     |
| abs_remainder (Word)   | abs_remainder_{0..3} | 4     |
| abs_c (Word)           | abs_c_{0..3}         | 4     |
| max_abs_c_or_1 (Word)  | max_abs_c_or_1_{0..3}| 4     |
| c_times_quotient       | c_times_quotient_{0..7} | 8  |
| carry                  | carry_{0..7}         | 8     |
| is_c_0 (IsZeroWordGadget) | is_c_0_*          | 11    |
| Operation selectors    | is_div, is_divu, is_rem, is_remu | 4 |
| is_overflow             | is_overflow          | 1     |
| is_overflow_b (IsEqualWordGadget) | is_overflow_b_* | 11 |
| is_overflow_c (IsEqualWordGadget) | is_overflow_c_* | 11 |
| Sign/Neg bits          | b_msb, rem_msb, c_msb, b_neg, rem_neg, c_neg | 6 |
| ALU event flags        | abs_c_alu_event, abs_rem_alu_event | 2 |
| Control                | is_real              | 1     |
| Remainder check mult   | remainder_check_multiplicity | 1 |
-/

-- ============================================================================
-- Sub-air definitions
-- ============================================================================

-- Rust: IsZeroGadget (2 columns)
#define_subair "DivRem_IsZeroGadget" using "pico_encapsulation" where
  Column["inverse"]
  Column["result"]

-- Rust: IsZeroWordGadget (11 columns)
-- is_zero_byte: [IsZeroGadget; 4] + is_lower_half_zero + is_upper_half_zero + result
#define_subair "DivRem_IsZeroWordGadget" using "pico_encapsulation" where
  SubAir["is_zero_byte_0": "DivRem_IsZeroGadget" width := 2]
  SubAir["is_zero_byte_1": "DivRem_IsZeroGadget" width := 2]
  SubAir["is_zero_byte_2": "DivRem_IsZeroGadget" width := 2]
  SubAir["is_zero_byte_3": "DivRem_IsZeroGadget" width := 2]
  Column["is_lower_half_zero"]
  Column["is_upper_half_zero"]
  Column["result"]

-- ============================================================================
-- DivRemCols (96 columns total)
-- ============================================================================

#define_subair "DivRemCols" using "pico_encapsulation" where
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
  -- quotient (Word)
  Column["quotient_0"]
  Column["quotient_1"]
  Column["quotient_2"]
  Column["quotient_3"]
  -- remainder (Word)
  Column["remainder_0"]
  Column["remainder_1"]
  Column["remainder_2"]
  Column["remainder_3"]
  -- abs_remainder (Word)
  Column["abs_remainder_0"]
  Column["abs_remainder_1"]
  Column["abs_remainder_2"]
  Column["abs_remainder_3"]
  -- abs_c (Word)
  Column["abs_c_0"]
  Column["abs_c_1"]
  Column["abs_c_2"]
  Column["abs_c_3"]
  -- max_abs_c_or_1 (Word)
  Column["max_abs_c_or_1_0"]
  Column["max_abs_c_or_1_1"]
  Column["max_abs_c_or_1_2"]
  Column["max_abs_c_or_1_3"]
  -- c_times_quotient (LONG_WORD_SIZE = 8)
  Column["c_times_quotient_0"]
  Column["c_times_quotient_1"]
  Column["c_times_quotient_2"]
  Column["c_times_quotient_3"]
  Column["c_times_quotient_4"]
  Column["c_times_quotient_5"]
  Column["c_times_quotient_6"]
  Column["c_times_quotient_7"]
  -- carry (LONG_WORD_SIZE = 8)
  Column["carry_0"]
  Column["carry_1"]
  Column["carry_2"]
  Column["carry_3"]
  Column["carry_4"]
  Column["carry_5"]
  Column["carry_6"]
  Column["carry_7"]
  -- is_c_0 (IsZeroWordGadget = 11)
  SubAir["is_c_0": "DivRem_IsZeroWordGadget" width := 11]
  -- Operation selectors
  Column["is_div"]
  Column["is_divu"]
  Column["is_rem"]
  Column["is_remu"]
  -- is_overflow
  Column["is_overflow"]
  -- is_overflow_b (IsEqualWordGadget = IsZeroWordGadget = 11)
  SubAir["is_overflow_b": "DivRem_IsZeroWordGadget" width := 11]
  -- is_overflow_c (IsEqualWordGadget = IsZeroWordGadget = 11)
  SubAir["is_overflow_c": "DivRem_IsZeroWordGadget" width := 11]
  -- Sign/Neg bits
  Column["b_msb"]
  Column["rem_msb"]
  Column["c_msb"]
  Column["b_neg"]
  Column["rem_neg"]
  Column["c_neg"]
  -- ALU event flags
  Column["abs_c_alu_event"]
  Column["abs_rem_alu_event"]
  -- Control
  Column["is_real"]
  -- Remainder check multiplicity
  Column["remainder_check_multiplicity"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "DivRemAir" using "pico_encapsulation" where
  MainSubAir["cols": "DivRemCols" width := 96]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_div + is_rem (signed operations)
def Valid_DivRemCols.is_signed
  [Field F]
  (c : Valid_DivRemCols F) (row rotation : ℕ)
: F :=
  c.is_div row rotation +
  c.is_rem row rotation

@[pico_encapsulation]
lemma DivRemCols.is_signed_def
  [Field F]
  (c : Valid_DivRemCols F) (row rotation : ℕ)
:
  c.is_div row rotation +
  c.is_rem row rotation =
  c.is_signed row rotation
:= rfl

-- ============================================================================
-- Lifted to Air level
-- ============================================================================

@[pico_encapsulation]
lemma DivRemAir.is_signed_def
  [Field F] [Field ExtF]
  (air : Valid_DivRemAir F ExtF) (row rotation : ℕ)
:
  air.cols.is_div row rotation +
  air.cols.is_rem row rotation =
  air.cols.is_signed row rotation
:= rfl
