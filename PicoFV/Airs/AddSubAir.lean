import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.Extraction.Attributes
import PicoFV.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# AddSubAir

Lean formalisation of the Pico RISC-V ADD/SUB chip AIR.

Rust sources:
- AddSubValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/add_sub/columns.rs

## Column layout (17 columns total)

| Group                  | Columns              | Count |
|------------------------|----------------------|-------|
| AddGadget              | value_{0..3}, carry_{0..2} | 7 |
| Operand 1 (Word)       | operand_1_{0..3}     | 4     |
| Operand 2 (Word)       | operand_2_{0..3}     | 4     |
| Operation selectors    | is_add, is_sub       | 2     |
-/

-- ============================================================================
-- AddSubCols (17 columns total)
-- ============================================================================

#define_subair "AddSubCols" using "pico_encapsulation" where
  -- AddGadget: value (Word) + carry[3]
  Column["add_value_0"]
  Column["add_value_1"]
  Column["add_value_2"]
  Column["add_value_3"]
  Column["add_carry_0"]
  Column["add_carry_1"]
  Column["add_carry_2"]
  -- operand_1 (Word)
  Column["operand_1_0"]
  Column["operand_1_1"]
  Column["operand_1_2"]
  Column["operand_1_3"]
  -- operand_2 (Word)
  Column["operand_2_0"]
  Column["operand_2_1"]
  Column["operand_2_2"]
  Column["operand_2_3"]
  -- Operation selectors
  Column["is_add"]
  Column["is_sub"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "AddSubAir" using "pico_encapsulation" where
  MainSubAir["cols": "AddSubCols" width := 17]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_add + is_sub (used as the "is_real" multiplier in constraints)
def Valid_AddSubCols.is_add_or_sub
  [Field F]
  (c : Valid_AddSubCols F) (row rotation : ℕ)
: F :=
  c.is_add row rotation +
  c.is_sub row rotation

@[pico_encapsulation]
lemma AddSubCols.is_add_or_sub_def
  [Field F]
  (c : Valid_AddSubCols F) (row rotation : ℕ)
:
  c.is_add row rotation +
  c.is_sub row rotation =
  c.is_add_or_sub row rotation
:= rfl

-- ============================================================================
-- Lifted to Air level
-- ============================================================================

@[pico_encapsulation]
lemma AddSubAir.is_add_or_sub_def
  [Field F] [Field ExtF]
  (air : Valid_AddSubAir F ExtF) (row rotation : ℕ)
:
  air.cols.is_add row rotation +
  air.cols.is_sub row rotation =
  air.cols.is_add_or_sub row rotation
:= rfl
