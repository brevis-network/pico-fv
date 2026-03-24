import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV32IM.Extraction.Attributes
import PicoFV.RV32IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# BitwiseAir

Lean formalisation of the Pico RISC-V Bitwise chip AIR (AND, OR, XOR).

Rust sources:
- BitwiseValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/bitwise/columns.rs

## Column layout (15 columns total)

| Group              | Columns          | Count |
|--------------------|------------------|-------|
| a (Word)           | a_{0..3}         | 4     |
| b (Word)           | b_{0..3}         | 4     |
| c (Word)           | c_{0..3}         | 4     |
| Operation selectors| is_xor, is_or, is_and | 3  |
-/

-- ============================================================================
-- BitwiseCols (15 columns total)
-- ============================================================================

#define_subair "BitwiseCols" using "pico_encapsulation" where
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
  -- Operation selectors
  Column["is_xor"]
  Column["is_or"]
  Column["is_and"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "BitwiseAir" using "pico_encapsulation" where
  MainSubAir["cols": "BitwiseCols" width := 15]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_xor + is_or + is_and (the "is_real" multiplier)
def Valid_BitwiseCols.is_real
  [Field F]
  (c : Valid_BitwiseCols F) (row rotation : ℕ)
: F :=
  c.is_xor row rotation +
  c.is_or row rotation +
  c.is_and row rotation

@[pico_encapsulation]
lemma BitwiseCols.is_real_def
  [Field F]
  (c : Valid_BitwiseCols F) (row rotation : ℕ)
:
  c.is_xor row rotation +
  c.is_or row rotation +
  c.is_and row rotation =
  c.is_real row rotation
:= rfl

-- ============================================================================
-- Lifted to Air level
-- ============================================================================

@[pico_encapsulation]
lemma BitwiseAir.is_real_def
  [Field F] [Field ExtF]
  (air : Valid_BitwiseAir F ExtF) (row rotation : ℕ)
:
  air.cols.is_xor row rotation +
  air.cols.is_or row rotation +
  air.cols.is_and row rotation =
  air.cols.is_real row rotation
:= rfl
