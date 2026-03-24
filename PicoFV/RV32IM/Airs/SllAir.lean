import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV32IM.Extraction.Attributes
import PicoFV.RV32IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# SllAir

Lean formalisation of the Pico RISC-V left-shift chip AIR (SLL).

Rust sources:
- ShiftLeftValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/sll/columns.rs

## Column layout (42 columns total)

| Group              | Columns                      | Count |
|--------------------|------------------------------|-------|
| a (Word)           | a_{0..3}                     | 4     |
| b (Word)           | b_{0..3}                     | 4     |
| c (Word)           | c_{0..3}                     | 4     |
| c_lsb              | c_lsb_{0..7}                 | 8     |
| shift_by_n_bits    | shift_by_n_bits_{0..7}       | 8     |
| bit_shift_multiplier | bit_shift_multiplier       | 1     |
| shift_result       | shift_result_{0..3}          | 4     |
| shift_result_carry | shift_result_carry_{0..3}    | 4     |
| shift_by_n_bytes   | shift_by_n_bytes_{0..3}      | 4     |
| Control            | is_real                      | 1     |
-/

-- ============================================================================
-- SllCols (42 columns total)
-- ============================================================================

#define_subair "SllCols" using "pico_encapsulation" where
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
  -- c_lsb[8] (least significant byte decomposition)
  Column["c_lsb_0"]
  Column["c_lsb_1"]
  Column["c_lsb_2"]
  Column["c_lsb_3"]
  Column["c_lsb_4"]
  Column["c_lsb_5"]
  Column["c_lsb_6"]
  Column["c_lsb_7"]
  -- shift_by_n_bits[8]
  Column["shift_by_n_bits_0"]
  Column["shift_by_n_bits_1"]
  Column["shift_by_n_bits_2"]
  Column["shift_by_n_bits_3"]
  Column["shift_by_n_bits_4"]
  Column["shift_by_n_bits_5"]
  Column["shift_by_n_bits_6"]
  Column["shift_by_n_bits_7"]
  -- bit_shift_multiplier
  Column["bit_shift_multiplier"]
  -- shift_result[4]
  Column["shift_result_0"]
  Column["shift_result_1"]
  Column["shift_result_2"]
  Column["shift_result_3"]
  -- shift_result_carry[4]
  Column["shift_result_carry_0"]
  Column["shift_result_carry_1"]
  Column["shift_result_carry_2"]
  Column["shift_result_carry_3"]
  -- shift_by_n_bytes[4]
  Column["shift_by_n_bytes_0"]
  Column["shift_by_n_bytes_1"]
  Column["shift_by_n_bytes_2"]
  Column["shift_by_n_bytes_3"]
  -- Control
  Column["is_real"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "SllAir" using "pico_encapsulation" where
  MainSubAir["cols": "SllCols" width := 42]
