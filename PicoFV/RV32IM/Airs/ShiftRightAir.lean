import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV32IM.Extraction.Attributes
import PicoFV.RV32IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# ShiftRightAir

Lean formalisation of the Pico RISC-V right-shift chip AIR (SRL, SRA).

Rust sources:
- ShiftRightValueCols struct:
  https://github.com/brevis-network/pico/blob/3b074f0bce60835e650566b089c0295fd278a2dc/vm/src/chips/chips/alu/sr/columns.rs

## Column layout (68 columns total)

| Group                       | Columns                            | Count |
|-----------------------------|------------------------------------|-------|
| a (Word)                    | a_{0..3}                           | 4     |
| b (Word)                    | b_{0..3}                           | 4     |
| c (Word)                    | c_{0..3}                           | 4     |
| shift_by_n_bits             | shift_by_n_bits_{0..7}             | 8     |
| shift_by_n_bytes            | shift_by_n_bytes_{0..3}            | 4     |
| byte_shift_result           | byte_shift_result_{0..7}           | 8     |
| bit_shift_result            | bit_shift_result_{0..7}            | 8     |
| shr_carry_output_carry      | shr_carry_output_carry_{0..7}      | 8     |
| shr_carry_output_shifted_byte | shr_carry_output_shifted_byte_{0..7} | 8 |
| b_msb                       | b_msb                              | 1     |
| c_least_sig_byte            | c_least_sig_byte_{0..7}            | 8     |
| Operation selectors         | is_srl, is_sra                     | 2     |
| Control                     | is_real                            | 1     |
-/

-- ============================================================================
-- ShiftRightCols (68 columns total)
-- ============================================================================

#define_subair "ShiftRightCols" using "pico_encapsulation" where
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
  -- shift_by_n_bits[8]
  Column["shift_by_n_bits_0"]
  Column["shift_by_n_bits_1"]
  Column["shift_by_n_bits_2"]
  Column["shift_by_n_bits_3"]
  Column["shift_by_n_bits_4"]
  Column["shift_by_n_bits_5"]
  Column["shift_by_n_bits_6"]
  Column["shift_by_n_bits_7"]
  -- shift_by_n_bytes[4]
  Column["shift_by_n_bytes_0"]
  Column["shift_by_n_bytes_1"]
  Column["shift_by_n_bytes_2"]
  Column["shift_by_n_bytes_3"]
  -- byte_shift_result[8]
  Column["byte_shift_result_0"]
  Column["byte_shift_result_1"]
  Column["byte_shift_result_2"]
  Column["byte_shift_result_3"]
  Column["byte_shift_result_4"]
  Column["byte_shift_result_5"]
  Column["byte_shift_result_6"]
  Column["byte_shift_result_7"]
  -- bit_shift_result[8]
  Column["bit_shift_result_0"]
  Column["bit_shift_result_1"]
  Column["bit_shift_result_2"]
  Column["bit_shift_result_3"]
  Column["bit_shift_result_4"]
  Column["bit_shift_result_5"]
  Column["bit_shift_result_6"]
  Column["bit_shift_result_7"]
  -- shr_carry_output_carry[8]
  Column["shr_carry_output_carry_0"]
  Column["shr_carry_output_carry_1"]
  Column["shr_carry_output_carry_2"]
  Column["shr_carry_output_carry_3"]
  Column["shr_carry_output_carry_4"]
  Column["shr_carry_output_carry_5"]
  Column["shr_carry_output_carry_6"]
  Column["shr_carry_output_carry_7"]
  -- shr_carry_output_shifted_byte[8]
  Column["shr_carry_output_shifted_byte_0"]
  Column["shr_carry_output_shifted_byte_1"]
  Column["shr_carry_output_shifted_byte_2"]
  Column["shr_carry_output_shifted_byte_3"]
  Column["shr_carry_output_shifted_byte_4"]
  Column["shr_carry_output_shifted_byte_5"]
  Column["shr_carry_output_shifted_byte_6"]
  Column["shr_carry_output_shifted_byte_7"]
  -- b_msb
  Column["b_msb"]
  -- c_least_sig_byte[8]
  Column["c_least_sig_byte_0"]
  Column["c_least_sig_byte_1"]
  Column["c_least_sig_byte_2"]
  Column["c_least_sig_byte_3"]
  Column["c_least_sig_byte_4"]
  Column["c_least_sig_byte_5"]
  Column["c_least_sig_byte_6"]
  Column["c_least_sig_byte_7"]
  -- Operation selectors
  Column["is_srl"]
  Column["is_sra"]
  -- Control
  Column["is_real"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "ShiftRightAir" using "pico_encapsulation" where
  MainSubAir["cols": "ShiftRightCols" width := 68]
