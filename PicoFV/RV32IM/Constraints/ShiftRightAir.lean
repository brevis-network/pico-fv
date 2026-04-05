import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.Extraction.ShiftRightAir
import PicoFV.RV32IM.Airs.ShiftRightAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace ShiftRightAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =========================================================================
      -- Byte decomposition (constraint 0): c_least_sig_byte bits reconstruct c_0.
      -- =========================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((((((((0 + (1 * (air.cols.c_least_sig_byte_0 row 0))) + (2 * (air.cols.c_least_sig_byte_1 row 0))) + (4 * (air.cols.c_least_sig_byte_2 row 0))) + (8 * (air.cols.c_least_sig_byte_3 row 0))) + (16 * (air.cols.c_least_sig_byte_4 row 0))) + (32 * (air.cols.c_least_sig_byte_5 row 0))) + (64 * (air.cols.c_least_sig_byte_6 row 0))) + (128 * (air.cols.c_least_sig_byte_7 row 0))) - (air.cols.c_0 row 0)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =========================================================================================
      -- Bit-shift selectors (constraints 1-8): shift_by_n_bits_i active when bits [2:0] of c = i.
      -- Constraint 9: sum = 1.
      -- =========================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_0 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 0)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_1 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_2 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 2)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_3 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 3)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_4 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 4)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_5 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 5)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_6 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 6)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_7 row 0) * ((((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4)) - 7)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((((((((0 + (air.cols.shift_by_n_bits_0 row 0)) + (air.cols.shift_by_n_bits_1 row 0)) + (air.cols.shift_by_n_bits_2 row 0)) + (air.cols.shift_by_n_bits_3 row 0)) + (air.cols.shift_by_n_bits_4 row 0)) + (air.cols.shift_by_n_bits_5 row 0)) + (air.cols.shift_by_n_bits_6 row 0)) + (air.cols.shift_by_n_bits_7 row 0)) - 1) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =============================================================================================
      -- Byte-shift selectors (constraints 10-13): shift_by_n_bytes_j active when bits [4:3] of c = j.
      -- Constraint 14: sum = 1.
      -- =============================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * (((air.cols.c_least_sig_byte_3 row 0) + ((air.cols.c_least_sig_byte_4 row 0) * 2)) - 0)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * (((air.cols.c_least_sig_byte_3 row 0) + ((air.cols.c_least_sig_byte_4 row 0) * 2)) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * (((air.cols.c_least_sig_byte_3 row 0) + ((air.cols.c_least_sig_byte_4 row 0) * 2)) - 2)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * (((air.cols.c_least_sig_byte_3 row 0) + ((air.cols.c_least_sig_byte_4 row 0) * 2)) - 3)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((((0 + (air.cols.shift_by_n_bytes_0 row 0)) + (air.cols.shift_by_n_bytes_1 row 0)) + (air.cols.shift_by_n_bytes_2 row 0)) + (air.cols.shift_by_n_bytes_3 row 0)) - 1) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ======================================================================================
      -- Byte shift routing (constraints 15-40): routes b bytes into byte_shift_result based on
      -- byte shift amount. SRA sign-extends with b_msb*255; SRL uses 0.
      -- ======================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_0 row 0) - (air.cols.b_0 row 0))) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_1 row 0) - (air.cols.b_1 row 0))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_2 row 0) - (air.cols.b_2 row 0))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_3 row 0) - (air.cols.b_3 row 0))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_4 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_5 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_6 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.byte_shift_result_7 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_0 row 0) - (air.cols.b_1 row 0))) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_1 row 0) - (air.cols.b_2 row 0))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_2 row 0) - (air.cols.b_3 row 0))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_3 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_4 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_5 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.byte_shift_result_6 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.byte_shift_result_0 row 0) - (air.cols.b_2 row 0))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.byte_shift_result_1 row 0) - (air.cols.b_3 row 0))) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.byte_shift_result_2 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.byte_shift_result_3 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.byte_shift_result_4 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.byte_shift_result_5 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.byte_shift_result_0 row 0) - (air.cols.b_3 row 0))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.byte_shift_result_1 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.byte_shift_result_2 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.byte_shift_result_3 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.byte_shift_result_4 row 0) - (((air.cols.is_sra row 0) * (air.cols.b_msb row 0)) * 255))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ===================================================================================
      -- Bit shift carry chain (constraints 41-48): propagates bit-level right shift through
      -- byte_shift_result, producing bit_shift_result and carries.
      -- ===================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shr_carry_output_shifted_byte_7 row 0) - (air.cols.bit_shift_result_7 row 0)) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_6 row 0) + ((air.cols.shr_carry_output_carry_7 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_6 row 0)) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_5 row 0) + ((air.cols.shr_carry_output_carry_6 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_5 row 0)) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_4 row 0) + ((air.cols.shr_carry_output_carry_5 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_4 row 0)) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_3 row 0) + ((air.cols.shr_carry_output_carry_4 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_3 row 0)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_2 row 0) + ((air.cols.shr_carry_output_carry_3 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_2 row 0)) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_1 row 0) + ((air.cols.shr_carry_output_carry_2 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_1 row 0)) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.shr_carry_output_shifted_byte_0 row 0) + ((air.cols.shr_carry_output_carry_1 row 0) * ((((((((0 + (256 * (air.cols.shift_by_n_bits_0 row 0))) + (128 * (air.cols.shift_by_n_bits_1 row 0))) + (64 * (air.cols.shift_by_n_bits_2 row 0))) + (32 * (air.cols.shift_by_n_bits_3 row 0))) + (16 * (air.cols.shift_by_n_bits_4 row 0))) + (8 * (air.cols.shift_by_n_bits_5 row 0))) + (4 * (air.cols.shift_by_n_bits_6 row 0))) + (2 * (air.cols.shift_by_n_bits_7 row 0))))) - (air.cols.bit_shift_result_0 row 0)) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ============================================================
      -- Result output (constraints 49-52): a_i = bit_shift_result_i.
      -- ============================================================

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.a_0 row 0) - (air.cols.bit_shift_result_0 row 0)) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.a_1 row 0) - (air.cols.bit_shift_result_1 row 0)) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.a_2 row 0) - (air.cols.bit_shift_result_2 row 0)) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.a_3 row 0) - (air.cols.bit_shift_result_3 row 0)) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ===================================================================
      -- Binary constraints (constraints 53-80): selectors, flags, bits, and
      -- is_srl + is_sra = is_real (constraint 80).
      -- ===================================================================

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_srl row 0) * ((air.cols.is_srl row 0) - 1)) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_sra row 0) * ((air.cols.is_sra row 0) - 1)) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_msb row 0) * ((air.cols.b_msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.shift_by_n_bytes_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.shift_by_n_bytes_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.shift_by_n_bytes_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.shift_by_n_bytes_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_0 row 0) * ((air.cols.shift_by_n_bits_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_1 row 0) * ((air.cols.shift_by_n_bits_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_2 row 0) * ((air.cols.shift_by_n_bits_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_3 row 0) * ((air.cols.shift_by_n_bits_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_64_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_64 air row ↔ constraint_64 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_65 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_4 row 0) * ((air.cols.shift_by_n_bits_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_65_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_65 air row ↔ constraint_65 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_66 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_5 row 0) * ((air.cols.shift_by_n_bits_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_66_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_66 air row ↔ constraint_66 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_67 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_6 row 0) * ((air.cols.shift_by_n_bits_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_67_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_67 air row ↔ constraint_67 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_68 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_7 row 0) * ((air.cols.shift_by_n_bits_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_68_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_68 air row ↔ constraint_68 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_69 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_0 row 0) * ((air.cols.c_least_sig_byte_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_69_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_69 air row ↔ constraint_69 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_70 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_1 row 0) * ((air.cols.c_least_sig_byte_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_70_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_70 air row ↔ constraint_70 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_71 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_2 row 0) * ((air.cols.c_least_sig_byte_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_71_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_71 air row ↔ constraint_71 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_72 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_3 row 0) * ((air.cols.c_least_sig_byte_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_72_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_72 air row ↔ constraint_72 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_73 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_4 row 0) * ((air.cols.c_least_sig_byte_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_73_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_73 air row ↔ constraint_73 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_74 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_5 row 0) * ((air.cols.c_least_sig_byte_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_74_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_74 air row ↔ constraint_74 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_75 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_6 row 0) * ((air.cols.c_least_sig_byte_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_75_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_75 air row ↔ constraint_75 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_76 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_least_sig_byte_7 row 0) * ((air.cols.c_least_sig_byte_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_76_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_76 air row ↔ constraint_76 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_77 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_srl row 0) * ((air.cols.is_srl row 0) - 1)) = 0

      @[simp]
      lemma constraint_77_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_77 air row ↔ constraint_77 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_78 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_sra row 0) * ((air.cols.is_sra row 0) - 1)) = 0

      @[simp]
      lemma constraint_78_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_78 air row ↔ constraint_78 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_79 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_79_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_79 air row ↔ constraint_79 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_80 (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_srl row 0) + (air.cols.is_sra row 0)) - (air.cols.is_real row 0)) = 0

      @[simp]
      lemma constraint_80_equiv (air : Valid_ShiftRightAir F ExtF) (row : ℕ)
      : ShiftRightAir.Extraction.constraint_80 air row ↔ constraint_80 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_ShiftRightAir F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row,
          constraint_5 air row,
          constraint_6 air row,
          constraint_7 air row,
          constraint_8 air row,
          constraint_9 air row,
          constraint_10 air row,
          constraint_11 air row,
          constraint_12 air row,
          constraint_13 air row,
          constraint_14 air row,
          constraint_15 air row,
          constraint_16 air row,
          constraint_17 air row,
          constraint_18 air row,
          constraint_19 air row,
          constraint_20 air row,
          constraint_21 air row,
          constraint_22 air row,
          constraint_23 air row,
          constraint_24 air row,
          constraint_25 air row,
          constraint_26 air row,
          constraint_27 air row,
          constraint_28 air row,
          constraint_29 air row,
          constraint_30 air row,
          constraint_31 air row,
          constraint_32 air row,
          constraint_33 air row,
          constraint_34 air row,
          constraint_35 air row,
          constraint_36 air row,
          constraint_37 air row,
          constraint_38 air row,
          constraint_39 air row,
          constraint_40 air row,
          constraint_41 air row,
          constraint_42 air row,
          constraint_43 air row,
          constraint_44 air row,
          constraint_45 air row,
          constraint_46 air row,
          constraint_47 air row,
          constraint_48 air row,
          constraint_49 air row,
          constraint_50 air row,
          constraint_51 air row,
          constraint_52 air row,
          constraint_53 air row,
          constraint_54 air row,
          constraint_55 air row,
          constraint_56 air row,
          constraint_57 air row,
          constraint_58 air row,
          constraint_59 air row,
          constraint_60 air row,
          constraint_61 air row,
          constraint_62 air row,
          constraint_63 air row,
          constraint_64 air row,
          constraint_65 air row,
          constraint_66 air row,
          constraint_67 air row,
          constraint_68 air row,
          constraint_69 air row,
          constraint_70 air row,
          constraint_71 air row,
          constraint_72 air row,
          constraint_73 air row,
          constraint_74 air row,
          constraint_75 air row,
          constraint_76 air row,
          constraint_77 air row,
          constraint_78 air row,
          constraint_79 air row,
          constraint_80 air row
        ]

    end row_constraints

    /-- All 68 column values of a ShiftRightAir row. No non-deterministic columns. -/
    def row [Field ExtF] (air : Valid_ShiftRightAir FKB ExtF) (r : ℕ) : Vector FKB 68 :=
      #v[ air.cols.a_0 r 0, air.cols.a_1 r 0, air.cols.a_2 r 0, air.cols.a_3 r 0,
          air.cols.b_0 r 0, air.cols.b_1 r 0, air.cols.b_2 r 0, air.cols.b_3 r 0,
          air.cols.c_0 r 0, air.cols.c_1 r 0, air.cols.c_2 r 0, air.cols.c_3 r 0,
          air.cols.shift_by_n_bits_0 r 0, air.cols.shift_by_n_bits_1 r 0,
          air.cols.shift_by_n_bits_2 r 0, air.cols.shift_by_n_bits_3 r 0,
          air.cols.shift_by_n_bits_4 r 0, air.cols.shift_by_n_bits_5 r 0,
          air.cols.shift_by_n_bits_6 r 0, air.cols.shift_by_n_bits_7 r 0,
          air.cols.shift_by_n_bytes_0 r 0, air.cols.shift_by_n_bytes_1 r 0,
          air.cols.shift_by_n_bytes_2 r 0, air.cols.shift_by_n_bytes_3 r 0,
          air.cols.byte_shift_result_0 r 0, air.cols.byte_shift_result_1 r 0,
          air.cols.byte_shift_result_2 r 0, air.cols.byte_shift_result_3 r 0,
          air.cols.byte_shift_result_4 r 0, air.cols.byte_shift_result_5 r 0,
          air.cols.byte_shift_result_6 r 0, air.cols.byte_shift_result_7 r 0,
          air.cols.bit_shift_result_0 r 0, air.cols.bit_shift_result_1 r 0,
          air.cols.bit_shift_result_2 r 0, air.cols.bit_shift_result_3 r 0,
          air.cols.bit_shift_result_4 r 0, air.cols.bit_shift_result_5 r 0,
          air.cols.bit_shift_result_6 r 0, air.cols.bit_shift_result_7 r 0,
          air.cols.shr_carry_output_carry_0 r 0, air.cols.shr_carry_output_carry_1 r 0,
          air.cols.shr_carry_output_carry_2 r 0, air.cols.shr_carry_output_carry_3 r 0,
          air.cols.shr_carry_output_carry_4 r 0, air.cols.shr_carry_output_carry_5 r 0,
          air.cols.shr_carry_output_carry_6 r 0, air.cols.shr_carry_output_carry_7 r 0,
          air.cols.shr_carry_output_shifted_byte_0 r 0, air.cols.shr_carry_output_shifted_byte_1 r 0,
          air.cols.shr_carry_output_shifted_byte_2 r 0, air.cols.shr_carry_output_shifted_byte_3 r 0,
          air.cols.shr_carry_output_shifted_byte_4 r 0, air.cols.shr_carry_output_shifted_byte_5 r 0,
          air.cols.shr_carry_output_shifted_byte_6 r 0, air.cols.shr_carry_output_shifted_byte_7 r 0,
          air.cols.b_msb r 0,
          air.cols.c_least_sig_byte_0 r 0, air.cols.c_least_sig_byte_1 r 0,
          air.cols.c_least_sig_byte_2 r 0, air.cols.c_least_sig_byte_3 r 0,
          air.cols.c_least_sig_byte_4 r 0, air.cols.c_least_sig_byte_5 r 0,
          air.cols.c_least_sig_byte_6 r 0, air.cols.c_least_sig_byte_7 r 0,
          air.cols.is_srl r 0, air.cols.is_sra r 0, air.cols.is_real r 0 ]

    section row_buses

      -- ========================================================================
      -- Bus interactions: 1 ByteBus (opcode 6, MSB check) + 8 ByteBus (opcode 4,
      -- per-byte shift validation) + 4 ByteBus (opcode 7, range checks)
      -- + 1 ALU (opcode 6=SRL, 7=SRA).
      -- ========================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_ShiftRightAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(-((air.cols.is_real row 0)), [4, 6, (air.cols.b_msb row 0), 0, (air.cols.b_3 row 0), 0]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_7 row 0), (air.cols.shr_carry_output_carry_7 row 0), (air.cols.byte_shift_result_7 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_6 row 0), (air.cols.shr_carry_output_carry_6 row 0), (air.cols.byte_shift_result_6 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_5 row 0), (air.cols.shr_carry_output_carry_5 row 0), (air.cols.byte_shift_result_5 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_4 row 0), (air.cols.shr_carry_output_carry_4 row 0), (air.cols.byte_shift_result_4 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_3 row 0), (air.cols.shr_carry_output_carry_3 row 0), (air.cols.byte_shift_result_3 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_2 row 0), (air.cols.shr_carry_output_carry_2 row 0), (air.cols.byte_shift_result_2 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_1 row 0), (air.cols.shr_carry_output_carry_1 row 0), (air.cols.byte_shift_result_1 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 4, (air.cols.shr_carry_output_shifted_byte_0 row 0), (air.cols.shr_carry_output_carry_0 row 0), (air.cols.byte_shift_result_0 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.byte_shift_result_0 row 0), (air.cols.byte_shift_result_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.byte_shift_result_2 row 0), (air.cols.byte_shift_result_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.byte_shift_result_4 row 0), (air.cols.byte_shift_result_5 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.byte_shift_result_6 row 0), (air.cols.byte_shift_result_7 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.bit_shift_result_0 row 0), (air.cols.bit_shift_result_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.bit_shift_result_2 row 0), (air.cols.bit_shift_result_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.bit_shift_result_4 row 0), (air.cols.bit_shift_result_5 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.bit_shift_result_6 row 0), (air.cols.bit_shift_result_7 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_carry_0 row 0), (air.cols.shr_carry_output_carry_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_carry_2 row 0), (air.cols.shr_carry_output_carry_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_carry_4 row 0), (air.cols.shr_carry_output_carry_5 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_carry_6 row 0), (air.cols.shr_carry_output_carry_7 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_shifted_byte_0 row 0), (air.cols.shr_carry_output_shifted_byte_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_shifted_byte_2 row 0), (air.cols.shr_carry_output_shifted_byte_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_shifted_byte_4 row 0), (air.cols.shr_carry_output_shifted_byte_5 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shr_carry_output_shifted_byte_6 row 0), (air.cols.shr_carry_output_shifted_byte_7 row 0)]),
        ((air.cols.is_real row 0), [3, (((air.cols.is_srl row 0) * 6) + ((air.cols.is_sra row 0) * 7)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_ShiftRightAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_ShiftRightAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_ShiftRightAir FKB ExtF)
      (row : ℕ)
    :
      ShiftRightAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        ShiftRightAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold ShiftRightAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end ShiftRightAir.ConstraintsAndBuses

namespace ShiftRightAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_ShiftRightAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((air.cols.is_real row 0), #v[(((air.cols.is_srl row 0) * 6) + ((air.cols.is_sra row 0) * 7)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-((air.cols.is_real row 0)), #v[6, (air.cols.b_msb row 0), 0, (air.cols.b_3 row 0), 0]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_7 row 0), (air.cols.shr_carry_output_carry_7 row 0), (air.cols.byte_shift_result_7 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_6 row 0), (air.cols.shr_carry_output_carry_6 row 0), (air.cols.byte_shift_result_6 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_5 row 0), (air.cols.shr_carry_output_carry_5 row 0), (air.cols.byte_shift_result_5 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_4 row 0), (air.cols.shr_carry_output_carry_4 row 0), (air.cols.byte_shift_result_4 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_3 row 0), (air.cols.shr_carry_output_carry_3 row 0), (air.cols.byte_shift_result_3 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_2 row 0), (air.cols.shr_carry_output_carry_2 row 0), (air.cols.byte_shift_result_2 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_1 row 0), (air.cols.shr_carry_output_carry_1 row 0), (air.cols.byte_shift_result_1 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[4, (air.cols.shr_carry_output_shifted_byte_0 row 0), (air.cols.shr_carry_output_carry_0 row 0), (air.cols.byte_shift_result_0 row 0), (((0 + ((air.cols.c_least_sig_byte_0 row 0) * 1)) + ((air.cols.c_least_sig_byte_1 row 0) * 2)) + ((air.cols.c_least_sig_byte_2 row 0) * 4))]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.byte_shift_result_0 row 0), (air.cols.byte_shift_result_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.byte_shift_result_2 row 0), (air.cols.byte_shift_result_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.byte_shift_result_4 row 0), (air.cols.byte_shift_result_5 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.byte_shift_result_6 row 0), (air.cols.byte_shift_result_7 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.bit_shift_result_0 row 0), (air.cols.bit_shift_result_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.bit_shift_result_2 row 0), (air.cols.bit_shift_result_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.bit_shift_result_4 row 0), (air.cols.bit_shift_result_5 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.bit_shift_result_6 row 0), (air.cols.bit_shift_result_7 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_carry_0 row 0), (air.cols.shr_carry_output_carry_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_carry_2 row 0), (air.cols.shr_carry_output_carry_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_carry_4 row 0), (air.cols.shr_carry_output_carry_5 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_carry_6 row 0), (air.cols.shr_carry_output_carry_7 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_shifted_byte_0 row 0), (air.cols.shr_carry_output_shifted_byte_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_shifted_byte_2 row 0), (air.cols.shr_carry_output_shifted_byte_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_shifted_byte_4 row 0), (air.cols.shr_carry_output_shifted_byte_5 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shr_carry_output_shifted_byte_6 row 0), (air.cols.shr_carry_output_shifted_byte_7 row 0)])
      ],
      State := [],
      Memory := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_ShiftRightAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (ShiftRightAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end ShiftRightAir.Interactions

-- ==========================================================
-- Interpretation lemmas: selector breakdown.
-- ==========================================================

namespace ShiftRightAir.Interpretations

  open ShiftRightAir.ConstraintsAndBuses
  open ShiftRightAir.Interactions

  /-- Each selector is binary and their sum is 0 or 1. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_ShiftRightAir FKB ExtF)
    (row : ℕ)
    (h_constraints : ShiftRightAir.Extraction.allHold air row)
  :
    (air.cols.is_srl row 0 = 0 ∨ air.cols.is_srl row 0 = 1) ∧
    (air.cols.is_sra row 0 = 0 ∨ air.cols.is_sra row 0 = 1) ∧
    (air.cols.is_srl row 0 + air.cols.is_sra row 0 = 0 ∨
     air.cols.is_srl row 0 + air.cols.is_sra row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

end ShiftRightAir.Interpretations
