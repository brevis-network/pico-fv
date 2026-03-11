import PicoFV.RVSail.RV32IM.Operations
import PicoFV.Extraction.SllAir
import PicoFV.Airs.SllAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace SllAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        (((((((((0 + (1 * (air.cols.c_lsb_0 row 0))) + (2 * (air.cols.c_lsb_1 row 0))) + (4 * (air.cols.c_lsb_2 row 0))) + (8 * (air.cols.c_lsb_3 row 0))) + (16 * (air.cols.c_lsb_4 row 0))) + (32 * (air.cols.c_lsb_5 row 0))) + (64 * (air.cols.c_lsb_6 row 0))) + (128 * (air.cols.c_lsb_7 row 0))) - (air.cols.c_0 row 0)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_0 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 0)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_1 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_2 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 2)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_3 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 3)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_4 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 4)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_5 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 5)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_6 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 6)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_7 row 0) * ((((0 + ((air.cols.c_lsb_0 row 0) * 1)) + ((air.cols.c_lsb_1 row 0) * 2)) + ((air.cols.c_lsb_2 row 0) * 4)) - 7)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_0 row 0) * ((air.cols.bit_shift_multiplier row 0) - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_1 row 0) * ((air.cols.bit_shift_multiplier row 0) - 2)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_2 row 0) * ((air.cols.bit_shift_multiplier row 0) - 4)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_3 row 0) * ((air.cols.bit_shift_multiplier row 0) - 8)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_4 row 0) * ((air.cols.bit_shift_multiplier row 0) - 16)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_5 row 0) * ((air.cols.bit_shift_multiplier row 0) - 32)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_6 row 0) * ((air.cols.bit_shift_multiplier row 0) - 64)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_7 row 0) * ((air.cols.bit_shift_multiplier row 0) - 128)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_result_0 row 0) - (((air.cols.b_0 row 0) * (air.cols.bit_shift_multiplier row 0)) - ((air.cols.shift_result_carry_0 row 0) * 256))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_result_1 row 0) - ((((air.cols.b_1 row 0) * (air.cols.bit_shift_multiplier row 0)) - ((air.cols.shift_result_carry_1 row 0) * 256)) + (air.cols.shift_result_carry_0 row 0))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_result_2 row 0) - ((((air.cols.b_2 row 0) * (air.cols.bit_shift_multiplier row 0)) - ((air.cols.shift_result_carry_2 row 0) * 256)) + (air.cols.shift_result_carry_1 row 0))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_result_3 row 0) - ((((air.cols.b_3 row 0) * (air.cols.bit_shift_multiplier row 0)) - ((air.cols.shift_result_carry_3 row 0) * 256)) + (air.cols.shift_result_carry_2 row 0))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * (((air.cols.c_lsb_3 row 0) + ((air.cols.c_lsb_4 row 0) * 2)) - 0)) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * (((air.cols.c_lsb_3 row 0) + ((air.cols.c_lsb_4 row 0) * 2)) - 1)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * (((air.cols.c_lsb_3 row 0) + ((air.cols.c_lsb_4 row 0) * 2)) - 2)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * (((air.cols.c_lsb_3 row 0) + ((air.cols.c_lsb_4 row 0) * 2)) - 3)) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.a_0 row 0) - (air.cols.shift_result_0 row 0))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.a_1 row 0) - (air.cols.shift_result_1 row 0))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.a_2 row 0) - (air.cols.shift_result_2 row 0))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.a_3 row 0) - (air.cols.shift_result_3 row 0))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.a_0 row 0) - 0)) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.a_1 row 0) - (air.cols.shift_result_0 row 0))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.a_2 row 0) - (air.cols.shift_result_1 row 0))) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.a_3 row 0) - (air.cols.shift_result_2 row 0))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.a_0 row 0) - 0)) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.a_1 row 0) - 0)) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.a_2 row 0) - (air.cols.shift_result_0 row 0))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.a_3 row 0) - (air.cols.shift_result_1 row 0))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.a_0 row 0) - 0)) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.a_1 row 0) - 0)) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.a_2 row 0) - 0)) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.a_3 row 0) - (air.cols.shift_result_0 row 0))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_0 row 0) * ((air.cols.c_lsb_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_1 row 0) * ((air.cols.c_lsb_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_2 row 0) * ((air.cols.c_lsb_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_3 row 0) * ((air.cols.c_lsb_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_4 row 0) * ((air.cols.c_lsb_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_5 row 0) * ((air.cols.c_lsb_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_6 row 0) * ((air.cols.c_lsb_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_lsb_7 row 0) * ((air.cols.c_lsb_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_0 row 0) * ((air.cols.shift_by_n_bits_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_1 row 0) * ((air.cols.shift_by_n_bits_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_2 row 0) * ((air.cols.shift_by_n_bits_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_3 row 0) * ((air.cols.shift_by_n_bits_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_4 row 0) * ((air.cols.shift_by_n_bits_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_5 row 0) * ((air.cols.shift_by_n_bits_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_6 row 0) * ((air.cols.shift_by_n_bits_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bits_7 row 0) * ((air.cols.shift_by_n_bits_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        (((((((((0 + (air.cols.shift_by_n_bits_0 row 0)) + (air.cols.shift_by_n_bits_1 row 0)) + (air.cols.shift_by_n_bits_2 row 0)) + (air.cols.shift_by_n_bits_3 row 0)) + (air.cols.shift_by_n_bits_4 row 0)) + (air.cols.shift_by_n_bits_5 row 0)) + (air.cols.shift_by_n_bits_6 row 0)) + (air.cols.shift_by_n_bits_7 row 0)) - 1) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_0 row 0) * ((air.cols.shift_by_n_bytes_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_1 row 0) * ((air.cols.shift_by_n_bytes_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_2 row 0) * ((air.cols.shift_by_n_bytes_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.shift_by_n_bytes_3 row 0) * ((air.cols.shift_by_n_bytes_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        (((((0 + (air.cols.shift_by_n_bytes_0 row 0)) + (air.cols.shift_by_n_bytes_1 row 0)) + (air.cols.shift_by_n_bytes_2 row 0)) + (air.cols.shift_by_n_bytes_3 row 0)) - 1) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_SllAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_SllAir F ExtF) (row : ℕ)
      : SllAir.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_SllAir F ExtF) (row : ℕ) : List Prop :=
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
          constraint_63 air row
        ]

    end row_constraints

    section row_buses

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_SllAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shift_result_0 row 0), (air.cols.shift_result_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shift_result_2 row 0), (air.cols.shift_result_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shift_result_carry_0 row 0), (air.cols.shift_result_carry_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.shift_result_carry_2 row 0), (air.cols.shift_result_carry_3 row 0)]),
        ((air.cols.is_real row 0), [3, 5, (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_SllAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_SllAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_SllAir FKB ExtF)
      (row : ℕ)
    :
      SllAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        SllAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold SllAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end SllAir.ConstraintsAndBuses

namespace SllAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_SllAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((air.cols.is_real row 0), #v[5, (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shift_result_0 row 0), (air.cols.shift_result_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shift_result_2 row 0), (air.cols.shift_result_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shift_result_carry_0 row 0), (air.cols.shift_result_carry_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.shift_result_carry_2 row 0), (air.cols.shift_result_carry_3 row 0)])
      ],
      State := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_SllAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (SllAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end SllAir.Interactions
