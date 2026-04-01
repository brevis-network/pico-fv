import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.Extraction.DivRemAir
import PicoFV.RV32IM.Airs.DivRemAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace DivRemAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- ====================================================================
      -- Constraints 0-2: Sign flags.
      -- For signed ops (is_div + is_rem = 1): neg = msb.
      -- For unsigned ops: neg = 0 (since msb * 0 = 0).
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.b_msb row 0) * ((air.cols.is_div row 0) + (air.cols.is_rem row 0))) - (air.cols.b_neg row 0)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.rem_msb row 0) * ((air.cols.is_div row 0) + (air.cols.is_rem row 0))) - (air.cols.rem_neg row 0)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.c_msb row 0) * ((air.cols.is_div row 0) + (air.cols.is_rem row 0))) - (air.cols.c_neg row 0)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraint 3: is_real ∈ {0, 1}.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 4-22: IsEqualWordGadget for is_overflow_b.
      -- Checks if b = -2^31 (= [0, 0, 0, 128] as bytes).
      -- 4-11: IsZeroGadget for each byte difference (inverse, result).
      -- 12-13: is_lower_half_zero, is_upper_half_zero from byte results.
      -- 14-22: Binary constraints on gadget results + final result.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_b.is_zero_byte_0.inverse row 0) * ((air.cols.b_0 row 0) - 0))) - (air.cols.is_overflow_b.is_zero_byte_0.result row 0))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_0.result row 0) * ((air.cols.is_overflow_b.is_zero_byte_0.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_0.result row 0) * ((air.cols.b_0 row 0) - 0))) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_b.is_zero_byte_1.inverse row 0) * ((air.cols.b_1 row 0) - 0))) - (air.cols.is_overflow_b.is_zero_byte_1.result row 0))) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_1.result row 0) * ((air.cols.is_overflow_b.is_zero_byte_1.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_1.result row 0) * ((air.cols.b_1 row 0) - 0))) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_b.is_zero_byte_2.inverse row 0) * ((air.cols.b_2 row 0) - 0))) - (air.cols.is_overflow_b.is_zero_byte_2.result row 0))) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_2.result row 0) * ((air.cols.is_overflow_b.is_zero_byte_2.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_2.result row 0) * ((air.cols.b_2 row 0) - 0))) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_b.is_zero_byte_3.inverse row 0) * ((air.cols.b_3 row 0) - 128))) - (air.cols.is_overflow_b.is_zero_byte_3.result row 0))) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_3.result row 0) * ((air.cols.is_overflow_b.is_zero_byte_3.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_zero_byte_3.result row 0) * ((air.cols.b_3 row 0) - 128))) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_lower_half_zero row 0) * ((air.cols.is_overflow_b.is_lower_half_zero row 0) - 1))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_upper_half_zero row 0) * ((air.cols.is_overflow_b.is_upper_half_zero row 0) - 1))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.result row 0) * ((air.cols.is_overflow_b.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_lower_half_zero row 0) - ((air.cols.is_overflow_b.is_zero_byte_0.result row 0) * (air.cols.is_overflow_b.is_zero_byte_1.result row 0)))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.is_upper_half_zero row 0) - ((air.cols.is_overflow_b.is_zero_byte_2.result row 0) * (air.cols.is_overflow_b.is_zero_byte_3.result row 0)))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_b.result row 0) - ((air.cols.is_overflow_b.is_lower_half_zero row 0) * (air.cols.is_overflow_b.is_upper_half_zero row 0)))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 23-42: IsEqualWordGadget for is_overflow_c.
      -- Checks if c = -1 (= [255, 255, 255, 255] as bytes).
      -- Same structure as constraints 4-22 but for c bytes.
      -- Constraint 23 is a duplicate is_real boolean check.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_c.is_zero_byte_0.inverse row 0) * ((air.cols.c_0 row 0) - 255))) - (air.cols.is_overflow_c.is_zero_byte_0.result row 0))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_0.result row 0) * ((air.cols.is_overflow_c.is_zero_byte_0.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_0.result row 0) * ((air.cols.c_0 row 0) - 255))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_c.is_zero_byte_1.inverse row 0) * ((air.cols.c_1 row 0) - 255))) - (air.cols.is_overflow_c.is_zero_byte_1.result row 0))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_1.result row 0) * ((air.cols.is_overflow_c.is_zero_byte_1.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_1.result row 0) * ((air.cols.c_1 row 0) - 255))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_c.is_zero_byte_2.inverse row 0) * ((air.cols.c_2 row 0) - 255))) - (air.cols.is_overflow_c.is_zero_byte_2.result row 0))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_2.result row 0) * ((air.cols.is_overflow_c.is_zero_byte_2.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_2.result row 0) * ((air.cols.c_2 row 0) - 255))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_overflow_c.is_zero_byte_3.inverse row 0) * ((air.cols.c_3 row 0) - 255))) - (air.cols.is_overflow_c.is_zero_byte_3.result row 0))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_3.result row 0) * ((air.cols.is_overflow_c.is_zero_byte_3.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_zero_byte_3.result row 0) * ((air.cols.c_3 row 0) - 255))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_lower_half_zero row 0) * ((air.cols.is_overflow_c.is_lower_half_zero row 0) - 1))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_upper_half_zero row 0) * ((air.cols.is_overflow_c.is_upper_half_zero row 0) - 1))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.result row 0) * ((air.cols.is_overflow_c.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_lower_half_zero row 0) - ((air.cols.is_overflow_c.is_zero_byte_0.result row 0) * (air.cols.is_overflow_c.is_zero_byte_1.result row 0)))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.is_upper_half_zero row 0) - ((air.cols.is_overflow_c.is_zero_byte_2.result row 0) * (air.cols.is_overflow_c.is_zero_byte_3.result row 0)))) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_overflow_c.result row 0) - ((air.cols.is_overflow_c.is_lower_half_zero row 0) * (air.cols.is_overflow_c.is_upper_half_zero row 0)))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraint 43: is_overflow = is_overflow_b * is_overflow_c * is_signed.
      -- Overflow only when b = -2^31 and c = -1 and operation is signed.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_overflow row 0) - (((air.cols.is_overflow_b.result row 0) * (air.cols.is_overflow_c.result row 0)) * ((air.cols.is_div row 0) + (air.cols.is_rem row 0)))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 44-59: Division equation (16 constraints).
      -- Byte-level: b_i = c_times_quotient_i + remainder_i - carry_i*256 + carry_{i-1}.
      -- For i ≥ 4: sign-extended with rem_neg*255 and overflow correction.
      -- Enforces b = c*quotient + remainder at the byte level.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_0 row 0) - (((air.cols.c_times_quotient_0 row 0) + (air.cols.remainder_0 row 0)) - ((air.cols.carry_0 row 0) * 256))) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_1 row 0) - ((((air.cols.c_times_quotient_1 row 0) + (air.cols.remainder_1 row 0)) - ((air.cols.carry_1 row 0) * 256)) + (air.cols.carry_0 row 0))) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_2 row 0) - ((((air.cols.c_times_quotient_2 row 0) + (air.cols.remainder_2 row 0)) - ((air.cols.carry_2 row 0) * 256)) + (air.cols.carry_1 row 0))) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_3 row 0) - ((((air.cols.c_times_quotient_3 row 0) + (air.cols.remainder_3 row 0)) - ((air.cols.carry_3 row 0) * 256)) + (air.cols.carry_2 row 0))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((air.cols.b_neg row 0) * (((((air.cols.c_times_quotient_4 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_4 row 0) * 256)) + (air.cols.carry_3 row 0)) - 255))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((1 - (air.cols.b_neg row 0)) * ((((air.cols.c_times_quotient_4 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_4 row 0) * 256)) + (air.cols.carry_3 row 0)))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_overflow row 0) * ((((air.cols.c_times_quotient_4 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_4 row 0) * 256)) + (air.cols.carry_3 row 0))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((air.cols.b_neg row 0) * (((((air.cols.c_times_quotient_5 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_5 row 0) * 256)) + (air.cols.carry_4 row 0)) - 255))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((1 - (air.cols.b_neg row 0)) * ((((air.cols.c_times_quotient_5 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_5 row 0) * 256)) + (air.cols.carry_4 row 0)))) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_overflow row 0) * ((((air.cols.c_times_quotient_5 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_5 row 0) * 256)) + (air.cols.carry_4 row 0))) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((air.cols.b_neg row 0) * (((((air.cols.c_times_quotient_6 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_6 row 0) * 256)) + (air.cols.carry_5 row 0)) - 255))) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((1 - (air.cols.b_neg row 0)) * ((((air.cols.c_times_quotient_6 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_6 row 0) * 256)) + (air.cols.carry_5 row 0)))) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_overflow row 0) * ((((air.cols.c_times_quotient_6 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_6 row 0) * 256)) + (air.cols.carry_5 row 0))) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((air.cols.b_neg row 0) * (((((air.cols.c_times_quotient_7 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_7 row 0) * 256)) + (air.cols.carry_6 row 0)) - 255))) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_overflow row 0)) * ((1 - (air.cols.b_neg row 0)) * ((((air.cols.c_times_quotient_7 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_7 row 0) * 256)) + (air.cols.carry_6 row 0)))) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_overflow row 0) * ((((air.cols.c_times_quotient_7 row 0) + ((air.cols.rem_neg row 0) * 255)) - ((air.cols.carry_7 row 0) * 256)) + (air.cols.carry_6 row 0))) = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 60-67: Output routing.
      -- DIV/DIVU: a = quotient. REM/REMU: a = remainder.
      -- Even constraints (60,62,64,66) for DIV/DIVU,
      -- odd (61,63,65,67) for REM/REMU.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_divu row 0) + (air.cols.is_div row 0)) * ((air.cols.quotient_0 row 0) - (air.cols.a_0 row 0))) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_remu row 0) + (air.cols.is_rem row 0)) * ((air.cols.remainder_0 row 0) - (air.cols.a_0 row 0))) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_divu row 0) + (air.cols.is_div row 0)) * ((air.cols.quotient_1 row 0) - (air.cols.a_1 row 0))) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_remu row 0) + (air.cols.is_rem row 0)) * ((air.cols.remainder_1 row 0) - (air.cols.a_1 row 0))) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_divu row 0) + (air.cols.is_div row 0)) * ((air.cols.quotient_2 row 0) - (air.cols.a_2 row 0))) = 0

      @[simp]
      lemma constraint_64_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_64 air row ↔ constraint_64 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_65 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_remu row 0) + (air.cols.is_rem row 0)) * ((air.cols.remainder_2 row 0) - (air.cols.a_2 row 0))) = 0

      @[simp]
      lemma constraint_65_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_65 air row ↔ constraint_65 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_66 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_divu row 0) + (air.cols.is_div row 0)) * ((air.cols.quotient_3 row 0) - (air.cols.a_3 row 0))) = 0

      @[simp]
      lemma constraint_66_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_66 air row ↔ constraint_66 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_67 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_remu row 0) + (air.cols.is_rem row 0)) * ((air.cols.remainder_3 row 0) - (air.cols.a_3 row 0))) = 0

      @[simp]
      lemma constraint_67_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_67 air row ↔ constraint_67 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 68-69: Remainder sign constraints.
      -- 68: rem_neg * (b_neg - 1) = 0 (remainder sign ≤ dividend sign).
      -- 69: remainder_sum * (1 - rem_neg) = 0 (zero remainder → non-negative).
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_68 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.rem_neg row 0) * ((air.cols.b_neg row 0) - 1)) = 0

      @[simp]
      lemma constraint_68_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_68 air row ↔ constraint_68 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_69 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((((0 + (air.cols.remainder_0 row 0)) + (air.cols.remainder_1 row 0)) + (air.cols.remainder_2 row 0)) + (air.cols.remainder_3 row 0)) * ((1 - (air.cols.rem_neg row 0)) * (air.cols.b_neg row 0))) = 0

      @[simp]
      lemma constraint_69_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_69 air row ↔ constraint_69 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 70-88: IsZeroWordGadget for is_c_0.
      -- Checks if c = 0 (division by zero detection).
      -- Same IsZeroGadget structure as is_overflow gadgets.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_70 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_c_0.is_zero_byte_0.inverse row 0) * (air.cols.c_0 row 0))) - (air.cols.is_c_0.is_zero_byte_0.result row 0))) = 0

      @[simp]
      lemma constraint_70_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_70 air row ↔ constraint_70 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_71 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_0.result row 0) * ((air.cols.is_c_0.is_zero_byte_0.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_71_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_71 air row ↔ constraint_71 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_72 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_0.result row 0) * (air.cols.c_0 row 0))) = 0

      @[simp]
      lemma constraint_72_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_72 air row ↔ constraint_72 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_73 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_c_0.is_zero_byte_1.inverse row 0) * (air.cols.c_1 row 0))) - (air.cols.is_c_0.is_zero_byte_1.result row 0))) = 0

      @[simp]
      lemma constraint_73_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_73 air row ↔ constraint_73 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_74 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_1.result row 0) * ((air.cols.is_c_0.is_zero_byte_1.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_74_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_74 air row ↔ constraint_74 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_75 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_1.result row 0) * (air.cols.c_1 row 0))) = 0

      @[simp]
      lemma constraint_75_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_75 air row ↔ constraint_75 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_76 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_c_0.is_zero_byte_2.inverse row 0) * (air.cols.c_2 row 0))) - (air.cols.is_c_0.is_zero_byte_2.result row 0))) = 0

      @[simp]
      lemma constraint_76_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_76 air row ↔ constraint_76 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_77 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_2.result row 0) * ((air.cols.is_c_0.is_zero_byte_2.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_77_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_77 air row ↔ constraint_77 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_78 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_2.result row 0) * (air.cols.c_2 row 0))) = 0

      @[simp]
      lemma constraint_78_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_78 air row ↔ constraint_78 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_79 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((1 - ((air.cols.is_c_0.is_zero_byte_3.inverse row 0) * (air.cols.c_3 row 0))) - (air.cols.is_c_0.is_zero_byte_3.result row 0))) = 0

      @[simp]
      lemma constraint_79_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_79 air row ↔ constraint_79 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_80 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_3.result row 0) * ((air.cols.is_c_0.is_zero_byte_3.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_80_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_80 air row ↔ constraint_80 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_81 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_zero_byte_3.result row 0) * (air.cols.c_3 row 0))) = 0

      @[simp]
      lemma constraint_81_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_81 air row ↔ constraint_81 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_82 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_82_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_82 air row ↔ constraint_82 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_83 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_lower_half_zero row 0) * ((air.cols.is_c_0.is_lower_half_zero row 0) - 1))) = 0

      @[simp]
      lemma constraint_83_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_83 air row ↔ constraint_83 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_84 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_upper_half_zero row 0) * ((air.cols.is_c_0.is_upper_half_zero row 0) - 1))) = 0

      @[simp]
      lemma constraint_84_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_84 air row ↔ constraint_84 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_85 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.result row 0) * ((air.cols.is_c_0.result row 0) - 1))) = 0

      @[simp]
      lemma constraint_85_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_85 air row ↔ constraint_85 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_86 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_lower_half_zero row 0) - ((air.cols.is_c_0.is_zero_byte_0.result row 0) * (air.cols.is_c_0.is_zero_byte_1.result row 0)))) = 0

      @[simp]
      lemma constraint_86_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_86 air row ↔ constraint_86 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_87 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.is_upper_half_zero row 0) - ((air.cols.is_c_0.is_zero_byte_2.result row 0) * (air.cols.is_c_0.is_zero_byte_3.result row 0)))) = 0

      @[simp]
      lemma constraint_87_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_87 air row ↔ constraint_87 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_88 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_c_0.result row 0) - ((air.cols.is_c_0.is_lower_half_zero row 0) * (air.cols.is_c_0.is_upper_half_zero row 0)))) = 0

      @[simp]
      lemma constraint_88_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_88 air row ↔ constraint_88 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 89-92: Division-by-zero quotient.
      -- When is_c_0 = 1: quotient = 0xFFFFFFFF.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_89 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_c_0.result row 0) * ((air.cols.quotient_0 row 0) - 255)) = 0

      @[simp]
      lemma constraint_89_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_89 air row ↔ constraint_89 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_90 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_c_0.result row 0) * ((air.cols.quotient_1 row 0) - 255)) = 0

      @[simp]
      lemma constraint_90_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_90 air row ↔ constraint_90 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_91 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_c_0.result row 0) * ((air.cols.quotient_2 row 0) - 255)) = 0

      @[simp]
      lemma constraint_91_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_91 air row ↔ constraint_91 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_92 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_c_0.result row 0) * ((air.cols.quotient_3 row 0) - 255)) = 0

      @[simp]
      lemma constraint_92_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_92 air row ↔ constraint_92 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 93-100: Absolute values.
      -- 93-96: abs_c from c_neg (abs_c = c if c_neg=0, else negated).
      -- 97-100: abs_remainder from rem_neg (same pattern).
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_93 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.c_neg row 0) - 1) * ((air.cols.c_0 row 0) - (air.cols.abs_c_0 row 0))) = 0

      @[simp]
      lemma constraint_93_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_93 air row ↔ constraint_93 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_94 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.rem_neg row 0) - 1) * ((air.cols.remainder_0 row 0) - (air.cols.abs_remainder_0 row 0))) = 0

      @[simp]
      lemma constraint_94_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_94 air row ↔ constraint_94 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_95 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.c_neg row 0) - 1) * ((air.cols.c_1 row 0) - (air.cols.abs_c_1 row 0))) = 0

      @[simp]
      lemma constraint_95_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_95 air row ↔ constraint_95 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_96 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.rem_neg row 0) - 1) * ((air.cols.remainder_1 row 0) - (air.cols.abs_remainder_1 row 0))) = 0

      @[simp]
      lemma constraint_96_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_96 air row ↔ constraint_96 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_97 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.c_neg row 0) - 1) * ((air.cols.c_2 row 0) - (air.cols.abs_c_2 row 0))) = 0

      @[simp]
      lemma constraint_97_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_97 air row ↔ constraint_97 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_98 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.rem_neg row 0) - 1) * ((air.cols.remainder_2 row 0) - (air.cols.abs_remainder_2 row 0))) = 0

      @[simp]
      lemma constraint_98_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_98 air row ↔ constraint_98 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_99 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.c_neg row 0) - 1) * ((air.cols.c_3 row 0) - (air.cols.abs_c_3 row 0))) = 0

      @[simp]
      lemma constraint_99_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_99 air row ↔ constraint_99 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_100 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.rem_neg row 0) - 1) * ((air.cols.remainder_3 row 0) - (air.cols.abs_remainder_3 row 0))) = 0

      @[simp]
      lemma constraint_100_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_100 air row ↔ constraint_100 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 101-104: max_abs_c_or_1.
      -- If c = 0: max_abs_c_or_1 = 1.
      -- If c ≠ 0: max_abs_c_or_1 = abs_c.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_101 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.max_abs_c_or_1_0 row 0) - (((air.cols.is_c_0.result row 0) * 1) + ((1 - (air.cols.is_c_0.result row 0)) * (air.cols.abs_c_0 row 0)))) = 0

      @[simp]
      lemma constraint_101_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_101 air row ↔ constraint_101 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_102 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.max_abs_c_or_1_1 row 0) - ((1 - (air.cols.is_c_0.result row 0)) * (air.cols.abs_c_1 row 0))) = 0

      @[simp]
      lemma constraint_102_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_102 air row ↔ constraint_102 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_103 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.max_abs_c_or_1_2 row 0) - ((1 - (air.cols.is_c_0.result row 0)) * (air.cols.abs_c_2 row 0))) = 0

      @[simp]
      lemma constraint_103_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_103 air row ↔ constraint_103 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_104 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.max_abs_c_or_1_3 row 0) - ((1 - (air.cols.is_c_0.result row 0)) * (air.cols.abs_c_3 row 0))) = 0

      @[simp]
      lemma constraint_104_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_104 air row ↔ constraint_104 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraint 105: remainder_check_multiplicity =
      --   (1 - is_c_0.result) * is_real.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_105 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (((1 - (air.cols.is_c_0.result row 0)) * (air.cols.is_real row 0)) - (air.cols.remainder_check_multiplicity row 0)) = 0

      @[simp]
      lemma constraint_105_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_105 air row ↔ constraint_105 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 106-107: ALU event flags.
      -- abs_c_alu_event = c_neg * is_real.
      -- abs_rem_alu_event = rem_neg * is_real.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_106 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.abs_c_alu_event row 0) - ((air.cols.c_neg row 0) * (air.cols.is_real row 0))) = 0

      @[simp]
      lemma constraint_106_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_106 air row ↔ constraint_106 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_107 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.abs_rem_alu_event row 0) - ((air.cols.rem_neg row 0) * (air.cols.is_real row 0))) = 0

      @[simp]
      lemma constraint_107_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_107 air row ↔ constraint_107 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 108-115: Carry boolean constraints.
      -- carry_i ∈ {0, 1} for i = 0..7.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_108 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_0 row 0) * ((air.cols.carry_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_108_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_108 air row ↔ constraint_108 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_109 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_1 row 0) * ((air.cols.carry_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_109_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_109 air row ↔ constraint_109 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_110 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_2 row 0) * ((air.cols.carry_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_110_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_110 air row ↔ constraint_110 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_111 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_3 row 0) * ((air.cols.carry_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_111_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_111 air row ↔ constraint_111 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_112 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_4 row 0) * ((air.cols.carry_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_112_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_112 air row ↔ constraint_112 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_113 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_5 row 0) * ((air.cols.carry_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_113_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_113 air row ↔ constraint_113 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_114 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_6 row 0) * ((air.cols.carry_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_114_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_114 air row ↔ constraint_114 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_115 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.carry_7 row 0) * ((air.cols.carry_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_115_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_115 air row ↔ constraint_115 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 116-119: Selector boolean constraints.
      -- is_div, is_divu, is_rem, is_remu ∈ {0, 1}.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_116 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_div row 0) * ((air.cols.is_div row 0) - 1)) = 0

      @[simp]
      lemma constraint_116_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_116 air row ↔ constraint_116 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_117 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_divu row 0) * ((air.cols.is_divu row 0) - 1)) = 0

      @[simp]
      lemma constraint_117_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_117 air row ↔ constraint_117 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_118 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_rem row 0) * ((air.cols.is_rem row 0) - 1)) = 0

      @[simp]
      lemma constraint_118_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_118 air row ↔ constraint_118 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_119 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_remu row 0) * ((air.cols.is_remu row 0) - 1)) = 0

      @[simp]
      lemma constraint_119_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_119 air row ↔ constraint_119 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 120-123: MSB and overflow boolean constraints.
      -- is_overflow, b_msb, rem_msb, c_msb ∈ {0, 1}.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_120 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_overflow row 0) * ((air.cols.is_overflow row 0) - 1)) = 0

      @[simp]
      lemma constraint_120_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_120 air row ↔ constraint_120 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_121 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_msb row 0) * ((air.cols.b_msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_121_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_121 air row ↔ constraint_121 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_122 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.rem_msb row 0) * ((air.cols.rem_msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_122_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_122 air row ↔ constraint_122 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_123 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_msb row 0) * ((air.cols.c_msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_123_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_123 air row ↔ constraint_123 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 124-127: Sign and control boolean constraints.
      -- b_neg, rem_neg, c_neg, is_real ∈ {0, 1}.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_124 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.b_neg row 0) * ((air.cols.b_neg row 0) - 1)) = 0

      @[simp]
      lemma constraint_124_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_124 air row ↔ constraint_124 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_125 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.rem_neg row 0) * ((air.cols.rem_neg row 0) - 1)) = 0

      @[simp]
      lemma constraint_125_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_125 air row ↔ constraint_125 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_126 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.c_neg row 0) * ((air.cols.c_neg row 0) - 1)) = 0

      @[simp]
      lemma constraint_126_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_126 air row ↔ constraint_126 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_127 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_127_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_127 air row ↔ constraint_127 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraints 128-129: Event flag boolean constraints.
      -- abs_c_alu_event, abs_rem_alu_event ∈ {0, 1}.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_128 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.abs_c_alu_event row 0) * ((air.cols.abs_c_alu_event row 0) - 1)) = 0

      @[simp]
      lemma constraint_128_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_128 air row ↔ constraint_128 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_129 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.abs_rem_alu_event row 0) * ((air.cols.abs_rem_alu_event row 0) - 1)) = 0

      @[simp]
      lemma constraint_129_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_129 air row ↔ constraint_129 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================
      -- Constraint 130: Selector sum.
      -- is_real * (1 - (is_div + is_divu + is_rem + is_remu)) = 0.
      -- Exactly one selector active when is_real = 1.
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_130 (air : Valid_DivRemAir F ExtF) (row : ℕ) : Prop :=
        (1 - ((((air.cols.is_divu row 0) + (air.cols.is_remu row 0)) + (air.cols.is_div row 0)) + (air.cols.is_rem row 0))) = 0

      @[simp]
      lemma constraint_130_equiv (air : Valid_DivRemAir F ExtF) (row : ℕ)
      : DivRemAir.Extraction.constraint_130 air row ↔ constraint_130 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_DivRemAir F ExtF) (row : ℕ) : List Prop :=
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
          constraint_80 air row,
          constraint_81 air row,
          constraint_82 air row,
          constraint_83 air row,
          constraint_84 air row,
          constraint_85 air row,
          constraint_86 air row,
          constraint_87 air row,
          constraint_88 air row,
          constraint_89 air row,
          constraint_90 air row,
          constraint_91 air row,
          constraint_92 air row,
          constraint_93 air row,
          constraint_94 air row,
          constraint_95 air row,
          constraint_96 air row,
          constraint_97 air row,
          constraint_98 air row,
          constraint_99 air row,
          constraint_100 air row,
          constraint_101 air row,
          constraint_102 air row,
          constraint_103 air row,
          constraint_104 air row,
          constraint_105 air row,
          constraint_106 air row,
          constraint_107 air row,
          constraint_108 air row,
          constraint_109 air row,
          constraint_110 air row,
          constraint_111 air row,
          constraint_112 air row,
          constraint_113 air row,
          constraint_114 air row,
          constraint_115 air row,
          constraint_116 air row,
          constraint_117 air row,
          constraint_118 air row,
          constraint_119 air row,
          constraint_120 air row,
          constraint_121 air row,
          constraint_122 air row,
          constraint_123 air row,
          constraint_124 air row,
          constraint_125 air row,
          constraint_126 air row,
          constraint_127 air row,
          constraint_128 air row,
          constraint_129 air row,
          constraint_130 air row
        ]

    end row_constraints

    section row_buses

      -- ====================================================================
      -- Bus interactions (17 entries per row):
      -- 0-1: ALU entries (mult = -is_real): c_times_quotient low/high,
      --      quotient, c (for MUL verification of c*quotient).
      -- 2: ALU entry (mult = -abs_c_alu_event): abs_c computation.
      -- 3: ALU entry (mult = -abs_rem_alu_event): abs_remainder computation.
      -- 4: ALU entry (mult = -remainder_check_multiplicity):
      --    abs_remainder < max_abs_c_or_1 (LT check).
      -- 5-7: ByteBus opcode 6 (mult = -is_real): MSB checks for b_3, c_3,
      --      remainder_3.
      -- 8-16: ByteBus opcode 7 (mult = -is_real): range checks for
      --       quotient, remainder, c_times_quotient byte pairs.
      -- 17: ALU result (mult = is_real): a, b, c with opcode
      --     (34=DIV, 35=DIVU, 36=REM, 37=REMU).
      -- ====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_DivRemAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(-((air.cols.is_real row 0)), [3, 30, (air.cols.c_times_quotient_0 row 0), (air.cols.c_times_quotient_1 row 0), (air.cols.c_times_quotient_2 row 0), (air.cols.c_times_quotient_3 row 0), (air.cols.quotient_0 row 0), (air.cols.quotient_1 row 0), (air.cols.quotient_2 row 0), (air.cols.quotient_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)]),
        (-((air.cols.is_real row 0)), [3, ((((air.cols.is_div row 0) + (air.cols.is_rem row 0)) * 31) + (((air.cols.is_divu row 0) + (air.cols.is_remu row 0)) * 32)), (air.cols.c_times_quotient_4 row 0), (air.cols.c_times_quotient_5 row 0), (air.cols.c_times_quotient_6 row 0), (air.cols.c_times_quotient_7 row 0), (air.cols.quotient_0 row 0), (air.cols.quotient_1 row 0), (air.cols.quotient_2 row 0), (air.cols.quotient_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)]),
        (-((air.cols.abs_c_alu_event row 0)), [3, 0, 0, 0, 0, 0, (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0), (air.cols.abs_c_0 row 0), (air.cols.abs_c_1 row 0), (air.cols.abs_c_2 row 0), (air.cols.abs_c_3 row 0)]),
        (-((air.cols.abs_rem_alu_event row 0)), [3, 0, 0, 0, 0, 0, (air.cols.remainder_0 row 0), (air.cols.remainder_1 row 0), (air.cols.remainder_2 row 0), (air.cols.remainder_3 row 0), (air.cols.abs_remainder_0 row 0), (air.cols.abs_remainder_1 row 0), (air.cols.abs_remainder_2 row 0), (air.cols.abs_remainder_3 row 0)]),
        (-((air.cols.remainder_check_multiplicity row 0)), [3, 9, 1, 0, 0, 0, (air.cols.abs_remainder_0 row 0), (air.cols.abs_remainder_1 row 0), (air.cols.abs_remainder_2 row 0), (air.cols.abs_remainder_3 row 0), (air.cols.max_abs_c_or_1_0 row 0), (air.cols.max_abs_c_or_1_1 row 0), (air.cols.max_abs_c_or_1_2 row 0), (air.cols.max_abs_c_or_1_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 6, (air.cols.b_msb row 0), 0, (air.cols.b_3 row 0), 0]),
        (-((air.cols.is_real row 0)), [4, 6, (air.cols.c_msb row 0), 0, (air.cols.c_3 row 0), 0]),
        (-((air.cols.is_real row 0)), [4, 6, (air.cols.rem_msb row 0), 0, (air.cols.remainder_3 row 0), 0]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.quotient_0 row 0), (air.cols.quotient_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.quotient_2 row 0), (air.cols.quotient_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.remainder_0 row 0), (air.cols.remainder_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.remainder_2 row 0), (air.cols.remainder_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.c_times_quotient_0 row 0), (air.cols.c_times_quotient_1 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.c_times_quotient_2 row 0), (air.cols.c_times_quotient_3 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.c_times_quotient_4 row 0), (air.cols.c_times_quotient_5 row 0)]),
        (-((air.cols.is_real row 0)), [4, 7, 0, 0, (air.cols.c_times_quotient_6 row 0), (air.cols.c_times_quotient_7 row 0)]),
        ((air.cols.is_real row 0), [3, (((((air.cols.is_divu row 0) * 35) + ((air.cols.is_remu row 0) * 37)) + ((air.cols.is_div row 0) * 34)) + ((air.cols.is_rem row 0) * 36)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_DivRemAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_DivRemAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_DivRemAir FKB ExtF)
      (row : ℕ)
    :
      DivRemAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        DivRemAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold DivRemAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end DivRemAir.ConstraintsAndBuses

-- ==========================================================
-- Structured bus view: typed ALU/Byte/State/Memory entries.
-- ==========================================================

namespace DivRemAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_DivRemAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-((air.cols.is_real row 0)), #v[30, (air.cols.c_times_quotient_0 row 0), (air.cols.c_times_quotient_1 row 0), (air.cols.c_times_quotient_2 row 0), (air.cols.c_times_quotient_3 row 0), (air.cols.quotient_0 row 0), (air.cols.quotient_1 row 0), (air.cols.quotient_2 row 0), (air.cols.quotient_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[((((air.cols.is_div row 0) + (air.cols.is_rem row 0)) * 31) + (((air.cols.is_divu row 0) + (air.cols.is_remu row 0)) * 32)), (air.cols.c_times_quotient_4 row 0), (air.cols.c_times_quotient_5 row 0), (air.cols.c_times_quotient_6 row 0), (air.cols.c_times_quotient_7 row 0), (air.cols.quotient_0 row 0), (air.cols.quotient_1 row 0), (air.cols.quotient_2 row 0), (air.cols.quotient_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)]),
        (-((air.cols.abs_c_alu_event row 0)), #v[0, 0, 0, 0, 0, (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0), (air.cols.abs_c_0 row 0), (air.cols.abs_c_1 row 0), (air.cols.abs_c_2 row 0), (air.cols.abs_c_3 row 0)]),
        (-((air.cols.abs_rem_alu_event row 0)), #v[0, 0, 0, 0, 0, (air.cols.remainder_0 row 0), (air.cols.remainder_1 row 0), (air.cols.remainder_2 row 0), (air.cols.remainder_3 row 0), (air.cols.abs_remainder_0 row 0), (air.cols.abs_remainder_1 row 0), (air.cols.abs_remainder_2 row 0), (air.cols.abs_remainder_3 row 0)]),
        (-((air.cols.remainder_check_multiplicity row 0)), #v[9, 1, 0, 0, 0, (air.cols.abs_remainder_0 row 0), (air.cols.abs_remainder_1 row 0), (air.cols.abs_remainder_2 row 0), (air.cols.abs_remainder_3 row 0), (air.cols.max_abs_c_or_1_0 row 0), (air.cols.max_abs_c_or_1_1 row 0), (air.cols.max_abs_c_or_1_2 row 0), (air.cols.max_abs_c_or_1_3 row 0)]),
        ((air.cols.is_real row 0), #v[(((((air.cols.is_divu row 0) * 35) + ((air.cols.is_remu row 0) * 37)) + ((air.cols.is_div row 0) * 34)) + ((air.cols.is_rem row 0) * 36)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-((air.cols.is_real row 0)), #v[6, (air.cols.b_msb row 0), 0, (air.cols.b_3 row 0), 0]),
        (-((air.cols.is_real row 0)), #v[6, (air.cols.c_msb row 0), 0, (air.cols.c_3 row 0), 0]),
        (-((air.cols.is_real row 0)), #v[6, (air.cols.rem_msb row 0), 0, (air.cols.remainder_3 row 0), 0]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.quotient_0 row 0), (air.cols.quotient_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.quotient_2 row 0), (air.cols.quotient_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.remainder_0 row 0), (air.cols.remainder_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.remainder_2 row 0), (air.cols.remainder_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.c_times_quotient_0 row 0), (air.cols.c_times_quotient_1 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.c_times_quotient_2 row 0), (air.cols.c_times_quotient_3 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.c_times_quotient_4 row 0), (air.cols.c_times_quotient_5 row 0)]),
        (-((air.cols.is_real row 0)), #v[7, 0, 0, (air.cols.c_times_quotient_6 row 0), (air.cols.c_times_quotient_7 row 0)])
      ],
      State := [],
      Memory := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_DivRemAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (DivRemAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end DivRemAir.Interactions

-- ==========================================================
-- Interpretation lemmas: selector breakdown/exclusivity,
-- helpers_signed (sign flags, event flags, is_overflow),
-- helpers_general (is_c_0.result, remainder_check_multiplicity).
-- ==========================================================

namespace DivRemAir.Interpretations

  open RV32IM_Interactions
  open DivRemAir.ConstraintsAndBuses
  open DivRemAir.Interactions

  /-- Each selector is binary and exactly one is active when is_real = 1. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : DivRemAir.Extraction.allHold air row)
  :
    (air.cols.is_div row 0 = 0 ∨ air.cols.is_div row 0 = 1) ∧
    (air.cols.is_divu row 0 = 0 ∨ air.cols.is_divu row 0 = 1) ∧
    (air.cols.is_rem row 0 = 0 ∨ air.cols.is_rem row 0 = 1) ∧
    (air.cols.is_remu row 0 = 0 ∨ air.cols.is_remu row 0 = 1) ∧
    (air.cols.is_div row 0 + air.cols.is_divu row 0 + air.cols.is_rem row 0 + air.cols.is_remu row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero, h_is_real] at h_constraints
    split_ands <;> grind

  /-- If one selector is 1, all others are 0. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : DivRemAir.Extraction.allHold air row)
  :
    (air.cols.is_div row 0 = 1 → air.cols.is_divu row 0 = 0 ∧ air.cols.is_rem row 0 = 0 ∧ air.cols.is_remu row 0 = 0 ) ∧
    (air.cols.is_divu row 0 = 1 → air.cols.is_div row 0 = 0 ∧ air.cols.is_rem row 0 = 0 ∧ air.cols.is_remu row 0 = 0 ) ∧
    (air.cols.is_rem row 0 = 1 → air.cols.is_div row 0 = 0 ∧ air.cols.is_divu row 0 = 0 ∧ air.cols.is_remu row 0 = 0 ) ∧
    (air.cols.is_remu row 0 = 1 → air.cols.is_div row 0 = 0 ∧ air.cols.is_divu row 0 = 0 ∧ air.cols.is_rem row 0 = 0 )
  := by
    have h_selectors := selector_breakdown air row h_is_real h_constraints
    clear *- h_selectors
    grind

  /-- U32 word equality helpers for overflow/zero detection. -/
  lemma U32_nat_eq_0 {x0 x1 x2 x3 : FKB}
    (ub_x0 : x0 < 256) (ub_x1 : x1 < 256) (ub_x2 : x2 < 256) (ub_x3 : x3 < 256)
  :
    (U32.toNat #v[BitVec.ofNat 8 x0, BitVec.ofNat 8 x1, BitVec.ofNat 8 x2, BitVec.ofNat 8 x3] = 0 ↔ x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0)
  := by
    simp [U32.toNat]; omega

  lemma U32_int_eq_0 {x0 x1 x2 x3 : FKB}
    (ub_x0 : x0 < 256) (ub_x1 : x1 < 256) (ub_x2 : x2 < 256) (ub_x3 : x3 < 256)
  :
    (U32.toInt #v[BitVec.ofNat 8 x0, BitVec.ofNat 8 x1, BitVec.ofNat 8 x2, BitVec.ofNat 8 x3] = 0 ↔ x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0)
  := by
    simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, U32.toNat]
    split_ifs <;> omega

  lemma U32_int_eq_minInt {x0 x1 x2 x3 : FKB}
    (ub_x0 : x0 < 256) (ub_x1 : x1 < 256) (ub_x2 : x2 < 256) (ub_x3 : x3 < 256)
  :
    (U32.toInt #v[BitVec.ofNat 8 x0, BitVec.ofNat 8 x1, BitVec.ofNat 8 x2, BitVec.ofNat 8 x3] = -2147483648 ↔ x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 128)
  := by
    simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, U32.toNat]
    split_ifs <;> omega

  lemma U32_int_eq_neg_one {x0 x1 x2 x3 : FKB}
    (ub_x0 : x0 < 256) (ub_x1 : x1 < 256) (ub_x2 : x2 < 256) (ub_x3 : x3 < 256)
  :
    (U32.toInt #v[BitVec.ofNat 8 x0, BitVec.ofNat 8 x1, BitVec.ofNat 8 x2, BitVec.ofNat 8 x3] = -1 ↔ x0 = 255 ∧ x1 = 255 ∧ x2 = 255 ∧ x3 = 255)
  := by
    simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, U32.toNat]
    split_ifs <;> omega

  /-- For signed ops: derives b_neg, rem_neg, c_neg, abs_c_alu_event,
      abs_rem_alu_event as if-expressions on MSB bytes, and is_overflow
      as a conjunction check on b = -2^31 ∧ c = -1. -/
  lemma helpers_signed {ExtF}
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_is_signed : air.cols.is_signed row 0 = 1)
  :
    air.cols.b_neg row 0 = (if (air.cols.b_3 row 0).val < 128 then 0 else 1) ∧
    air.cols.rem_neg row 0 = (if (air.cols.remainder_3 row 0).val < 128 then 0 else 1) ∧
    air.cols.c_neg row 0 = (if (air.cols.c_3 row 0).val < 128 then 0 else 1) ∧
    air.cols.abs_rem_alu_event row 0 = (if (air.cols.remainder_3 row 0).val < 128 then 0 else 1) ∧
    air.cols.abs_c_alu_event row 0 = (if (air.cols.c_3 row 0).val < 128 then 0 else 1) ∧
    air.cols.is_overflow row 0 = (if air.cols.b_0 row 0 = 0 ∧ air.cols.b_1 row 0 = 0 ∧ air.cols.b_2 row 0 = 0 ∧ air.cols.b_3 row 0 = 128 ∧ air.cols.c_0 row 0 = 255 ∧ air.cols.c_1 row 0 = 255 ∧ air.cols.c_2 row 0 = 255 ∧ air.cols.c_3 row 0 = 255 then 1 else 0)
  := by
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ u0, asm_alu, asm_byte, u1, u2 ⟩ := h_wf; clear u0 u1 u2
    simp [bus_row, ByteBus.Spec, h_is_real, and_assoc] at asm_byte
    obtain ⟨ eq_b_msb, u0, u1, eq_c_msb, u2, u3, eq_rem_msb, u4, u5,
             ub_q0, ub_q1, ub_q2, ub_q3, ub_r0, ub_r1, ub_r2, ub_r3,
             rest ⟩ := asm_byte
    clear u0 u1 u2 u3 u4 u5 rest

    have relevant_constraints :
      constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row ∧
      constraint_106 air row ∧ constraint_107 air row
    := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      Fin.lt_def,
      *
    ] at relevant_constraints
    obtain ⟨ eq_b_neg, eq_rem_neg, eq_c_neg, eq_c_alu, eq_rem_alu ⟩ := relevant_constraints
    symm at eq_b_neg eq_rem_neg eq_c_neg
    simp_all
    have relevant_constraints :
      constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row ∧ constraint_8 air row ∧ constraint_9 air row ∧ constraint_10 air row ∧ constraint_11 air row ∧ constraint_12 air row ∧ constraint_13 air row ∧
      constraint_14 air row ∧ constraint_15 air row ∧ constraint_16 air row ∧ constraint_17 air row ∧ constraint_18 air row ∧ constraint_19 air row ∧ constraint_20 air row ∧ constraint_21 air row ∧ constraint_22 air row ∧ constraint_23 air row ∧
      constraint_24 air row ∧ constraint_25 air row ∧ constraint_26 air row ∧ constraint_27 air row ∧ constraint_28 air row ∧ constraint_29 air row ∧ constraint_30 air row ∧ constraint_31 air row ∧ constraint_32 air row ∧ constraint_33 air row ∧
      constraint_34 air row ∧ constraint_35 air row ∧ constraint_36 air row ∧ constraint_37 air row ∧ constraint_38 air row ∧ constraint_39 air row ∧ constraint_40 air row ∧ constraint_41 air row ∧ constraint_42 air row ∧ constraint_43 air row ∧
      constraint_120 air row
    := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      h_is_real,
      h_is_signed
    ] at relevant_constraints
    split_ifs with h_overflow
    . grind
    . by_contra h_no_overflow
      apply h_overflow; clear h_overflow
      simp [h_no_overflow] at relevant_constraints
      clear *- relevant_constraints
      grind

  /-- For all ops: derives is_c_0.result (is c zero?) and
      remainder_check_multiplicity as if-expressions on c bytes. -/
  lemma helpers_general {ExtF}
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : DivRemAir.Extraction.allHold air row)
  :
    air.cols.is_c_0.result row 0 = (if air.cols.c_0 row 0 = 0 ∧ air.cols.c_1 row 0 = 0 ∧ air.cols.c_2 row 0 = 0 ∧ air.cols.c_3 row 0 = 0 then 1 else 0) ∧
    air.cols.remainder_check_multiplicity row 0 = (if air.cols.c_0 row 0 = 0 ∧ air.cols.c_1 row 0 = 0 ∧ air.cols.c_2 row 0 = 0 ∧ air.cols.c_3 row 0 = 0 then 0 else 1)
  := by
    have h_eq_is_c_zero : air.cols.is_c_0.result row 0 = if air.cols.c_0 row 0 = 0 ∧ air.cols.c_1 row 0 = 0 ∧ air.cols.c_2 row 0 = 0 ∧ air.cols.c_3 row 0 = 0 then 1 else 0
    := by
      have relevant_constraints :
        constraint_70 air row ∧ constraint_71 air row ∧ constraint_72 air row ∧ constraint_73 air row ∧
        constraint_74 air row ∧ constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧
        constraint_78 air row ∧ constraint_79 air row ∧ constraint_80 air row ∧ constraint_81 air row ∧
        constraint_83 air row ∧ constraint_84 air row ∧ constraint_85 air row ∧ constraint_86 air row ∧
        constraint_87 air row ∧ constraint_88 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        sub_eq_zero,
        h_is_real
      ] at relevant_constraints
      split_ifs with h_c_zero
      . grind
      . by_contra h_cnz
        apply h_c_zero; clear h_c_zero
        simp [h_cnz] at relevant_constraints
        clear *- relevant_constraints
        grind
    simp [h_eq_is_c_zero]
    have relevant_constraints : constraint_105 air row
    := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      h_is_real,
      h_eq_is_c_zero
    ] at relevant_constraints
    clear *- relevant_constraints; grind

end DivRemAir.Interpretations
