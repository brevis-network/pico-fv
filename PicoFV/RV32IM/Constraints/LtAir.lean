import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.Extraction.LtAir
import PicoFV.RV32IM.Airs.LtAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace LtAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- ================================================================================================
      -- MSB extraction (constraints 0-1): extract sign bits from b_3 and c_3 via modular inverse of 128.
      -- ================================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.msb_b row 0) - (((air.cols.b_3 row 0) - (air.cols.b_masked row 0)) * 2114060289)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.msb_c row 0) - (((air.cols.c_3 row 0) - (air.cols.c_masked row 0)) * 2114060289)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================================
      -- Binary flags and sign-bit propagation (constraints 2-4): is_sign_bit_same is boolean;
      -- bit_b = msb_b * is_slt, bit_c = msb_c * is_slt (zero for unsigned).
      -- =====================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_sign_bit_same row 0) * ((air.cols.is_sign_bit_same row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.bit_b row 0) - ((air.cols.msb_b row 0) * (air.cols.is_slt row 0))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.bit_c row 0) - ((air.cols.msb_c row 0) * (air.cols.is_slt row 0))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ==============================================================================================
      -- Sign-bit comparison logic (constraints 5-7): constraint 5 forces is_sign_bit_same=0 when signs
      -- differ; constraint 6 ensures consistency; constraint 7 computes result:
      -- a_0 = bit_b*(1-bit_c) + is_sign_bit_same*slt_u.
      -- ==============================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_sign_bit_same row 0) * ((air.cols.bit_b row 0) - (air.cols.bit_c row 0))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)) * (((air.cols.is_sign_bit_same row 0) - 1) * (((air.cols.bit_b row 0) + (air.cols.bit_c row 0)) - 1))) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.a_0 row 0) - (((air.cols.bit_b row 0) * (1 - (air.cols.bit_c row 0))) + ((air.cols.is_sign_bit_same row 0) * (air.cols.slt_u row 0)))) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =================================================================
      -- Result word zero-padding (constraints 8-10): a_1 = a_2 = a_3 = 0.
      -- =================================================================

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.a_1 row 0) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.a_2 row 0) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.a_3 row 0) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =======================================================================================
      -- More binary constraints (constraints 11-15): is_cmp_eq and byte_flags_0..3 are boolean.
      -- =======================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_cmp_eq row 0) * ((air.cols.is_cmp_eq row 0) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.byte_flags_0 row 0) * ((air.cols.byte_flags_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.byte_flags_1 row 0) * ((air.cols.byte_flags_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.byte_flags_2 row 0) * ((air.cols.byte_flags_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.byte_flags_3 row 0) * ((air.cols.byte_flags_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ==================================================================================================
      -- Byte flag structure (constraints 16-17): byte flags form one-hot or all-zero; linked to is_cmp_eq.
      -- ==================================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((((air.cols.byte_flags_0 row 0) + (air.cols.byte_flags_1 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_3 row 0)) * (((((air.cols.byte_flags_0 row 0) + (air.cols.byte_flags_1 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_3 row 0)) - 1)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)) * ((1 - (air.cols.is_cmp_eq row 0)) - ((((air.cols.byte_flags_0 row 0) + (air.cols.byte_flags_1 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_3 row 0)))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ===========================================================================================
      -- Byte-level comparison scan (constraints 18-25): scanning from MSB (byte 3) to LSB (byte 0),
      -- flagging the first differing byte pair. Even constraints enforce equality above the flagged
      -- byte; odd constraints enforce consistency with is_cmp_eq.
      -- ===========================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((0 + (air.cols.byte_flags_3 row 0)) - 1) * ((((air.cols.b_3 row 0) * (air.cols.is_slt_u row 0)) + ((air.cols.b_masked row 0) * (air.cols.is_slt row 0))) - (((air.cols.c_3 row 0) * (air.cols.is_slt_u row 0)) + ((air.cols.c_masked row 0) * (air.cols.is_slt row 0))))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_cmp_eq row 0) * (0 + (air.cols.byte_flags_3 row 0))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((((0 + (air.cols.byte_flags_3 row 0)) + (air.cols.byte_flags_2 row 0)) - 1) * ((air.cols.b_2 row 0) - (air.cols.c_2 row 0))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_cmp_eq row 0) * ((0 + (air.cols.byte_flags_3 row 0)) + (air.cols.byte_flags_2 row 0))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((((0 + (air.cols.byte_flags_3 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_1 row 0)) - 1) * ((air.cols.b_1 row 0) - (air.cols.c_1 row 0))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_cmp_eq row 0) * (((0 + (air.cols.byte_flags_3 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_1 row 0))) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((((((0 + (air.cols.byte_flags_3 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_1 row 0)) + (air.cols.byte_flags_0 row 0)) - 1) * ((air.cols.b_0 row 0) - (air.cols.c_0 row 0))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_cmp_eq row 0) * ((((0 + (air.cols.byte_flags_3 row 0)) + (air.cols.byte_flags_2 row 0)) + (air.cols.byte_flags_1 row 0)) + (air.cols.byte_flags_0 row 0))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ==========================================================================================
      -- Comparison byte assembly (constraints 26-27): select the first differing byte from b and c
      -- using byte_flags, with sign-aware masking for SLT.
      -- ==========================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.cmp_bytes_0 row 0) - ((((0 + ((((air.cols.b_3 row 0) * (air.cols.is_slt_u row 0)) + ((air.cols.b_masked row 0) * (air.cols.is_slt row 0))) * (air.cols.byte_flags_3 row 0))) + ((air.cols.b_2 row 0) * (air.cols.byte_flags_2 row 0))) + ((air.cols.b_1 row 0) * (air.cols.byte_flags_1 row 0))) + ((air.cols.b_0 row 0) * (air.cols.byte_flags_0 row 0)))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.cmp_bytes_1 row 0) - ((((0 + ((((air.cols.c_3 row 0) * (air.cols.is_slt_u row 0)) + ((air.cols.c_masked row 0) * (air.cols.is_slt row 0))) * (air.cols.byte_flags_3 row 0))) + ((air.cols.c_2 row 0) * (air.cols.byte_flags_2 row 0))) + ((air.cols.c_1 row 0) * (air.cols.byte_flags_1 row 0))) + ((air.cols.c_0 row 0) * (air.cols.byte_flags_0 row 0)))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ================================================================================
      -- Final comparison (constraint 28): when not equal, uses multiplicative inverse of
      -- (cmp_bytes_0 - cmp_bytes_1) to determine order.
      -- ================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_cmp_eq row 0) - 1) * (((air.cols.not_eq_inv row 0) * ((air.cols.cmp_bytes_0 row 0) - (air.cols.cmp_bytes_1 row 0))) - ((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ================================================================================================
      -- Selector booleans (constraints 29-31): is_slt, is_slt_u are boolean; is_slt + is_slt_u in {0,1}.
      -- ================================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_slt row 0) * ((air.cols.is_slt row 0) - 1)) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_slt_u row 0) * ((air.cols.is_slt_u row 0) - 1)) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_LtAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)) * (((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)) - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_LtAir F ExtF) (row : ℕ)
      : LtAir.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_LtAir F ExtF) (row : ℕ) : List Prop :=
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
          constraint_31 air row
        ]

    end row_constraints

    /-- All 30 column values of a LtAir row, including `not_eq_inv`. -/
    def row [Field ExtF] (air : Valid_LtAir FKB ExtF) (r : ℕ) : Vector FKB 30 :=
      #v[ air.cols.is_slt r 0, air.cols.is_slt_u r 0,
          air.cols.a_0 r 0, air.cols.a_1 r 0, air.cols.a_2 r 0, air.cols.a_3 r 0,
          air.cols.b_0 r 0, air.cols.b_1 r 0, air.cols.b_2 r 0, air.cols.b_3 r 0,
          air.cols.c_0 r 0, air.cols.c_1 r 0, air.cols.c_2 r 0, air.cols.c_3 r 0,
          air.cols.byte_flags_0 r 0, air.cols.byte_flags_1 r 0,
          air.cols.byte_flags_2 r 0, air.cols.byte_flags_3 r 0,
          air.cols.b_masked r 0, air.cols.c_masked r 0,
          air.cols.bit_b r 0, air.cols.bit_c r 0,
          air.cols.msb_b r 0, air.cols.msb_c r 0,
          air.cols.slt_u r 0, air.cols.is_cmp_eq r 0, air.cols.is_sign_bit_same r 0,
          air.cols.cmp_bytes_0 r 0, air.cols.cmp_bytes_1 r 0,
          -- Non-deterministic: free when operands are equal (is_cmp_eq = 1)
          air.cols.not_eq_inv r 0 ]

    section row_buses

      -- ===================================================================================
      -- Bus interactions: 3 ByteBus entries (MSB decomposition for b and c, comparison byte
      -- validation) + 1 ALU entry (opcode 8 for SLT, 9 for SLTU).
      -- ===================================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_LtAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(-(((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0))), [4, 0, (air.cols.b_masked row 0), 0, (air.cols.b_3 row 0), 127]),
        (-(((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0))), [4, 0, (air.cols.c_masked row 0), 0, (air.cols.c_3 row 0), 127]),
        (-(((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0))), [4, 5, (air.cols.slt_u row 0), 0, (air.cols.cmp_bytes_0 row 0), (air.cols.cmp_bytes_1 row 0)]),
        (((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)), [3, (((air.cols.is_slt row 0) * 8) + ((air.cols.is_slt_u row 0) * 9)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_LtAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_LtAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_LtAir FKB ExtF)
      (row : ℕ)
    :
      LtAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        LtAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold LtAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end LtAir.ConstraintsAndBuses

namespace LtAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_LtAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0)), #v[(((air.cols.is_slt row 0) * 8) + ((air.cols.is_slt_u row 0) * 9)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-(((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0))), #v[0, (air.cols.b_masked row 0), 0, (air.cols.b_3 row 0), 127]),
        (-(((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0))), #v[0, (air.cols.c_masked row 0), 0, (air.cols.c_3 row 0), 127]),
        (-(((air.cols.is_slt row 0) + (air.cols.is_slt_u row 0))), #v[5, (air.cols.slt_u row 0), 0, (air.cols.cmp_bytes_0 row 0), (air.cols.cmp_bytes_1 row 0)])
      ],
      State := [],
      Memory := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_LtAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (LtAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end LtAir.Interactions

namespace LtAir.Interpretations

  -- =======================================================================
  -- Interpretation lemmas: derive selector properties from raw constraints.
  -- =======================================================================

  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_LtAir FKB ExtF)
    (row : ℕ)
    (h_constraints : LtAir.Extraction.allHold air row)
  :
    (air.cols.is_slt row 0 = 0 ∨ air.cols.is_slt row 0 = 1) ∧
    (air.cols.is_slt_u row 0 = 0 ∨ air.cols.is_slt_u row 0 = 1) ∧
    (air.cols.is_slt row 0 + air.cols.is_slt_u row 0 = 0 ∨
     air.cols.is_slt row 0 + air.cols.is_slt_u row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

end LtAir.Interpretations
