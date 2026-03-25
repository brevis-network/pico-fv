import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.Extraction.MemoryReadWriteAir
import PicoFV.RV32IM.Airs.MemoryReadWriteAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace MemoryReadWriteAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================================
      -- Address range validation (constraints 0-9): MSB decomposition bits are boolean (0-7),
      -- weighted sum equals MSB byte (8), upper address byte is zero (9).
      -- =====================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_0 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_0 row 0) - 1))) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_1 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_1 row 0) - 1))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_2 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_2 row 0) - 1))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_3 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_3 row 0) - 1))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_4 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_4 row 0) - 1))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_5 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_5 row 0) - 1))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_6 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_6 row 0) - 1))) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_7 row 0) * ((air.cols.addr_word_range_checker.most_sig_byte_decomp_7 row 0) - 1))) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (((((((((0 + (1 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_0 row 0))) + (2 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_1 row 0))) + (4 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_2 row 0))) + (8 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_3 row 0))) + (16 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_4 row 0))) + (32 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_5 row 0))) + (64 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_6 row 0))) + (128 * (air.cols.addr_word_range_checker.most_sig_byte_decomp_7 row 0))) - (air.cols.addr_word_3 row 0))) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (air.cols.addr_word_range_checker.most_sig_byte_decomp_7 row 0)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ===========================================================================================
      -- Memory access tracking (constraints 10-34): prev_chunk/prev_clk handling, LSB decomposition
      -- for addr%64, offset computation (addr%4 encoded as offset_is_one/two/three), clock and
      -- chunk sequencing.
      -- ===========================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((1 - ((air.cols.addr_word_range_checker.upper_all_one_inverse row 0) * ((((((((0 + (air.cols.addr_word_range_checker.most_sig_byte_decomp_0 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_1 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_2 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_3 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_4 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_5 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_6 row 0)) - 7))) - (air.cols.addr_word_range_checker.upper_all_one_result row 0))) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.upper_all_one_result row 0) * ((air.cols.addr_word_range_checker.upper_all_one_result row 0) - 1))) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.upper_all_one_result row 0) * ((((((((0 + (air.cols.addr_word_range_checker.most_sig_byte_decomp_0 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_1 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_2 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_3 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_4 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_5 row 0)) + (air.cols.addr_word_range_checker.most_sig_byte_decomp_6 row 0)) - 7))) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.upper_all_one_result row 0) * 0)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.addr_word_range_checker.upper_all_one_result row 0) * (((air.cols.addr_word_0 row 0) + (air.cols.addr_word_1 row 0)) + (air.cols.addr_word_2 row 0)))) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_one row 0) * ((air.cols.offset_is_one row 0) - 1))) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_two row 0) * ((air.cols.offset_is_two row 0) - 1))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_three row 0) * ((air.cols.offset_is_three row 0) - 1))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (((((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) + (air.cols.offset_is_one row 0)) + (air.cols.offset_is_two row 0)) + (air.cols.offset_is_three row 0)) - 1)) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) * (air.cols.addr_offset row 0))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_one row 0) * ((air.cols.addr_offset row 0) - 1))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_two row 0) * ((air.cols.addr_offset row 0) - 2))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_three row 0) * ((air.cols.addr_offset row 0) - 3))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (((air.cols.addr_aligned row 0) + (air.cols.addr_offset row 0)) - ((((1 * (air.cols.addr_word_0 row 0)) + (256 * (air.cols.addr_word_1 row 0))) + (65536 * (air.cols.addr_word_2 row 0))) + (16777216 * (air.cols.addr_word_3 row 0))))) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.aa_lsb_decomp_0 row 0) * ((air.cols.aa_lsb_decomp_0 row 0) - 1))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.aa_lsb_decomp_1 row 0) * ((air.cols.aa_lsb_decomp_1 row 0) - 1))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.aa_lsb_decomp_2 row 0) * ((air.cols.aa_lsb_decomp_2 row 0) - 1))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.aa_lsb_decomp_3 row 0) * ((air.cols.aa_lsb_decomp_3 row 0) - 1))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.aa_lsb_decomp_4 row 0) * ((air.cols.aa_lsb_decomp_4 row 0) - 1))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.aa_lsb_decomp_5 row 0) * ((air.cols.aa_lsb_decomp_5 row 0) - 1))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (((air.cols.addr_word_0 row 0) - (((0 + (1 * (air.cols.offset_is_one row 0))) + (2 * (air.cols.offset_is_two row 0))) + (3 * (air.cols.offset_is_three row 0)))) - ((((((0 + (4 * (air.cols.aa_lsb_decomp_0 row 0))) + (8 * (air.cols.aa_lsb_decomp_1 row 0))) + (16 * (air.cols.aa_lsb_decomp_2 row 0))) + (32 * (air.cols.aa_lsb_decomp_3 row 0))) + (64 * (air.cols.aa_lsb_decomp_4 row 0))) + (128 * (air.cols.aa_lsb_decomp_5 row 0))))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.memory_access.access.compare_clk row 0) * ((air.cols.memory_access.access.compare_clk row 0) - 1))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.memory_access.access.compare_clk row 0) * ((air.cols.chunk row 0) - (air.cols.memory_access.access.prev_chunk row 0)))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((((((air.cols.memory_access.access.compare_clk row 0) * ((air.cols.clk row 0) + 0)) + ((1 - (air.cols.memory_access.access.compare_clk row 0)) * (air.cols.chunk row 0))) - (((air.cols.memory_access.access.compare_clk row 0) * (air.cols.memory_access.access.prev_clk row 0)) + ((1 - (air.cols.memory_access.access.compare_clk row 0)) * (air.cols.memory_access.access.prev_chunk row 0)))) - 1) - ((air.cols.memory_access.access.diff_16bit_limb row 0) + ((air.cols.memory_access.access.diff_8bit_limb row 0) * 65536)))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================================
      -- Load instruction constraints (constraints 35-62): constraints 35-38 enforce read-only
      -- (value=prev_value for loads); 39-42 LB/LBU byte extraction by offset; 43-44 alignment
      -- (LH: offset in {0,2}, LW: offset=0); 45-52 LH/LHU and LW value extraction; 53-62 MSB
      -- decomposition for sign extension.
      -- =====================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) * ((air.cols.memory_access.access.value_0 row 0) - (air.cols.memory_access.prev_value_0 row 0))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) * ((air.cols.memory_access.access.value_1 row 0) - (air.cols.memory_access.prev_value_1 row 0))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) * ((air.cols.memory_access.access.value_2 row 0) - (air.cols.memory_access.prev_value_2 row 0))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) * ((air.cols.memory_access.access.value_3 row 0) - (air.cols.memory_access.prev_value_3 row 0))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) * ((0 + (((((air.cols.memory_access.access.value_0 row 0) * (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) + ((air.cols.memory_access.access.value_1 row 0) * (air.cols.offset_is_one row 0))) + ((air.cols.memory_access.access.value_2 row 0) * (air.cols.offset_is_two row 0))) + ((air.cols.memory_access.access.value_3 row 0) * (air.cols.offset_is_three row 0)))) - (air.cols.unsigned_mem_val_0 row 0))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) * (0 - (air.cols.unsigned_mem_val_1 row 0))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) * (0 - (air.cols.unsigned_mem_val_2 row 0))) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) * (0 - (air.cols.unsigned_mem_val_3 row 0))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lh row 0) + (air.cols.instruction.is_lhu row 0)) * ((air.cols.offset_is_one row 0) + (air.cols.offset_is_three row 0))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lw row 0) * ((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) - 1)) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lh row 0) + (air.cols.instruction.is_lhu row 0)) * ((((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) * (air.cols.memory_access.access.value_0 row 0)) + ((air.cols.offset_is_two row 0) * (air.cols.memory_access.access.value_2 row 0))) - (air.cols.unsigned_mem_val_0 row 0))) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lh row 0) + (air.cols.instruction.is_lhu row 0)) * ((((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) * (air.cols.memory_access.access.value_1 row 0)) + ((air.cols.offset_is_two row 0) * (air.cols.memory_access.access.value_3 row 0))) - (air.cols.unsigned_mem_val_1 row 0))) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lh row 0) + (air.cols.instruction.is_lhu row 0)) * (0 - (air.cols.unsigned_mem_val_2 row 0))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.instruction.is_lh row 0) + (air.cols.instruction.is_lhu row 0)) * (0 - (air.cols.unsigned_mem_val_3 row 0))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lw row 0) * ((air.cols.memory_access.access.value_0 row 0) - (air.cols.unsigned_mem_val_0 row 0))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lw row 0) * ((air.cols.memory_access.access.value_1 row 0) - (air.cols.unsigned_mem_val_1 row 0))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lw row 0) * ((air.cols.memory_access.access.value_2 row 0) - (air.cols.unsigned_mem_val_2 row 0))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lw row 0) * ((air.cols.memory_access.access.value_3 row 0) - (air.cols.unsigned_mem_val_3 row 0))) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_0 row 0) * ((air.cols.msb_decomp_0 row 0) - 1))) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_1 row 0) * ((air.cols.msb_decomp_1 row 0) - 1))) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_2 row 0) * ((air.cols.msb_decomp_2 row 0) - 1))) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_3 row 0) * ((air.cols.msb_decomp_3 row 0) - 1))) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_4 row 0) * ((air.cols.msb_decomp_4 row 0) - 1))) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_5 row 0) * ((air.cols.msb_decomp_5 row 0) - 1))) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_6 row 0) * ((air.cols.msb_decomp_6 row 0) - 1))) = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.msb_decomp_7 row 0) * ((air.cols.msb_decomp_7 row 0) - 1))) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lb row 0) * (((((((((0 + ((air.cols.msb_decomp_0 row 0) * 1)) + ((air.cols.msb_decomp_1 row 0) * 2)) + ((air.cols.msb_decomp_2 row 0) * 4)) + ((air.cols.msb_decomp_3 row 0) * 8)) + ((air.cols.msb_decomp_4 row 0) * 16)) + ((air.cols.msb_decomp_5 row 0) * 32)) + ((air.cols.msb_decomp_6 row 0) * 64)) + ((air.cols.msb_decomp_7 row 0) * 128)) - (air.cols.unsigned_mem_val_0 row 0))) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_lh row 0) * (((((((((0 + ((air.cols.msb_decomp_0 row 0) * 1)) + ((air.cols.msb_decomp_1 row 0) * 2)) + ((air.cols.msb_decomp_2 row 0) * 4)) + ((air.cols.msb_decomp_3 row 0) * 8)) + ((air.cols.msb_decomp_4 row 0) * 16)) + ((air.cols.msb_decomp_5 row 0) * 32)) + ((air.cols.msb_decomp_6 row 0) * 64)) + ((air.cols.msb_decomp_7 row 0) * 128)) - (air.cols.unsigned_mem_val_1 row 0))) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ====================================================================================
      -- Sign extension flags (constraints 63-65): op_a_0 binary; mem_value_is_neg_not_x0 and
      -- mem_value_is_pos_not_x0 for signed load sign detection.
      -- ====================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.op_a_0 row 0) * ((air.cols.instruction.op_a_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.mem_value_is_neg_not_x0 row 0) - ((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lh row 0)) * (air.cols.msb_decomp_7 row 0)))) = 0

      -- =========================================================================================
      -- FIXME:
      -- `MemoryReadWriteAir.Extraction.constraint_64 air row` should not be conditional on a_is_0
      -- =========================================================================================

      @[simp]
      lemma constraint_64_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_64 air row ↔ constraint_64 air row
      := by sorry -- simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_65 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.mem_value_is_pos_not_x0 row 0) - (((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lh row 0)) * (1 - (air.cols.msb_decomp_7 row 0))) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)))) = 0

      -- =========================================================================================
      -- FIXME:
      -- `MemoryReadWriteAir.Extraction.constraint_65 air row` should not be conditional on a_is_0
      -- =========================================================================================

      @[simp]
      lemma constraint_65_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_65 air row ↔ constraint_65 air row
      := by sorry -- simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_66 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.mem_value_is_pos_not_x0 row 0) * ((air.cols.unsigned_mem_val_0 row 0) - (air.cols.instruction.op_a_access.access.value_0 row 0))) = 0

      @[simp]
      lemma constraint_66_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_66 air row ↔ constraint_66 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_67 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.mem_value_is_pos_not_x0 row 0) * ((air.cols.unsigned_mem_val_1 row 0) - (air.cols.instruction.op_a_access.access.value_1 row 0))) = 0

      @[simp]
      lemma constraint_67_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_67 air row ↔ constraint_67 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_68 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.mem_value_is_pos_not_x0 row 0) * ((air.cols.unsigned_mem_val_2 row 0) - (air.cols.instruction.op_a_access.access.value_2 row 0))) = 0

      @[simp]
      lemma constraint_68_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_68 air row ↔ constraint_68 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_69 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.mem_value_is_pos_not_x0 row 0) * ((air.cols.unsigned_mem_val_3 row 0) - (air.cols.instruction.op_a_access.access.value_3 row 0))) = 0

      @[simp]
      lemma constraint_69_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_69 air row ↔ constraint_69 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ======================================================================================
      -- Offset validation (constraints 70-77): offset_is_one/two/three are binary, at most one
      -- set, linked to addr_offset value.
      -- ======================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_70 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_one row 0) * ((air.cols.offset_is_one row 0) - 1))) = 0

      @[simp]
      lemma constraint_70_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_70 air row ↔ constraint_70 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_71 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_two row 0) * ((air.cols.offset_is_two row 0) - 1))) = 0

      @[simp]
      lemma constraint_71_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_71 air row ↔ constraint_71 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_72 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_three row 0) * ((air.cols.offset_is_three row 0) - 1))) = 0

      @[simp]
      lemma constraint_72_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_72 air row ↔ constraint_72 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_73 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * (((((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) + (air.cols.offset_is_one row 0)) + (air.cols.offset_is_two row 0)) + (air.cols.offset_is_three row 0)) - 1)) = 0

      @[simp]
      lemma constraint_73_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_73 air row ↔ constraint_73 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_74 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) * (air.cols.addr_offset row 0))) = 0

      @[simp]
      lemma constraint_74_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_74 air row ↔ constraint_74 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_75 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_one row 0) * ((air.cols.addr_offset row 0) - 1))) = 0

      @[simp]
      lemma constraint_75_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_75 air row ↔ constraint_75 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_76 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_two row 0) * ((air.cols.addr_offset row 0) - 2))) = 0

      @[simp]
      lemma constraint_76_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_76 air row ↔ constraint_76 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_77 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)) * ((air.cols.offset_is_three row 0) * ((air.cols.addr_offset row 0) - 3))) = 0

      @[simp]
      lemma constraint_77_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_77 air row ↔ constraint_77 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ===================================================================================
      -- Store instruction constraints (constraints 78-91): SB byte store by offset (78-81);
      -- SH alignment + half-word store (82-87); SW alignment + word store (88-91).
      -- ===================================================================================

      @[constraint_and_interaction_simplification]
      def constraint_78 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sb row 0) * ((air.cols.memory_access.access.value_0 row 0) - (((air.cols.instruction.op_a_access.access.value_0 row 0) * (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) + ((1 - (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) * (air.cols.memory_access.prev_value_0 row 0))))) = 0

      @[simp]
      lemma constraint_78_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_78 air row ↔ constraint_78 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_79 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sb row 0) * ((air.cols.memory_access.access.value_1 row 0) - (((air.cols.instruction.op_a_access.access.value_0 row 0) * (air.cols.offset_is_one row 0)) + ((1 - (air.cols.offset_is_one row 0)) * (air.cols.memory_access.prev_value_1 row 0))))) = 0

      @[simp]
      lemma constraint_79_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_79 air row ↔ constraint_79 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_80 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sb row 0) * ((air.cols.memory_access.access.value_2 row 0) - (((air.cols.instruction.op_a_access.access.value_0 row 0) * (air.cols.offset_is_two row 0)) + ((1 - (air.cols.offset_is_two row 0)) * (air.cols.memory_access.prev_value_2 row 0))))) = 0

      @[simp]
      lemma constraint_80_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_80 air row ↔ constraint_80 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_81 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sb row 0) * ((air.cols.memory_access.access.value_3 row 0) - (((air.cols.instruction.op_a_access.access.value_0 row 0) * (air.cols.offset_is_three row 0)) + ((1 - (air.cols.offset_is_three row 0)) * (air.cols.memory_access.prev_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_81_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_81 air row ↔ constraint_81 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_82 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sh row 0) * ((air.cols.offset_is_one row 0) + (air.cols.offset_is_three row 0))) = 0

      @[simp]
      lemma constraint_82_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_82 air row ↔ constraint_82 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_83 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sw row 0) * ((((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0)) - 1)) = 0

      @[simp]
      lemma constraint_83_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_83 air row ↔ constraint_83 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_84 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sh row 0) * ((air.cols.memory_access.access.value_0 row 0) - (((air.cols.instruction.op_a_access.access.value_0 row 0) * (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) + ((1 - (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) * (air.cols.memory_access.prev_value_0 row 0))))) = 0

      @[simp]
      lemma constraint_84_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_84 air row ↔ constraint_84 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_85 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sh row 0) * ((air.cols.memory_access.access.value_1 row 0) - (((air.cols.instruction.op_a_access.access.value_1 row 0) * (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) + ((1 - (((1 - (air.cols.offset_is_one row 0)) - (air.cols.offset_is_two row 0)) - (air.cols.offset_is_three row 0))) * (air.cols.memory_access.prev_value_1 row 0))))) = 0

      @[simp]
      lemma constraint_85_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_85 air row ↔ constraint_85 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_86 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sh row 0) * ((air.cols.memory_access.access.value_2 row 0) - (((air.cols.instruction.op_a_access.access.value_0 row 0) * (air.cols.offset_is_two row 0)) + ((1 - (air.cols.offset_is_two row 0)) * (air.cols.memory_access.prev_value_2 row 0))))) = 0

      @[simp]
      lemma constraint_86_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_86 air row ↔ constraint_86 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_87 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sh row 0) * ((air.cols.memory_access.access.value_3 row 0) - (((air.cols.instruction.op_a_access.access.value_1 row 0) * (air.cols.offset_is_two row 0)) + ((1 - (air.cols.offset_is_two row 0)) * (air.cols.memory_access.prev_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_87_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_87 air row ↔ constraint_87 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_88 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sw row 0) * ((air.cols.memory_access.access.value_0 row 0) - (air.cols.instruction.op_a_access.access.value_0 row 0))) = 0

      @[simp]
      lemma constraint_88_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_88 air row ↔ constraint_88 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_89 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sw row 0) * ((air.cols.memory_access.access.value_1 row 0) - (air.cols.instruction.op_a_access.access.value_1 row 0))) = 0

      @[simp]
      lemma constraint_89_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_89 air row ↔ constraint_89 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_90 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sw row 0) * ((air.cols.memory_access.access.value_2 row 0) - (air.cols.instruction.op_a_access.access.value_2 row 0))) = 0

      @[simp]
      lemma constraint_90_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_90 air row ↔ constraint_90 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_91 (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.is_sw row 0) * ((air.cols.memory_access.access.value_3 row 0) - (air.cols.instruction.op_a_access.access.value_3 row 0))) = 0

      @[simp]
      lemma constraint_91_equiv (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ)
      : MemoryReadWriteAir.Extraction.constraint_91 air row ↔ constraint_91 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_MemoryReadWriteAir F ExtF) (row : ℕ) : List Prop :=
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
          constraint_91 air row
        ]

    end row_constraints

    section row_buses

      -- =====================================================================================
      -- Bus interactions: program/ALU entry (instruction metadata), ALU address verification,
      -- 2 ByteBus (address byte range), 2 ByteBus (clock diffs), 2 State Bus (before/after
      -- memory state), 1 ALU (sign extension).
      -- =====================================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_MemoryReadWriteAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)), [0, (air.cols.instruction.opcode row 0), (air.cols.instruction.op_a_access.access.value_0 row 0), (air.cols.instruction.op_a_access.access.value_1 row 0), (air.cols.instruction.op_a_access.access.value_2 row 0), (air.cols.instruction.op_a_access.access.value_3 row 0), (air.cols.instruction.op_b_access.value_0 row 0), (air.cols.instruction.op_b_access.value_1 row 0), (air.cols.instruction.op_b_access.value_2 row 0), (air.cols.instruction.op_b_access.value_3 row 0), (air.cols.instruction.op_c_access.value_0 row 0), (air.cols.instruction.op_c_access.value_1 row 0), (air.cols.instruction.op_c_access.value_2 row 0), (air.cols.instruction.op_c_access.value_3 row 0), (air.cols.instruction.op_a_0 row 0), (air.cols.instruction.is_lb row 0), (air.cols.instruction.is_lbu row 0), (air.cols.instruction.is_lh row 0), (air.cols.instruction.is_lhu row 0), (air.cols.instruction.is_lw row 0), (air.cols.instruction.is_sb row 0), (air.cols.instruction.is_sh row 0), (air.cols.instruction.is_sw row 0)]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), [3, 0, (air.cols.addr_word_0 row 0), (air.cols.addr_word_1 row 0), (air.cols.addr_word_2 row 0), (air.cols.addr_word_3 row 0), (air.cols.instruction.op_b_access.value_0 row 0), (air.cols.instruction.op_b_access.value_1 row 0), (air.cols.instruction.op_b_access.value_2 row 0), (air.cols.instruction.op_b_access.value_3 row 0), (air.cols.instruction.op_c_access.value_0 row 0), (air.cols.instruction.op_c_access.value_1 row 0), (air.cols.instruction.op_c_access.value_2 row 0), (air.cols.instruction.op_c_access.value_3 row 0)]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), [4, 7, 0, 0, (air.cols.addr_word_0 row 0), (air.cols.addr_word_1 row 0)]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), [4, 7, 0, 0, (air.cols.addr_word_2 row 0), (air.cols.addr_word_3 row 0)]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), [4, 8, (air.cols.memory_access.access.diff_16bit_limb row 0), 0, 0, 0]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), [4, 7, 0, 0, (air.cols.memory_access.access.diff_8bit_limb row 0), 0]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), [0, (air.cols.memory_access.access.prev_chunk row 0), (air.cols.memory_access.access.prev_clk row 0), (air.cols.addr_aligned row 0), (air.cols.memory_access.prev_value_0 row 0), (air.cols.memory_access.prev_value_1 row 0), (air.cols.memory_access.prev_value_2 row 0), (air.cols.memory_access.prev_value_3 row 0)]),
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)), [0, (air.cols.chunk row 0), ((air.cols.clk row 0) + 0), (air.cols.addr_aligned row 0), (air.cols.memory_access.access.value_0 row 0), (air.cols.memory_access.access.value_1 row 0), (air.cols.memory_access.access.value_2 row 0), (air.cols.memory_access.access.value_3 row 0)]),
        (-((air.cols.mem_value_is_neg_not_x0 row 0)), [3, 1, (air.cols.instruction.op_a_access.access.value_0 row 0), (air.cols.instruction.op_a_access.access.value_1 row 0), (air.cols.instruction.op_a_access.access.value_2 row 0), (air.cols.instruction.op_a_access.access.value_3 row 0), (air.cols.unsigned_mem_val_0 row 0), (air.cols.unsigned_mem_val_1 row 0), (air.cols.unsigned_mem_val_2 row 0), (air.cols.unsigned_mem_val_3 row 0), 0, (1 * (air.cols.instruction.is_lb row 0)), (1 * (air.cols.instruction.is_lh row 0)), 0])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_MemoryReadWriteAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_MemoryReadWriteAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_MemoryReadWriteAir FKB ExtF)
      (row : ℕ)
    :
      MemoryReadWriteAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition]
        simp [Extraction.constraint_list]
      have equiv_interactions
      :
        MemoryReadWriteAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold MemoryReadWriteAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end MemoryReadWriteAir.ConstraintsAndBuses

namespace MemoryReadWriteAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_MemoryReadWriteAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), #v[0, (air.cols.addr_word_0 row 0), (air.cols.addr_word_1 row 0), (air.cols.addr_word_2 row 0), (air.cols.addr_word_3 row 0), (air.cols.instruction.op_b_access.value_0 row 0), (air.cols.instruction.op_b_access.value_1 row 0), (air.cols.instruction.op_b_access.value_2 row 0), (air.cols.instruction.op_b_access.value_3 row 0), (air.cols.instruction.op_c_access.value_0 row 0), (air.cols.instruction.op_c_access.value_1 row 0), (air.cols.instruction.op_c_access.value_2 row 0), (air.cols.instruction.op_c_access.value_3 row 0)]),
        (-((air.cols.mem_value_is_neg_not_x0 row 0)), #v[1, (air.cols.instruction.op_a_access.access.value_0 row 0), (air.cols.instruction.op_a_access.access.value_1 row 0), (air.cols.instruction.op_a_access.access.value_2 row 0), (air.cols.instruction.op_a_access.access.value_3 row 0), (air.cols.unsigned_mem_val_0 row 0), (air.cols.unsigned_mem_val_1 row 0), (air.cols.unsigned_mem_val_2 row 0), (air.cols.unsigned_mem_val_3 row 0), 0, (1 * (air.cols.instruction.is_lb row 0)), (1 * (air.cols.instruction.is_lh row 0)), 0])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), #v[7, 0, 0, (air.cols.addr_word_0 row 0), (air.cols.addr_word_1 row 0)]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), #v[7, 0, 0, (air.cols.addr_word_2 row 0), (air.cols.addr_word_3 row 0)]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), #v[8, (air.cols.memory_access.access.diff_16bit_limb row 0), 0, 0, 0]),
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), #v[7, 0, 0, (air.cols.memory_access.access.diff_8bit_limb row 0), 0])
      ],
      State := List.map StateBusEntry.deserialise [
        (-(((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0))), #v[(air.cols.memory_access.access.prev_chunk row 0), (air.cols.memory_access.access.prev_clk row 0), (air.cols.addr_aligned row 0), (air.cols.memory_access.prev_value_0 row 0), (air.cols.memory_access.prev_value_1 row 0), (air.cols.memory_access.prev_value_2 row 0), (air.cols.memory_access.prev_value_3 row 0)]),
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)), #v[(air.cols.chunk row 0), ((air.cols.clk row 0) + 0), (air.cols.addr_aligned row 0), (air.cols.memory_access.access.value_0 row 0), (air.cols.memory_access.access.value_1 row 0), (air.cols.memory_access.access.value_2 row 0), (air.cols.memory_access.access.value_3 row 0)])
      ],
      Memory := List.map MemoryBusEntry.deserialise [
        (((((((((air.cols.instruction.is_lb row 0) + (air.cols.instruction.is_lbu row 0)) + (air.cols.instruction.is_lh row 0)) + (air.cols.instruction.is_lhu row 0)) + (air.cols.instruction.is_lw row 0)) + (air.cols.instruction.is_sb row 0)) + (air.cols.instruction.is_sh row 0)) + (air.cols.instruction.is_sw row 0)), #v[(air.cols.instruction.opcode row 0), (air.cols.instruction.op_a_access.access.value_0 row 0), (air.cols.instruction.op_a_access.access.value_1 row 0), (air.cols.instruction.op_a_access.access.value_2 row 0), (air.cols.instruction.op_a_access.access.value_3 row 0), (air.cols.instruction.op_b_access.value_0 row 0), (air.cols.instruction.op_b_access.value_1 row 0), (air.cols.instruction.op_b_access.value_2 row 0), (air.cols.instruction.op_b_access.value_3 row 0), (air.cols.instruction.op_c_access.value_0 row 0), (air.cols.instruction.op_c_access.value_1 row 0), (air.cols.instruction.op_c_access.value_2 row 0), (air.cols.instruction.op_c_access.value_3 row 0), (air.cols.instruction.op_a_0 row 0), (air.cols.instruction.is_lb row 0), (air.cols.instruction.is_lbu row 0), (air.cols.instruction.is_lh row 0), (air.cols.instruction.is_lhu row 0), (air.cols.instruction.is_lw row 0), (air.cols.instruction.is_sb row 0), (air.cols.instruction.is_sh row 0), (air.cols.instruction.is_sw row 0)])
      ]
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_MemoryReadWriteAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (MemoryReadWriteAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end MemoryReadWriteAir.Interactions
