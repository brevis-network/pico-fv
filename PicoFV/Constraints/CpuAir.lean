import PicoFV.RVSail.RV32IM.Operations

import PicoFV.Extraction.CpuAir
import PicoFV.Airs.CpuAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace CpuAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_0 row 0 - air.cols.instruction.b_0 row 0) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_1 row 0 - air.cols.instruction.b_1 row 0) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_2 row 0 - air.cols.instruction.b_2 row 0) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_3 row 0 - air.cols.instruction.b_3 row 0) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_0 row 0 - air.cols.instruction.c_0 row 0) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_1 row 0 - air.cols.instruction.c_1 row 0) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_2 row 0 - air.cols.instruction.c_2 row 0) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_3 row 0 - air.cols.instruction.c_3 row 0) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (1 - air.cols.opcode_selector.imm_b row 0 - 1) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (air.cols.op_b_access.compare_clk row 0 * (air.cols.op_b_access.compare_clk row 0 - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (air.cols.op_b_access.compare_clk row 0 * (air.cols.chunk row 0 - air.cols.op_b_access.prev_chunk row 0)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (air.cols.op_b_access.compare_clk row 0 * (air.cols.clk row 0 + 2) + (1 - air.cols.op_b_access.compare_clk row 0) * air.cols.chunk row 0 - (air.cols.op_b_access.compare_clk row 0 * air.cols.op_b_access.prev_clk row 0 + (1 - air.cols.op_b_access.compare_clk row 0) * air.cols.op_b_access.prev_chunk row 0) - 1 - (air.cols.op_b_access.diff_16bit_limb row 0 + air.cols.op_b_access.diff_8bit_limb row 0 * 65536)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (1 - air.cols.opcode_selector.imm_c row 0 - 1) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (air.cols.op_c_access.compare_clk row 0 * (air.cols.op_c_access.compare_clk row 0 - 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (air.cols.op_c_access.compare_clk row 0 * (air.cols.chunk row 0 - air.cols.op_c_access.prev_chunk row 0)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (air.cols.op_c_access.compare_clk row 0 * (air.cols.clk row 0 + 1) + (1 - air.cols.op_c_access.compare_clk row 0) * air.cols.chunk row 0 - (air.cols.op_c_access.compare_clk row 0 * air.cols.op_c_access.prev_clk row 0 + (1 - air.cols.op_c_access.compare_clk row 0) * air.cols.op_c_access.prev_chunk row 0) - 1 - (air.cols.op_c_access.diff_16bit_limb row 0 + air.cols.op_c_access.diff_8bit_limb row 0 * 65536)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_0 row 0 = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_1 row 0 = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_2 row 0 = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_3 row 0 = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_real row 0 - 1) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.op_a_access.access.compare_clk row 0 * (air.cols.op_a_access.access.compare_clk row 0 - 1)) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.op_a_access.access.compare_clk row 0 * (air.cols.chunk row 0 - air.cols.op_a_access.access.prev_chunk row 0)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.op_a_access.access.compare_clk row 0 * (air.cols.clk row 0 + 3) + (1 - air.cols.op_a_access.access.compare_clk row 0) * air.cols.chunk row 0 - (air.cols.op_a_access.access.compare_clk row 0 * air.cols.op_a_access.access.prev_clk row 0 + (1 - air.cols.op_a_access.access.compare_clk row 0) * air.cols.op_a_access.access.prev_chunk row 0) - 1 - (air.cols.op_a_access.access.diff_16bit_limb row 0 + air.cols.op_a_access.access.diff_8bit_limb row 0 * 65536)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) + (air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0)) * (air.cols.op_a_access.access.value_0 row 0 - air.cols.op_a_access.prev_value_0 row 0) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) + (air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0)) * (air.cols.op_a_access.access.value_1 row 0 - air.cols.op_a_access.prev_value_1 row 0) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) + (air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0)) * (air.cols.op_a_access.access.value_2 row 0 - air.cols.op_a_access.prev_value_2 row 0) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) + (air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0)) * (air.cols.op_a_access.access.value_3 row 0 - air.cols.op_a_access.prev_value_3 row 0) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.branching row 0 * (1 * air.cols.opcode_specific.specific_0 row 0 + 256 * air.cols.opcode_specific.specific_1 row 0 + 65536 * air.cols.opcode_specific.specific_2 row 0 + 16777216 * air.cols.opcode_specific.specific_3 row 0 - air.cols.pc row 0) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 1 * (air.cols.branching row 0 * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.pc row 1))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.branching row 0 * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.next_pc row 0)) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_4 row 0 * (air.cols.opcode_specific.specific_4 row 0 - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_6 row 0 * (air.cols.opcode_specific.specific_6 row 0 - 1)) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_8 row 0 * (air.cols.opcode_specific.specific_8 row 0 - 1)) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (0 + 1 * air.cols.opcode_specific.specific_4 row 0 + 2 * air.cols.opcode_specific.specific_5 row 0 + 4 * air.cols.opcode_specific.specific_6 row 0 + 8 * air.cols.opcode_specific.specific_7 row 0 + 16 * air.cols.opcode_specific.specific_8 row 0 + 32 * air.cols.opcode_specific.specific_9 row 0 + 64 * air.cols.opcode_specific.specific_10 row 0 + 128 * air.cols.opcode_specific.specific_11 row 0 - air.cols.opcode_specific.specific_3 row 0) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_11 row 0 = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (1 - (air.cols.opcode_specific.specific_12 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) - air.cols.opcode_specific.specific_13 row 0) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_13 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_13 row 0 * 0 = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_0 row 0 + air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_2 row 0)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_18 row 0 * (air.cols.opcode_specific.specific_18 row 0 - 1)) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_19 row 0 * (air.cols.opcode_specific.specific_19 row 0 - 1)) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_20 row 0 * (air.cols.opcode_specific.specific_20 row 0 - 1)) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_21 row 0 * (air.cols.opcode_specific.specific_21 row 0 - 1)) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_22 row 0 * (air.cols.opcode_specific.specific_22 row 0 - 1)) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_23 row 0 * (air.cols.opcode_specific.specific_23 row 0 - 1)) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_24 row 0 * (air.cols.opcode_specific.specific_24 row 0 - 1)) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_25 row 0 * (air.cols.opcode_specific.specific_25 row 0 - 1)) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (0 + 1 * air.cols.opcode_specific.specific_18 row 0 + 2 * air.cols.opcode_specific.specific_19 row 0 + 4 * air.cols.opcode_specific.specific_20 row 0 + 8 * air.cols.opcode_specific.specific_21 row 0 + 16 * air.cols.opcode_specific.specific_22 row 0 + 32 * air.cols.opcode_specific.specific_23 row 0 + 64 * air.cols.opcode_specific.specific_24 row 0 + 128 * air.cols.opcode_specific.specific_25 row 0 - air.cols.opcode_specific.specific_17 row 0) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_25 row 0 = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (1 - (air.cols.opcode_specific.specific_26 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) - air.cols.opcode_specific.specific_27 row 0) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_27 row 0 - 1)) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_27 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_27 row 0 * 0 = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0)) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 1 * (air.cols.not_branching row 0 * (air.cols.pc row 0 + 4 - air.cols.pc row 1))) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.not_branching row 0 * (air.cols.is_real row 0 - 1) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.not_branching row 0 * (air.cols.pc row 0 + 4 - air.cols.next_pc row 0)) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.branching row 0 + air.cols.not_branching row 0 - 1) = 0

      @[simp]
      lemma constraint_64_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_64 air row ↔ constraint_64 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_65 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.branching row 0 * (air.cols.branching row 0 - 1)) = 0

      @[simp]
      lemma constraint_65_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_65 air row ↔ constraint_65 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_66 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.not_branching row 0 * (air.cols.not_branching row 0 - 1)) = 0

      @[simp]
      lemma constraint_66_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_66 air row ↔ constraint_66 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_67 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_beq row 0 * air.cols.branching row 0 * (air.cols.opcode_specific.specific_28 row 0 - 1) = 0

      @[simp]
      lemma constraint_67_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_67 air row ↔ constraint_67 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_68 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_beq row 0 * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 - 1)) = 0

      @[simp]
      lemma constraint_68_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_68 air row ↔ constraint_68 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_69 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_bne row 0 * air.cols.branching row 0 * (air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 - 1) = 0

      @[simp]
      lemma constraint_69_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_69 air row ↔ constraint_69 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_70 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_bne row 0 * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_28 row 0 - 1)) = 0

      @[simp]
      lemma constraint_70_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_70 air row ↔ constraint_70 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_71 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bltu row 0) * air.cols.branching row 0) * (air.cols.opcode_specific.specific_30 row 0 - 1) = 0

      @[simp]
      lemma constraint_71_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_71 air row ↔ constraint_71 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_72 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bltu row 0) * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 - 1)) = 0

      @[simp]
      lemma constraint_72_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_72 air row ↔ constraint_72 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_73 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.branching row 0) * (air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_28 row 0 - 1) = 0

      @[simp]
      lemma constraint_73_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_73 air row ↔ constraint_73 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_74 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bgeu row 0) * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_30 row 0 - 1)) = 0

      @[simp]
      lemma constraint_74_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_74 air row ↔ constraint_74 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_75 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_0 row 0 - air.cols.op_b_access.value_0 row 0) = 0

      @[simp]
      lemma constraint_75_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_75 air row ↔ constraint_75 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_76 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_1 row 0 - air.cols.op_b_access.value_1 row 0) = 0

      @[simp]
      lemma constraint_76_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_76 air row ↔ constraint_76 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_77 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_2 row 0 - air.cols.op_b_access.value_2 row 0) = 0

      @[simp]
      lemma constraint_77_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_77 air row ↔ constraint_77 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_78 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_3 row 0 - air.cols.op_b_access.value_3 row 0) = 0

      @[simp]
      lemma constraint_78_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_78 air row ↔ constraint_78 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_79 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 - 1) * air.cols.branching row 0 = 0

      @[simp]
      lemma constraint_79_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_79 air row ↔ constraint_79 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_80 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * ((air.cols.instruction.a_is_0 row 0 - 1) * (1 * air.cols.op_a_access.access.value_0 row 0 + 256 * air.cols.op_a_access.access.value_1 row 0 + 65536 * air.cols.op_a_access.access.value_2 row 0 + 16777216 * air.cols.op_a_access.access.value_3 row 0 - (air.cols.pc row 0 + 4))) = 0

      @[simp]
      lemma constraint_80_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_80 air row ↔ constraint_80 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_81 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (1 * air.cols.opcode_specific.specific_0 row 0 + 256 * air.cols.opcode_specific.specific_1 row 0 + 65536 * air.cols.opcode_specific.specific_2 row 0 + 16777216 * air.cols.opcode_specific.specific_3 row 0 - air.cols.pc row 0) = 0

      @[simp]
      lemma constraint_81_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_81 air row ↔ constraint_81 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_82 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 1 * ((air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.pc row 1))) = 0

      @[simp]
      lemma constraint_82_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_82 air row ↔ constraint_82 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_83 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * ((air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.next_pc row 0)) = 0

      @[simp]
      lemma constraint_83_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_83 air row ↔ constraint_83 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_84 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_28 row 0 * (air.cols.opcode_specific.specific_28 row 0 - 1)) = 0

      @[simp]
      lemma constraint_84_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_84 air row ↔ constraint_84 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_85 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_29 row 0 * (air.cols.opcode_specific.specific_29 row 0 - 1)) = 0

      @[simp]
      lemma constraint_85_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_85 air row ↔ constraint_85 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_86 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_30 row 0 * (air.cols.opcode_specific.specific_30 row 0 - 1)) = 0

      @[simp]
      lemma constraint_86_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_86 air row ↔ constraint_86 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_87 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_31 row 0 * (air.cols.opcode_specific.specific_31 row 0 - 1)) = 0

      @[simp]
      lemma constraint_87_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_87 air row ↔ constraint_87 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_88 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_32 row 0 * (air.cols.opcode_specific.specific_32 row 0 - 1)) = 0

      @[simp]
      lemma constraint_88_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_88 air row ↔ constraint_88 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_89 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_33 row 0 * (air.cols.opcode_specific.specific_33 row 0 - 1)) = 0

      @[simp]
      lemma constraint_89_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_89 air row ↔ constraint_89 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_90 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_34 row 0 * (air.cols.opcode_specific.specific_34 row 0 - 1)) = 0

      @[simp]
      lemma constraint_90_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_90 air row ↔ constraint_90 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_91 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_35 row 0 * (air.cols.opcode_specific.specific_35 row 0 - 1)) = 0

      @[simp]
      lemma constraint_91_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_91 air row ↔ constraint_91 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_92 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (0 + 1 * air.cols.opcode_specific.specific_28 row 0 + 2 * air.cols.opcode_specific.specific_29 row 0 + 4 * air.cols.opcode_specific.specific_30 row 0 + 8 * air.cols.opcode_specific.specific_31 row 0 + 16 * air.cols.opcode_specific.specific_32 row 0 + 32 * air.cols.opcode_specific.specific_33 row 0 + 64 * air.cols.opcode_specific.specific_34 row 0 + 128 * air.cols.opcode_specific.specific_35 row 0 - air.cols.op_a_access.access.value_3 row 0) = 0

      @[simp]
      lemma constraint_92_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_92 air row ↔ constraint_92 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_93 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_35 row 0 = 0

      @[simp]
      lemma constraint_93_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_93 air row ↔ constraint_93 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_94 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 - (air.cols.opcode_specific.specific_36 row 0 * (0 + air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 + air.cols.opcode_specific.specific_31 row 0 + air.cols.opcode_specific.specific_32 row 0 + air.cols.opcode_specific.specific_33 row 0 + air.cols.opcode_specific.specific_34 row 0 - 7)) - air.cols.opcode_specific.specific_37 row 0) = 0

      @[simp]
      lemma constraint_94_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_94 air row ↔ constraint_94 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_95 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_37 row 0 * (air.cols.opcode_specific.specific_37 row 0 - 1)) = 0

      @[simp]
      lemma constraint_95_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_95 air row ↔ constraint_95 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_96 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_37 row 0 * (0 + air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 + air.cols.opcode_specific.specific_31 row 0 + air.cols.opcode_specific.specific_32 row 0 + air.cols.opcode_specific.specific_33 row 0 + air.cols.opcode_specific.specific_34 row 0 - 7)) = 0

      @[simp]
      lemma constraint_96_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_96 air row ↔ constraint_96 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_97 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_37 row 0 * 0 = 0

      @[simp]
      lemma constraint_97_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_97 air row ↔ constraint_97 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_98 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_37 row 0 * (air.cols.op_a_access.access.value_0 row 0 + air.cols.op_a_access.access.value_1 row 0 + air.cols.op_a_access.access.value_2 row 0)) = 0

      @[simp]
      lemma constraint_98_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_98 air row ↔ constraint_98 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_99 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_4 row 0 * (air.cols.opcode_specific.specific_4 row 0 - 1)) = 0

      @[simp]
      lemma constraint_99_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_99 air row ↔ constraint_99 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_100 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[simp]
      lemma constraint_100_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_100 air row ↔ constraint_100 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_101 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_6 row 0 * (air.cols.opcode_specific.specific_6 row 0 - 1)) = 0

      @[simp]
      lemma constraint_101_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_101 air row ↔ constraint_101 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_102 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[simp]
      lemma constraint_102_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_102 air row ↔ constraint_102 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_103 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_8 row 0 * (air.cols.opcode_specific.specific_8 row 0 - 1)) = 0

      @[simp]
      lemma constraint_103_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_103 air row ↔ constraint_103 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_104 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[simp]
      lemma constraint_104_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_104 air row ↔ constraint_104 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_105 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[simp]
      lemma constraint_105_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_105 air row ↔ constraint_105 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_106 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[simp]
      lemma constraint_106_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_106 air row ↔ constraint_106 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_107 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (0 + 1 * air.cols.opcode_specific.specific_4 row 0 + 2 * air.cols.opcode_specific.specific_5 row 0 + 4 * air.cols.opcode_specific.specific_6 row 0 + 8 * air.cols.opcode_specific.specific_7 row 0 + 16 * air.cols.opcode_specific.specific_8 row 0 + 32 * air.cols.opcode_specific.specific_9 row 0 + 64 * air.cols.opcode_specific.specific_10 row 0 + 128 * air.cols.opcode_specific.specific_11 row 0 - air.cols.opcode_specific.specific_3 row 0) = 0

      @[simp]
      lemma constraint_107_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_107 air row ↔ constraint_107 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_108 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * air.cols.opcode_specific.specific_11 row 0 = 0

      @[simp]
      lemma constraint_108_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_108 air row ↔ constraint_108 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_109 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (1 - (air.cols.opcode_specific.specific_12 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) - air.cols.opcode_specific.specific_13 row 0) = 0

      @[simp]
      lemma constraint_109_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_109 air row ↔ constraint_109 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_110 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[simp]
      lemma constraint_110_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_110 air row ↔ constraint_110 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_111 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_13 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) = 0

      @[simp]
      lemma constraint_111_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_111 air row ↔ constraint_111 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_112 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * air.cols.opcode_specific.specific_13 row 0 * 0 = 0

      @[simp]
      lemma constraint_112_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_112 air row ↔ constraint_112 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_113 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_0 row 0 + air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_2 row 0)) = 0

      @[simp]
      lemma constraint_113_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_113 air row ↔ constraint_113 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_114 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_18 row 0 * (air.cols.opcode_specific.specific_18 row 0 - 1)) = 0

      @[simp]
      lemma constraint_114_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_114 air row ↔ constraint_114 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_115 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_19 row 0 * (air.cols.opcode_specific.specific_19 row 0 - 1)) = 0

      @[simp]
      lemma constraint_115_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_115 air row ↔ constraint_115 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_116 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_20 row 0 * (air.cols.opcode_specific.specific_20 row 0 - 1)) = 0

      @[simp]
      lemma constraint_116_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_116 air row ↔ constraint_116 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_117 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_21 row 0 * (air.cols.opcode_specific.specific_21 row 0 - 1)) = 0

      @[simp]
      lemma constraint_117_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_117 air row ↔ constraint_117 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_118 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_22 row 0 * (air.cols.opcode_specific.specific_22 row 0 - 1)) = 0

      @[simp]
      lemma constraint_118_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_118 air row ↔ constraint_118 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_119 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_23 row 0 * (air.cols.opcode_specific.specific_23 row 0 - 1)) = 0

      @[simp]
      lemma constraint_119_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_119 air row ↔ constraint_119 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_120 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_24 row 0 * (air.cols.opcode_specific.specific_24 row 0 - 1)) = 0

      @[simp]
      lemma constraint_120_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_120 air row ↔ constraint_120 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_121 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_25 row 0 * (air.cols.opcode_specific.specific_25 row 0 - 1)) = 0

      @[simp]
      lemma constraint_121_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_121 air row ↔ constraint_121 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_122 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (0 + 1 * air.cols.opcode_specific.specific_18 row 0 + 2 * air.cols.opcode_specific.specific_19 row 0 + 4 * air.cols.opcode_specific.specific_20 row 0 + 8 * air.cols.opcode_specific.specific_21 row 0 + 16 * air.cols.opcode_specific.specific_22 row 0 + 32 * air.cols.opcode_specific.specific_23 row 0 + 64 * air.cols.opcode_specific.specific_24 row 0 + 128 * air.cols.opcode_specific.specific_25 row 0 - air.cols.opcode_specific.specific_17 row 0) = 0

      @[simp]
      lemma constraint_122_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_122 air row ↔ constraint_122 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_123 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_25 row 0 = 0

      @[simp]
      lemma constraint_123_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_123 air row ↔ constraint_123 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_124 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 - (air.cols.opcode_specific.specific_26 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) - air.cols.opcode_specific.specific_27 row 0) = 0

      @[simp]
      lemma constraint_124_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_124 air row ↔ constraint_124 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_125 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_27 row 0 - 1)) = 0

      @[simp]
      lemma constraint_125_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_125 air row ↔ constraint_125 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_126 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_27 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) = 0

      @[simp]
      lemma constraint_126_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_126 air row ↔ constraint_126 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_127 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_27 row 0 * 0 = 0

      @[simp]
      lemma constraint_127_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_127 air row ↔ constraint_127 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_128 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0)) = 0

      @[simp]
      lemma constraint_128_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_128 air row ↔ constraint_128 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_129 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (1 * air.cols.opcode_specific.specific_0 row 0 + 256 * air.cols.opcode_specific.specific_1 row 0 + 65536 * air.cols.opcode_specific.specific_2 row 0 + 16777216 * air.cols.opcode_specific.specific_3 row 0 - air.cols.pc row 0) = 0

      @[simp]
      lemma constraint_129_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_129 air row ↔ constraint_129 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_130 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_4 row 0 * (air.cols.opcode_specific.specific_4 row 0 - 1)) = 0

      @[simp]
      lemma constraint_130_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_130 air row ↔ constraint_130 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_131 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[simp]
      lemma constraint_131_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_131 air row ↔ constraint_131 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_132 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_6 row 0 * (air.cols.opcode_specific.specific_6 row 0 - 1)) = 0

      @[simp]
      lemma constraint_132_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_132 air row ↔ constraint_132 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_133 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[simp]
      lemma constraint_133_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_133 air row ↔ constraint_133 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_134 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_8 row 0 * (air.cols.opcode_specific.specific_8 row 0 - 1)) = 0

      @[simp]
      lemma constraint_134_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_134 air row ↔ constraint_134 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_135 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[simp]
      lemma constraint_135_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_135 air row ↔ constraint_135 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_136 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[simp]
      lemma constraint_136_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_136 air row ↔ constraint_136 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_137 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[simp]
      lemma constraint_137_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_137 air row ↔ constraint_137 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
    def constraint_138 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (0 + 1 * air.cols.opcode_specific.specific_4 row 0 + 2 * air.cols.opcode_specific.specific_5 row 0 + 4 * air.cols.opcode_specific.specific_6 row 0 + 8 * air.cols.opcode_specific.specific_7 row 0 + 16 * air.cols.opcode_specific.specific_8 row 0 + 32 * air.cols.opcode_specific.specific_9 row 0 + 64 * air.cols.opcode_specific.specific_10 row 0 + 128 * air.cols.opcode_specific.specific_11 row 0 - air.cols.opcode_specific.specific_3 row 0) = 0

      @[simp]
      lemma constraint_138_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_138 air row ↔ constraint_138 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_139 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * air.cols.opcode_specific.specific_11 row 0 = 0

      @[simp]
      lemma constraint_139_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_139 air row ↔ constraint_139 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_140 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (1 - (air.cols.opcode_specific.specific_12 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) - air.cols.opcode_specific.specific_13 row 0) = 0

      @[simp]
      lemma constraint_140_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_140 air row ↔ constraint_140 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_141 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[simp]
      lemma constraint_141_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_141 air row ↔ constraint_141 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_142 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_13 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) = 0

      @[simp]
      lemma constraint_142_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_142 air row ↔ constraint_142 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_143 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * air.cols.opcode_specific.specific_13 row 0 * 0 = 0

      @[simp]
      lemma constraint_143_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_143 air row ↔ constraint_143 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_144 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_0 row 0 + air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_2 row 0)) = 0

      @[simp]
      lemma constraint_144_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_144 air row ↔ constraint_144 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_145 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_mul_send_to_table row 0 - air.cols.op_a_access.prev_value_1 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0

      @[simp]
      lemma constraint_145_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_145 air row ↔ constraint_145 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_146 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_0 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 3)) - air.cols.opcode_specific.specific_1 row 0) = 0

      @[simp]
      lemma constraint_146_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_146 air row ↔ constraint_146 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_147 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_1 row 0 * (air.cols.opcode_specific.specific_1 row 0 - 1)) = 0

      @[simp]
      lemma constraint_147_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_147 air row ↔ constraint_147 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_148 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 3)) = 0

      @[simp]
      lemma constraint_148_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_148 air row ↔ constraint_148 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_149 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_2 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 240)) - air.cols.opcode_specific.specific_3 row 0) = 0

      @[simp]
      lemma constraint_149_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_149 air row ↔ constraint_149 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_150 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_3 row 0 * (air.cols.opcode_specific.specific_3 row 0 - 1)) = 0

      @[simp]
      lemma constraint_150_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_150 air row ↔ constraint_150 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_151 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_3 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 240)) = 0

      @[simp]
      lemma constraint_151_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_151 air row ↔ constraint_151 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_152 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_0 row 0 - 0) = 0

      @[simp]
      lemma constraint_152_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_152 air row ↔ constraint_152 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_153 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_1 row 0 - 0) = 0

      @[simp]
      lemma constraint_153_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_153 air row ↔ constraint_153 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_154 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_2 row 0 - 0) = 0

      @[simp]
      lemma constraint_154_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_154 air row ↔ constraint_154 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_155 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_3 row 0 - 0) = 0

      @[simp]
      lemma constraint_155_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_155 air row ↔ constraint_155 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_156 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_0 row 0 - air.cols.op_a_access.prev_value_0 row 0)) = 0

      @[simp]
      lemma constraint_156_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_156 air row ↔ constraint_156 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_157 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_1 row 0 - air.cols.op_a_access.prev_value_1 row 0)) = 0

      @[simp]
      lemma constraint_157_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_157 air row ↔ constraint_157 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_158 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_2 row 0 - air.cols.op_a_access.prev_value_2 row 0)) = 0

      @[simp]
      lemma constraint_158_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_158 air row ↔ constraint_158 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_159 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_3 row 0 - air.cols.op_a_access.prev_value_3 row 0)) = 0

      @[simp]
      lemma constraint_159_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_159 air row ↔ constraint_159 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_160 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 - (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_9 row 0)) = 0

      @[simp]
      lemma constraint_160_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_160 air row ↔ constraint_160 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_161 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_18 row 0 * (air.cols.opcode_specific.specific_18 row 0 - 1)) = 0

      @[simp]
      lemma constraint_161_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_161 air row ↔ constraint_161 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_162 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_19 row 0 * (air.cols.opcode_specific.specific_19 row 0 - 1)) = 0

      @[simp]
      lemma constraint_162_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_162 air row ↔ constraint_162 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_163 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_20 row 0 * (air.cols.opcode_specific.specific_20 row 0 - 1)) = 0

      @[simp]
      lemma constraint_163_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_163 air row ↔ constraint_163 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_164 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_21 row 0 * (air.cols.opcode_specific.specific_21 row 0 - 1)) = 0

      @[simp]
      lemma constraint_164_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_164 air row ↔ constraint_164 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_165 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_22 row 0 * (air.cols.opcode_specific.specific_22 row 0 - 1)) = 0

      @[simp]
      lemma constraint_165_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_165 air row ↔ constraint_165 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_166 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_23 row 0 * (air.cols.opcode_specific.specific_23 row 0 - 1)) = 0

      @[simp]
      lemma constraint_166_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_166 air row ↔ constraint_166 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_167 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_24 row 0 * (air.cols.opcode_specific.specific_24 row 0 - 1)) = 0

      @[simp]
      lemma constraint_167_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_167 air row ↔ constraint_167 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_168 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_25 row 0 * (air.cols.opcode_specific.specific_25 row 0 - 1)) = 0

      @[simp]
      lemma constraint_168_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_168 air row ↔ constraint_168 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_169 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (0 + 1 * air.cols.opcode_specific.specific_18 row 0 + 2 * air.cols.opcode_specific.specific_19 row 0 + 4 * air.cols.opcode_specific.specific_20 row 0 + 8 * air.cols.opcode_specific.specific_21 row 0 + 16 * air.cols.opcode_specific.specific_22 row 0 + 32 * air.cols.opcode_specific.specific_23 row 0 + 64 * air.cols.opcode_specific.specific_24 row 0 + 128 * air.cols.opcode_specific.specific_25 row 0 - air.cols.opcode_specific.specific_31 row 0) = 0

      @[simp]
      lemma constraint_169_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_169 air row ↔ constraint_169 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_170 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * air.cols.opcode_specific.specific_25 row 0 = 0

      @[simp]
      lemma constraint_170_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_170 air row ↔ constraint_170 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_171 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (1 - (air.cols.opcode_specific.specific_26 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) - air.cols.opcode_specific.specific_27 row 0) = 0

      @[simp]
      lemma constraint_171_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_171 air row ↔ constraint_171 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_172 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_27 row 0 - 1)) = 0

      @[simp]
      lemma constraint_172_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_172 air row ↔ constraint_172 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_173 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_27 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) = 0

      @[simp]
      lemma constraint_173_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_173 air row ↔ constraint_173 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_174 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * air.cols.opcode_specific.specific_27 row 0 * 0 = 0

      @[simp]
      lemma constraint_174_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_174 air row ↔ constraint_174 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_175 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0)) = 0

      @[simp]
      lemma constraint_175_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_175 air row ↔ constraint_175 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_176 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_6 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 16)) - air.cols.opcode_specific.specific_7 row 0) = 0

      @[simp]
      lemma constraint_176_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_176 air row ↔ constraint_176 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_177 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[simp]
      lemma constraint_177_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_177 air row ↔ constraint_177 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_178 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 16)) = 0

      @[simp]
      lemma constraint_178_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_178 air row ↔ constraint_178 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_179 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_8 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 26)) - air.cols.opcode_specific.specific_9 row 0) = 0

      @[simp]
      lemma constraint_179_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_179 air row ↔ constraint_179 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_180 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[simp]
      lemma constraint_180_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_180 air row ↔ constraint_180 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_181 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 26)) = 0

      @[simp]
      lemma constraint_181_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_181 air row ↔ constraint_181 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_182 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[simp]
      lemma constraint_182_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_182 air row ↔ constraint_182 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_183 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[simp]
      lemma constraint_183_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_183 air row ↔ constraint_183 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_184 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_12 row 0 * (air.cols.opcode_specific.specific_12 row 0 - 1)) = 0

      @[simp]
      lemma constraint_184_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_184 air row ↔ constraint_184 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_185 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[simp]
      lemma constraint_185_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_185 air row ↔ constraint_185 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_186 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_14 row 0 * (air.cols.opcode_specific.specific_14 row 0 - 1)) = 0

      @[simp]
      lemma constraint_186_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_186 air row ↔ constraint_186 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_187 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_15 row 0 * (air.cols.opcode_specific.specific_15 row 0 - 1)) = 0

      @[simp]
      lemma constraint_187_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_187 air row ↔ constraint_187 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_188 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_16 row 0 * (air.cols.opcode_specific.specific_16 row 0 - 1)) = 0

      @[simp]
      lemma constraint_188_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_188 air row ↔ constraint_188 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_189 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_17 row 0 * (air.cols.opcode_specific.specific_17 row 0 - 1)) = 0

      @[simp]
      lemma constraint_189_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_189 air row ↔ constraint_189 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_190 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (0 + air.cols.opcode_specific.specific_10 row 0 + air.cols.opcode_specific.specific_11 row 0 + air.cols.opcode_specific.specific_12 row 0 + air.cols.opcode_specific.specific_13 row 0 + air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0 + air.cols.opcode_specific.specific_17 row 0 - 1) = 0

      @[simp]
      lemma constraint_190_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_190 air row ↔ constraint_190 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_191 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0))) * (0 + air.cols.opcode_specific.specific_10 row 0 + air.cols.opcode_specific.specific_11 row 0 + air.cols.opcode_specific.specific_12 row 0 + air.cols.opcode_specific.specific_13 row 0 + air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0 + air.cols.opcode_specific.specific_17 row 0) = 0

      @[simp]
      lemma constraint_191_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_191 air row ↔ constraint_191 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_192 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_10 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 0) = 0

      @[simp]
      lemma constraint_192_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_192 air row ↔ constraint_192 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_193 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_11 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 1) = 0

      @[simp]
      lemma constraint_193_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_193 air row ↔ constraint_193 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_194 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_12 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 2) = 0

      @[simp]
      lemma constraint_194_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_194 air row ↔ constraint_194 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_195 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_13 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 3) = 0

      @[simp]
      lemma constraint_195_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_195 air row ↔ constraint_195 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_196 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_14 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 4) = 0

      @[simp]
      lemma constraint_196_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_196 air row ↔ constraint_196 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_197 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_15 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 5) = 0

      @[simp]
      lemma constraint_197_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_197 air row ↔ constraint_197 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_198 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_16 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 6) = 0

      @[simp]
      lemma constraint_198_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_198 air row ↔ constraint_198 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_199 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_17 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 7) = 0

      @[simp]
      lemma constraint_199_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_199 air row ↔ constraint_199 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_200 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (air.cols.op_b_access.value_1 row 0 - 0) = 0

      @[simp]
      lemma constraint_200_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_200 air row ↔ constraint_200 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_201 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (air.cols.op_b_access.value_2 row 0 - 0) = 0

      @[simp]
      lemma constraint_201_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_201 air row ↔ constraint_201 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_202 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (air.cols.op_b_access.value_3 row 0 - 0) = 0

      @[simp]
      lemma constraint_202_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_202 air row ↔ constraint_202 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_203 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 0 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 4 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 8 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 12 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 16 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 20 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 24 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 28 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_0 row 0) = 0

      @[simp]
      lemma constraint_203_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_203 air row ↔ constraint_203 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_204 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 1 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 5 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 9 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 13 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 17 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 21 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 25 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 29 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_1 row 0) = 0

      @[simp]
      lemma constraint_204_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_204 air row ↔ constraint_204 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_205 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 2 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 6 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 10 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 14 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 18 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 22 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 26 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 30 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_2 row 0) = 0

      @[simp]
      lemma constraint_205_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_205 air row ↔ constraint_205 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_206 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 3 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 7 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 11 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 15 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 19 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 23 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 27 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 31 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_3 row 0) = 0

      @[simp]
      lemma constraint_206_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_206 air row ↔ constraint_206 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_207 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_0 row 0 - air.cols.opcode_specific.specific_28 row 0) = 0

      @[simp]
      lemma constraint_207_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_207 air row ↔ constraint_207 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_208 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_1 row 0 - air.cols.opcode_specific.specific_29 row 0) = 0

      @[simp]
      lemma constraint_208_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_208 air row ↔ constraint_208 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_209 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_2 row 0 - air.cols.opcode_specific.specific_30 row 0) = 0

      @[simp]
      lemma constraint_209_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_209 air row ↔ constraint_209 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_210 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_3 row 0 - air.cols.opcode_specific.specific_31 row 0) = 0

      @[simp]
      lemma constraint_210_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_210 air row ↔ constraint_210 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_211 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (0 + air.public_values 32 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 33 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 34 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 35 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 36 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 37 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 38 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 39 * air.cols.opcode_specific.specific_17 row 0 - (1 * air.cols.op_c_access.value_0 row 0 + 256 * air.cols.op_c_access.value_1 row 0 + 65536 * air.cols.op_c_access.value_2 row 0 + 16777216 * air.cols.op_c_access.value_3 row 0)) = 0

      @[simp]
      lemma constraint_211_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_211 air row ↔ constraint_211 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_212 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_4 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) - air.cols.opcode_specific.specific_5 row 0) = 0

      @[simp]
      lemma constraint_212_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_212 air row ↔ constraint_212 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_213 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[simp]
      lemma constraint_213_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_213 air row ↔ constraint_213 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_214 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) = 0

      @[simp]
      lemma constraint_214_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_214 air row ↔ constraint_214 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_215 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * ((air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 + air.cols.opcode_selector.is_unimpl row 0) * air.cols.is_real row 1) = 0

      @[simp]
      lemma constraint_215_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_215 air row ↔ constraint_215 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_216 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * air.cols.next_pc row 0 = 0

      @[simp]
      lemma constraint_216_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_216 air row ↔ constraint_216 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_217 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - air.cols.opcode_specific.specific_28 row 0) = 0

      @[simp]
      lemma constraint_217_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_217 air row ↔ constraint_217 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_218 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_1 row 0 - air.cols.opcode_specific.specific_29 row 0) = 0

      @[simp]
      lemma constraint_218_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_218 air row ↔ constraint_218 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_219 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_2 row 0 - air.cols.opcode_specific.specific_30 row 0) = 0

      @[simp]
      lemma constraint_219_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_219 air row ↔ constraint_219 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_220 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_3 row 0 - air.cols.opcode_specific.specific_31 row 0) = 0

      @[simp]
      lemma constraint_220_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_220 air row ↔ constraint_220 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_221 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (1 * air.cols.op_b_access.value_0 row 0 + 256 * air.cols.op_b_access.value_1 row 0 + 65536 * air.cols.op_b_access.value_2 row 0 + 16777216 * air.cols.op_b_access.value_3 row 0 - air.public_values 42) = 0

      @[simp]
      lemma constraint_221_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_221 air row ↔ constraint_221 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_222 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 1 * (air.cols.chunk row 0 - air.cols.chunk row 1)) = 0

      @[simp]
      lemma constraint_222_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_222 air row ↔ constraint_222 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_223 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row * air.cols.clk row 0 = 0

      @[simp]
      lemma constraint_223_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_223 air row ↔ constraint_223 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_224 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 1 * (air.cols.clk row 0 + 4 + air.cols.op_a_access.prev_value_2 row 0 * air.cols.opcode_selector.is_ecall row 0 - air.cols.clk row 1)) = 0

      @[simp]
      lemma constraint_224_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_224 air row ↔ constraint_224 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_225 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.clk row 0 - (air.cols.clk_16bit_limb row 0 + air.cols.clk_8bit_limb row 0 * 65536)) = 0

      @[simp]
      lemma constraint_225_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_225 air row ↔ constraint_225 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_226 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_4 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) - air.cols.opcode_specific.specific_5 row 0) = 0

      @[simp]
      lemma constraint_226_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_226 air row ↔ constraint_226 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_227 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[simp]
      lemma constraint_227_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_227 air row ↔ constraint_227 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_228 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) = 0

      @[simp]
      lemma constraint_228_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_228 air row ↔ constraint_228 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_229 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_sequential_instr row 0 - (1 - (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 + air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0 + air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0))) = 0

      @[simp]
      lemma constraint_229_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_229 air row ↔ constraint_229 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_230 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 1 * (air.cols.is_sequential_instr row 0 * (air.cols.pc row 0 + 4 - air.cols.pc row 1))) = 0

      @[simp]
      lemma constraint_230_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_230 air row ↔ constraint_230 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_231 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_sequential_instr row 0 * (air.cols.pc row 0 + 4 - air.cols.next_pc row 0)) = 0

      @[simp]
      lemma constraint_231_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_231 air row ↔ constraint_231 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_232 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.public_values 44 - air.cols.chunk row 0) = 0

      @[simp]
      lemma constraint_232_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_232 air row ↔ constraint_232 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_233 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row * (air.public_values 40 - air.cols.pc row 0) = 0

      @[simp]
      lemma constraint_233_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_233 air row ↔ constraint_233 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_234 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * ((air.cols.is_real row 0 - air.cols.is_real row 1) * (air.public_values 41 - air.cols.next_pc row 0)) = 0

      @[simp]
      lemma constraint_234_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_234 air row ↔ constraint_234 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_235 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row * (air.cols.is_real row 0 * (air.public_values 41 - air.cols.next_pc row 0)) = 0

      @[simp]
      lemma constraint_235_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_235 air row ↔ constraint_235 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_236 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_real row 0 - 1) = 0

      @[simp]
      lemma constraint_236_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_236 air row ↔ constraint_236 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_237 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row * (air.cols.is_real row 0 - 1) = 0

      @[simp]
      lemma constraint_237_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_237 air row ↔ constraint_237 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_238 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * ((air.cols.is_real row 0 - 1) * air.cols.is_real row 1) = 0

      @[simp]
      lemma constraint_238_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_238 air row ↔ constraint_238 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_239 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * (air.cols.opcode_selector.imm_b row 0 - 1) = 0

      @[simp]
      lemma constraint_239_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_239 air row ↔ constraint_239 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_240 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * (air.cols.opcode_selector.imm_c row 0 - 1) = 0

      @[simp]
      lemma constraint_240_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_240 air row ↔ constraint_240 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_241 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_alu row 0 = 0

      @[simp]
      lemma constraint_241_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_241 air row ↔ constraint_241 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_242 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_ecall row 0 = 0

      @[simp]
      lemma constraint_242_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_242 air row ↔ constraint_242 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_243 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lb row 0 = 0

      @[simp]
      lemma constraint_243_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_243 air row ↔ constraint_243 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_244 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lbu row 0 = 0

      @[simp]
      lemma constraint_244_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_244 air row ↔ constraint_244 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_245 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lh row 0 = 0

      @[simp]
      lemma constraint_245_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_245 air row ↔ constraint_245 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_246 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lhu row 0 = 0

      @[simp]
      lemma constraint_246_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_246 air row ↔ constraint_246 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_247 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lw row 0 = 0

      @[simp]
      lemma constraint_247_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_247 air row ↔ constraint_247 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_248 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_sb row 0 = 0

      @[simp]
      lemma constraint_248_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_248 air row ↔ constraint_248 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_249 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_sh row 0 = 0

      @[simp]
      lemma constraint_249_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_249 air row ↔ constraint_249 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_250 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_sw row 0 = 0

      @[simp]
      lemma constraint_250_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_250 air row ↔ constraint_250 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_251 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_beq row 0 = 0

      @[simp]
      lemma constraint_251_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_251 air row ↔ constraint_251 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_252 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bne row 0 = 0

      @[simp]
      lemma constraint_252_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_252 air row ↔ constraint_252 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_253 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_blt row 0 = 0

      @[simp]
      lemma constraint_253_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_253 air row ↔ constraint_253 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_254 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bge row 0 = 0

      @[simp]
      lemma constraint_254_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_254 air row ↔ constraint_254 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_255 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bltu row 0 = 0

      @[simp]
      lemma constraint_255_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_255 air row ↔ constraint_255 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_256 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bgeu row 0 = 0

      @[simp]
      lemma constraint_256_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_256 air row ↔ constraint_256 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_257 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_jalr row 0 = 0

      @[simp]
      lemma constraint_257_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_257 air row ↔ constraint_257 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_258 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_jal row 0 = 0

      @[simp]
      lemma constraint_258_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_258 air row ↔ constraint_258 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_259 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_auipc row 0 = 0

      @[simp]
      lemma constraint_259_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_259 air row ↔ constraint_259 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_260 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_unimpl row 0 = 0

      @[simp]
      lemma constraint_260_equiv (air : Valid_CpuAir F ExtF) (row : ℕ)
      : CpuAir.Extraction.constraint_260 air row ↔ constraint_260 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_CpuAir F ExtF) (row : ℕ) : List Prop :=
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
          constraint_130 air row,
          constraint_131 air row,
          constraint_132 air row,
          constraint_133 air row,
          constraint_134 air row,
          constraint_135 air row,
          constraint_136 air row,
          constraint_137 air row,
          constraint_138 air row,
          constraint_139 air row,
          constraint_140 air row,
          constraint_141 air row,
          constraint_142 air row,
          constraint_143 air row,
          constraint_144 air row,
          constraint_145 air row,
          constraint_146 air row,
          constraint_147 air row,
          constraint_148 air row,
          constraint_149 air row,
          constraint_150 air row,
          constraint_151 air row,
          constraint_152 air row,
          constraint_153 air row,
          constraint_154 air row,
          constraint_155 air row,
          constraint_156 air row,
          constraint_157 air row,
          constraint_158 air row,
          constraint_159 air row,
          constraint_160 air row,
          constraint_161 air row,
          constraint_162 air row,
          constraint_163 air row,
          constraint_164 air row,
          constraint_165 air row,
          constraint_166 air row,
          constraint_167 air row,
          constraint_168 air row,
          constraint_169 air row,
          constraint_170 air row,
          constraint_171 air row,
          constraint_172 air row,
          constraint_173 air row,
          constraint_174 air row,
          constraint_175 air row,
          constraint_176 air row,
          constraint_177 air row,
          constraint_178 air row,
          constraint_179 air row,
          constraint_180 air row,
          constraint_181 air row,
          constraint_182 air row,
          constraint_183 air row,
          constraint_184 air row,
          constraint_185 air row,
          constraint_186 air row,
          constraint_187 air row,
          constraint_188 air row,
          constraint_189 air row,
          constraint_190 air row,
          constraint_191 air row,
          constraint_192 air row,
          constraint_193 air row,
          constraint_194 air row,
          constraint_195 air row,
          constraint_196 air row,
          constraint_197 air row,
          constraint_198 air row,
          constraint_199 air row,
          constraint_200 air row,
          constraint_201 air row,
          constraint_202 air row,
          constraint_203 air row,
          constraint_204 air row,
          constraint_205 air row,
          constraint_206 air row,
          constraint_207 air row,
          constraint_208 air row,
          constraint_209 air row,
          constraint_210 air row,
          constraint_211 air row,
          constraint_212 air row,
          constraint_213 air row,
          constraint_214 air row,
          constraint_215 air row,
          constraint_216 air row,
          constraint_217 air row,
          constraint_218 air row,
          constraint_219 air row,
          constraint_220 air row,
          constraint_221 air row,
          constraint_222 air row,
          constraint_223 air row,
          constraint_224 air row,
          constraint_225 air row,
          constraint_226 air row,
          constraint_227 air row,
          constraint_228 air row,
          constraint_229 air row,
          constraint_230 air row,
          constraint_231 air row,
          constraint_232 air row,
          constraint_233 air row,
          constraint_234 air row,
          constraint_235 air row,
          constraint_236 air row,
          constraint_237 air row,
          constraint_238 air row,
          constraint_239 air row,
          constraint_240 air row,
          constraint_241 air row,
          constraint_242 air row,
          constraint_243 air row,
          constraint_244 air row,
          constraint_245 air row,
          constraint_246 air row,
          constraint_247 air row,
          constraint_248 air row,
          constraint_249 air row,
          constraint_250 air row,
          constraint_251 air row,
          constraint_252 air row,
          constraint_253 air row,
          constraint_254 air row,
          constraint_255 air row,
          constraint_256 air row,
          constraint_257 air row,
          constraint_258 air row,
          constraint_259 air row,
          constraint_260 air row
        ]

    end row_constraints

    section row_buses

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_CpuAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [
        (-air.cols.is_real row 0,
          [1, air.cols.pc row 0, air.cols.instruction.opcode row 0, air.cols.instruction.opcode row 0,
            air.cols.instruction.a_0 row 0, air.cols.instruction.a_1 row 0, air.cols.instruction.a_2 row 0,
            air.cols.instruction.a_3 row 0, air.cols.instruction.b_0 row 0, air.cols.instruction.b_1 row 0,
            air.cols.instruction.b_2 row 0, air.cols.instruction.b_3 row 0, air.cols.instruction.c_0 row 0,
            air.cols.instruction.c_1 row 0, air.cols.instruction.c_2 row 0, air.cols.instruction.c_3 row 0,
            air.cols.instruction.a_is_0 row 0, air.cols.opcode_selector.imm_b row 0,
            air.cols.opcode_selector.imm_c row 0, air.cols.is_alu_instruction row 0,
            air.cols.opcode_selector.is_ecall row 0, air.cols.opcode_selector.is_lb row 0,
            air.cols.opcode_selector.is_lbu row 0, air.cols.opcode_selector.is_lh row 0,
            air.cols.opcode_selector.is_lhu row 0, air.cols.opcode_selector.is_lw row 0,
            air.cols.opcode_selector.is_sb row 0, air.cols.opcode_selector.is_sh row 0,
            air.cols.opcode_selector.is_sw row 0, air.cols.opcode_selector.is_beq row 0,
            air.cols.opcode_selector.is_bne row 0, air.cols.opcode_selector.is_blt row 0,
            air.cols.opcode_selector.is_bge row 0, air.cols.opcode_selector.is_bltu row 0,
            air.cols.opcode_selector.is_bgeu row 0, air.cols.opcode_selector.is_jalr row 0,
            air.cols.opcode_selector.is_jal row 0, air.cols.opcode_selector.is_auipc row 0,
            air.cols.opcode_selector.is_unimpl row 0]),
        (air.cols.opcode_selector.imm_b row 0 - 1, [4, 8, air.cols.op_b_access.diff_16bit_limb row 0, 0, 0, 0]),
        (air.cols.opcode_selector.imm_b row 0 - 1, [4, 7, 0, 0, air.cols.op_b_access.diff_8bit_limb row 0, 0]),
        (air.cols.opcode_selector.imm_b row 0 - 1,
          [0, air.cols.op_b_access.prev_chunk row 0, air.cols.op_b_access.prev_clk row 0,
            air.cols.instruction.b_0 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0,
            air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (1 - air.cols.opcode_selector.imm_b row 0,
          [0, air.cols.chunk row 0, air.cols.clk row 0 + 2, air.cols.instruction.b_0 row 0,
            air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0,
            air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (air.cols.opcode_selector.imm_c row 0 - 1, [4, 8, air.cols.op_c_access.diff_16bit_limb row 0, 0, 0, 0]),
        (air.cols.opcode_selector.imm_c row 0 - 1, [4, 7, 0, 0, air.cols.op_c_access.diff_8bit_limb row 0, 0]),
        (air.cols.opcode_selector.imm_c row 0 - 1,
          [0, air.cols.op_c_access.prev_chunk row 0, air.cols.op_c_access.prev_clk row 0,
            air.cols.instruction.c_0 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0,
            air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (1 - air.cols.opcode_selector.imm_c row 0,
          [0, air.cols.chunk row 0, air.cols.clk row 0 + 1, air.cols.instruction.c_0 row 0,
            air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0,
            air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-air.cols.is_real row 0, [4, 8, air.cols.op_a_access.access.diff_16bit_limb row 0, 0, 0, 0]),
        (-air.cols.is_real row 0, [4, 7, 0, 0, air.cols.op_a_access.access.diff_8bit_limb row 0, 0]),
        (-air.cols.is_real row 0,
          [0, air.cols.op_a_access.access.prev_chunk row 0, air.cols.op_a_access.access.prev_clk row 0,
            air.cols.instruction.a_0 row 0, air.cols.op_a_access.prev_value_0 row 0,
            air.cols.op_a_access.prev_value_1 row 0, air.cols.op_a_access.prev_value_2 row 0,
            air.cols.op_a_access.prev_value_3 row 0]),
        (air.cols.is_real row 0,
          [0, air.cols.chunk row 0, air.cols.clk row 0 + 3, air.cols.instruction.a_0 row 0,
            air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0,
            air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0]),
        (-air.cols.is_real row 0,
          [4, 7, 0, 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0]),
        (-air.cols.is_real row 0,
          [4, 7, 0, 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0]),
        (-air.cols.is_memory_instruction row 0,
          [0, air.cols.instruction.opcode row 0, air.cols.op_a_access.access.value_0 row 0,
            air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0,
            air.cols.op_a_access.access.value_3 row 0, air.cols.op_b_access.value_0 row 0,
            air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0,
            air.cols.op_b_access.value_3 row 0, air.cols.op_c_access.value_0 row 0,
            air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0,
            air.cols.op_c_access.value_3 row 0, air.cols.instruction.a_is_0 row 0,
            air.cols.opcode_selector.is_lb row 0, air.cols.opcode_selector.is_lbu row 0,
            air.cols.opcode_selector.is_lh row 0, air.cols.opcode_selector.is_lhu row 0,
            air.cols.opcode_selector.is_lw row 0, air.cols.opcode_selector.is_sb row 0,
            air.cols.opcode_selector.is_sh row 0, air.cols.opcode_selector.is_sw row 0]),
        (-air.cols.is_alu_instruction row 0,
          [3, air.cols.instruction.opcode row 0, air.cols.op_a_access.access.value_0 row 0,
            air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0,
            air.cols.op_a_access.access.value_3 row 0, air.cols.op_b_access.value_0 row 0,
            air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0,
            air.cols.op_b_access.value_3 row 0, air.cols.op_c_access.value_0 row 0,
            air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0,
            air.cols.op_c_access.value_3 row 0]),
        (-air.cols.branching row 0,
          [3, 0, air.cols.opcode_specific.specific_14 row 0, air.cols.opcode_specific.specific_15 row 0,
            air.cols.opcode_specific.specific_16 row 0, air.cols.opcode_specific.specific_17 row 0,
            air.cols.opcode_specific.specific_0 row 0, air.cols.opcode_specific.specific_1 row 0,
            air.cols.opcode_specific.specific_2 row 0, air.cols.opcode_specific.specific_3 row 0,
            air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0,
            air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-air.cols.is_branch_instruction row 0,
          [3, air.cols.use_signed_comparison row 0 * 8 + (1 - air.cols.use_signed_comparison row 0) * 9,
            air.cols.opcode_specific.specific_30 row 0, 0, 0, 0, air.cols.op_a_access.access.value_0 row 0,
            air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0,
            air.cols.op_a_access.access.value_3 row 0, air.cols.op_b_access.value_0 row 0,
            air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0,
            air.cols.op_b_access.value_3 row 0]),
        (-air.cols.is_branch_instruction row 0,
          [3, air.cols.use_signed_comparison row 0 * 8 + (1 - air.cols.use_signed_comparison row 0) * 9,
            air.cols.opcode_specific.specific_29 row 0, 0, 0, 0, air.cols.op_b_access.value_0 row 0,
            air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0,
            air.cols.op_b_access.value_3 row 0, air.cols.op_a_access.access.value_0 row 0,
            air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0,
            air.cols.op_a_access.access.value_3 row 0]),
        (-air.cols.opcode_selector.is_jal row 0,
          [3, 0, air.cols.opcode_specific.specific_14 row 0, air.cols.opcode_specific.specific_15 row 0,
            air.cols.opcode_specific.specific_16 row 0, air.cols.opcode_specific.specific_17 row 0,
            air.cols.opcode_specific.specific_0 row 0, air.cols.opcode_specific.specific_1 row 0,
            air.cols.opcode_specific.specific_2 row 0, air.cols.opcode_specific.specific_3 row 0,
            air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0,
            air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-air.cols.opcode_selector.is_jalr row 0,
          [3, 0, air.cols.opcode_specific.specific_14 row 0, air.cols.opcode_specific.specific_15 row 0,
            air.cols.opcode_specific.specific_16 row 0, air.cols.opcode_specific.specific_17 row 0,
            air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0,
            air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0,
            air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0,
            air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-air.cols.opcode_selector.is_auipc row 0,
          [3, 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0,
            air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0,
            air.cols.opcode_specific.specific_0 row 0, air.cols.opcode_specific.specific_1 row 0,
            air.cols.opcode_specific.specific_2 row 0, air.cols.opcode_specific.specific_3 row 0,
            air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0,
            air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-air.cols.ecall_mul_send_to_table row 0,
          [7, air.cols.clk row 0, air.cols.op_a_access.prev_value_0 row 0,
            air.cols.op_b_access.value_0 row 0 + 256 * air.cols.op_b_access.value_1 row 0 +
                65536 * air.cols.op_b_access.value_2 row 0 +
              16777216 * air.cols.op_b_access.value_3 row 0,
            air.cols.op_c_access.value_0 row 0 + 256 * air.cols.op_c_access.value_1 row 0 +
                65536 * air.cols.op_c_access.value_2 row 0 +
              16777216 * air.cols.op_c_access.value_3 row 0]),
        (-air.cols.is_real row 0, [4, 8, air.cols.chunk row 0, 0, 0, 0]),
        (-air.cols.is_real row 0, [4, 8, air.cols.clk_16bit_limb row 0, 0, 0, 0]),
        (-air.cols.is_real row 0, [4, 7, 0, 0, air.cols.clk_8bit_limb row 0, 0])
      ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_CpuAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
    :
      CpuAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        CpuAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold CpuAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end CpuAir.ConstraintsAndBuses

namespace CpuAir.Interactions

  open RV32IM_Interactions

  def program_bus_entry (air : Valid_CpuAir FKB ExtF) (row : ℕ) :=
    (-air.cols.is_real row 0, #v[air.cols.pc row 0, air.cols.instruction.opcode row 0, air.cols.instruction.opcode row 0, air.cols.instruction.a_0 row 0, air.cols.instruction.a_1 row 0, air.cols.instruction.a_2 row 0, air.cols.instruction.a_3 row 0, air.cols.instruction.b_0 row 0, air.cols.instruction.b_1 row 0, air.cols.instruction.b_2 row 0, air.cols.instruction.b_3 row 0, air.cols.instruction.c_0 row 0, air.cols.instruction.c_1 row 0, air.cols.instruction.c_2 row 0, air.cols.instruction.c_3 row 0, air.cols.instruction.a_is_0 row 0, air.cols.opcode_selector.imm_b row 0, air.cols.opcode_selector.imm_c row 0, air.cols.opcode_selector.is_alu row 0, air.cols.opcode_selector.is_ecall row 0, air.cols.opcode_selector.is_lb row 0, air.cols.opcode_selector.is_lbu row 0, air.cols.opcode_selector.is_lh row 0, air.cols.opcode_selector.is_lhu row 0, air.cols.opcode_selector.is_lw row 0, air.cols.opcode_selector.is_sb row 0, air.cols.opcode_selector.is_sh row 0, air.cols.opcode_selector.is_sw row 0, air.cols.opcode_selector.is_beq row 0, air.cols.opcode_selector.is_bne row 0, air.cols.opcode_selector.is_blt row 0, air.cols.opcode_selector.is_bge row 0, air.cols.opcode_selector.is_bltu row 0, air.cols.opcode_selector.is_bgeu row 0, air.cols.opcode_selector.is_jalr row 0, air.cols.opcode_selector.is_jal row 0, air.cols.opcode_selector.is_auipc row 0, air.cols.opcode_selector.is_unimpl row 0])

  def bus_row (air : Valid_CpuAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := List.map ProgramBusEntry.deserialise [
        program_bus_entry air row
      ],
      ALU := List.map ALUBusEntry.deserialise [
        (-air.cols.opcode_selector.is_alu row 0, #v[air.cols.instruction.opcode row 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-air.cols.branching row 0, #v[0, air.cols.opcode_specific.specific_14 row 0, air.cols.opcode_specific.specific_15 row 0, air.cols.opcode_specific.specific_16 row 0, air.cols.opcode_specific.specific_17 row 0, air.cols.opcode_specific.specific_0 row 0, air.cols.opcode_specific.specific_1 row 0, air.cols.opcode_specific.specific_2 row 0, air.cols.opcode_specific.specific_3 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-(air.cols.is_branch_instruction row 0), #v[9 - air.cols.opcode_selector.is_blt row 0 - air.cols.opcode_selector.is_bge row 0, air.cols.opcode_specific.specific_30 row 0, 0, 0, 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-(air.cols.is_branch_instruction row 0), #v[9 - air.cols.opcode_selector.is_blt row 0 - air.cols.opcode_selector.is_bge row 0, air.cols.opcode_specific.specific_29 row 0, 0, 0, 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0]),
        (-air.cols.opcode_selector.is_jal row 0, #v[0, air.cols.opcode_specific.specific_14 row 0, air.cols.opcode_specific.specific_15 row 0, air.cols.opcode_specific.specific_16 row 0, air.cols.opcode_specific.specific_17 row 0, air.cols.opcode_specific.specific_0 row 0, air.cols.opcode_specific.specific_1 row 0, air.cols.opcode_specific.specific_2 row 0, air.cols.opcode_specific.specific_3 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-air.cols.opcode_selector.is_jalr row 0, #v[0, air.cols.opcode_specific.specific_14 row 0, air.cols.opcode_specific.specific_15 row 0, air.cols.opcode_specific.specific_16 row 0, air.cols.opcode_specific.specific_17 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-air.cols.opcode_selector.is_auipc row 0, #v[0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0, air.cols.opcode_specific.specific_0 row 0, air.cols.opcode_specific.specific_1 row 0, air.cols.opcode_specific.specific_2 row 0, air.cols.opcode_specific.specific_3 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-(1 - air.cols.opcode_selector.imm_b row 0), #v[8, air.cols.op_b_access.diff_16bit_limb row 0, 0, 0, 0]),
        (-(1 - air.cols.opcode_selector.imm_b row 0), #v[7, 0, 0, air.cols.op_b_access.diff_8bit_limb row 0, 0]),
        (-(1 - air.cols.opcode_selector.imm_c row 0), #v[8, air.cols.op_c_access.diff_16bit_limb row 0, 0, 0, 0]),
        (-(1 - air.cols.opcode_selector.imm_c row 0), #v[7, 0, 0, air.cols.op_c_access.diff_8bit_limb row 0, 0]),
        (-air.cols.is_real row 0, #v[8, air.cols.op_a_access.access.diff_16bit_limb row 0, 0, 0, 0]),
        (-air.cols.is_real row 0, #v[7, 0, 0, air.cols.op_a_access.access.diff_8bit_limb row 0, 0]),
        (-air.cols.is_real row 0, #v[7, 0, 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0]),
        (-air.cols.is_real row 0, #v[7, 0, 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0]),
        (-air.cols.is_real row 0, #v[8, air.cols.chunk row 0, 0, 0, 0]),
        (-air.cols.is_real row 0, #v[8, air.cols.clk_16bit_limb row 0, 0, 0, 0]),
        (-air.cols.is_real row 0, #v[7, 0, 0, air.cols.clk_8bit_limb row 0, 0])
      ],
      Register := List.map RegisterBusEntry.deserialise [
        (-(1 - air.cols.opcode_selector.imm_b row 0), #v[air.cols.op_b_access.prev_chunk row 0, air.cols.op_b_access.prev_clk row 0, air.cols.instruction.b_0 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (  1 - air.cols.opcode_selector.imm_b row 0,  #v[air.cols.chunk row 0, 2 + air.cols.clk row 0, air.cols.instruction.b_0 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-(1 - air.cols.opcode_selector.imm_c row 0), #v[air.cols.op_c_access.prev_chunk row 0, air.cols.op_c_access.prev_clk row 0, air.cols.instruction.c_0 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (  1 - air.cols.opcode_selector.imm_c row 0,  #v[air.cols.chunk row 0, 1 + air.cols.clk row 0, air.cols.instruction.c_0 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-air.cols.is_real row 0, #v[air.cols.op_a_access.access.prev_chunk row 0, air.cols.op_a_access.access.prev_clk row 0, air.cols.instruction.a_0 row 0, air.cols.op_a_access.prev_value_0 row 0, air.cols.op_a_access.prev_value_1 row 0, air.cols.op_a_access.prev_value_2 row 0, air.cols.op_a_access.prev_value_3 row 0]),
        ( air.cols.is_real row 0, #v[air.cols.chunk row 0, 3 + air.cols.clk row 0, air.cols.instruction.a_0 row 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0])
      ]
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_CpuAir FKB ExtF) (row : ℕ) :
     RV32IM_Interactions.deserialise_bus_row (CpuAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      program_bus_entry,
      pico_encapsulation,
      add_comm (a := air.cols.clk row 0)
    ]
    simp [Valid_CpuCols.use_signed_comparison]
    omega

  @[simp]
  def CPU_bus_operations (air : Valid_CpuAir FKB ExtF) (row : ℕ) :=
    RV32IM.bus_operations (RV32IM_Interactions.deserialise_bus_row (CpuAir.ConstraintsAndBuses.raw_bus_row air row)) ++
    [ .WritePC (BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)) ]

end CpuAir.Interactions
