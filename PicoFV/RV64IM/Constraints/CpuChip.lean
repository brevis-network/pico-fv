import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.BusesV3
import PicoFV.RV64IM.Extraction.CpuChip
import PicoFV.RV64IM.Airs.CpuChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-! The 65 constraints and 17 messages of the Pico v3.1.1 CPU chip over named columns.
    Generated from `Extraction/CpuChip.lean` by renaming columns; each `constraint_i_equiv`
    proves the restatement equal to the extracted constraint. -/

namespace CpuChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_b row 0) * ((air.cols.op_b_access.access.value_0 row 0) - (air.cols.instruction.op_b_0 row 0))) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_b row 0) * ((air.cols.op_b_access.access.value_1 row 0) - (air.cols.instruction.op_b_1 row 0))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_b row 0) * ((air.cols.op_b_access.access.value_2 row 0) - ((air.cols.instruction.op_b_sign row 0) * 65535))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_b row 0) * ((air.cols.op_b_access.access.value_3 row 0) - ((air.cols.instruction.op_b_sign row 0) * 65535))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_c row 0) * ((air.cols.op_c_access.access.value_0 row 0) - (air.cols.instruction.op_c_0 row 0))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_c row 0) * ((air.cols.op_c_access.access.value_1 row 0) - (air.cols.instruction.op_c_1 row 0))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_c row 0) * ((air.cols.op_c_access.access.value_2 row 0) - ((air.cols.instruction.op_c_sign row 0) * 65535))) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.imm_c row 0) * ((air.cols.op_c_access.access.value_3 row 0) - ((air.cols.instruction.op_c_sign row 0) * 65535))) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.op_a_is_x0 row 0) * (air.cols.op_a_access.access.value_0 row 0)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.op_a_is_x0 row 0) * (air.cols.op_a_access.access.value_1 row 0)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.op_a_is_x0 row 0) * (air.cols.op_a_access.access.value_2 row 0)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.instruction.op_a_is_x0 row 0) * (air.cols.op_a_access.access.value_3 row 0)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) + (air.cols.opcode_selector.is_store row 0)) * ((air.cols.op_a_access.access.value_0 row 0) - (air.cols.op_a_access.prev_value_0 row 0))) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) + (air.cols.opcode_selector.is_store row 0)) * ((air.cols.op_a_access.access.value_1 row 0) - (air.cols.op_a_access.prev_value_1 row 0))) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) + (air.cols.opcode_selector.is_store row 0)) * ((air.cols.op_a_access.access.value_2 row 0) - (air.cols.op_a_access.prev_value_2 row 0))) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) + (air.cols.opcode_selector.is_store row 0)) * ((air.cols.op_a_access.access.value_3 row 0) - (air.cols.op_a_access.prev_value_3 row 0))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_alu_not_x0 row 0) - (((air.cols.is_real row 0) - ((((((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) + (air.cols.opcode_selector.is_ecall row 0)) + (air.cols.opcode_selector.is_memory row 0)) + (air.cols.opcode_selector.is_jal row 0)) + (air.cols.opcode_selector.is_jalr row 0))) * (1 - (air.cols.instruction.op_a_is_x0 row 0)))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        (((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) * (1 - (air.cols.opcode_selector.imm_c row 0))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.opcode_selector.is_beq row 0) * ((1 - (air.cols.a_lt_b row 0)) - (air.cols.a_gt_b row 0))) + ((air.cols.opcode_selector.is_bne row 0) * ((air.cols.a_lt_b row 0) + (air.cols.a_gt_b row 0)))) + (((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bltu row 0)) * (air.cols.a_lt_b row 0))) + (((air.cols.opcode_selector.is_bge row 0) + (air.cols.opcode_selector.is_bgeu row 0)) * (1 - (air.cols.a_lt_b row 0)))) * (((1 * (air.cols.next_pc_0 row 0)) + (65536 * (air.cols.next_pc_1 row 0))) - (((((1 * (air.cols.pc_0 row 0)) + (65536 * (air.cols.pc_1 row 0))) + (air.cols.op_c_access.access.value_0 row 0)) + ((air.cols.op_c_access.access.value_1 row 0) * 65536)) - ((air.cols.instruction.op_c_sign row 0) * 33554430)))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.opcode_selector.is_jal row 0) + (air.cols.opcode_selector.is_jalr row 0)) * (1 - (air.cols.instruction.op_a_is_x0 row 0))) * ((0 + ((air.cols.pc_carry row 0) * 65536)) - (((air.cols.pc_0 row 0) + 4) - (air.cols.op_a_access.access.value_0 row 0)))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.opcode_selector.is_jal row 0) + (air.cols.opcode_selector.is_jalr row 0)) * (1 - (air.cols.instruction.op_a_is_x0 row 0))) * ((air.cols.op_a_access.access.value_1 row 0) - ((air.cols.pc_1 row 0) + (air.cols.pc_carry row 0)))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.opcode_selector.is_jal row 0) + (air.cols.opcode_selector.is_jalr row 0)) * (1 - (air.cols.instruction.op_a_is_x0 row 0))) * (air.cols.op_a_access.access.value_2 row 0)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.opcode_selector.is_jal row 0) + (air.cols.opcode_selector.is_jalr row 0)) * (air.cols.op_a_access.access.value_3 row 0)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_jal row 0) * (((1 * (air.cols.next_pc_0 row 0)) + (65536 * (air.cols.next_pc_1 row 0))) - (((((1 * (air.cols.pc_0 row 0)) + (65536 * (air.cols.pc_1 row 0))) + (air.cols.op_b_access.access.value_0 row 0)) + ((air.cols.op_b_access.access.value_1 row 0) * 65536)) - ((air.cols.instruction.op_b_sign row 0) * 33554430)))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_jal row 0) * (1 - (air.cols.opcode_selector.imm_b row 0))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.jalr_lsb row 0) * ((air.cols.jalr_lsb row 0) - 1)) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_jalr row 0) * ((((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921) * ((((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_jalr row 0) * ((((((0 + (air.cols.op_b_access.access.value_1 row 0)) + (air.cols.op_c_access.access.value_1 row 0)) + (((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921)) - (air.cols.next_pc_1 row 0)) * 2130673921) * ((((((0 + (air.cols.op_b_access.access.value_1 row 0)) + (air.cols.op_c_access.access.value_1 row 0)) + (((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921)) - (air.cols.next_pc_1 row 0)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_jalr row 0) * (((((0 + (air.cols.op_b_access.access.value_2 row 0)) + (air.cols.op_c_access.access.value_2 row 0)) + (((((0 + (air.cols.op_b_access.access.value_1 row 0)) + (air.cols.op_c_access.access.value_1 row 0)) + (((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921)) - (air.cols.next_pc_1 row 0)) * 2130673921)) * 2130673921) * (((((0 + (air.cols.op_b_access.access.value_2 row 0)) + (air.cols.op_c_access.access.value_2 row 0)) + (((((0 + (air.cols.op_b_access.access.value_1 row 0)) + (air.cols.op_c_access.access.value_1 row 0)) + (((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921)) - (air.cols.next_pc_1 row 0)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_jalr row 0) * (((((0 + (air.cols.op_b_access.access.value_3 row 0)) + (air.cols.op_c_access.access.value_3 row 0)) + ((((0 + (air.cols.op_b_access.access.value_2 row 0)) + (air.cols.op_c_access.access.value_2 row 0)) + (((((0 + (air.cols.op_b_access.access.value_1 row 0)) + (air.cols.op_c_access.access.value_1 row 0)) + (((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921)) - (air.cols.next_pc_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) * (((((0 + (air.cols.op_b_access.access.value_3 row 0)) + (air.cols.op_c_access.access.value_3 row 0)) + ((((0 + (air.cols.op_b_access.access.value_2 row 0)) + (air.cols.op_c_access.access.value_2 row 0)) + (((((0 + (air.cols.op_b_access.access.value_1 row 0)) + (air.cols.op_c_access.access.value_1 row 0)) + (((((0 + (air.cols.op_b_access.access.value_0 row 0)) + (air.cols.op_c_access.access.value_0 row 0)) - (air.cols.next_pc_0 row 0)) - (air.cols.jalr_lsb row 0)) * 2130673921)) - (air.cols.next_pc_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.opcode_selector.is_ecall row 0) - 1) * (air.cols.is_halt row 0)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.opcode_selector.is_ecall row 0) - 1) * (air.cols.num_extra_clk row 0)) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_halt row 0) * ((air.cols.is_last row 0) - 1)) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_halt row 0) * (air.cols.next_pc_0 row 0)) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_halt row 0) * (air.cols.next_pc_1 row 0)) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isFirstRow air row) * ((air.cols.clk row 0) - 4)) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.is_real row 0) - (((((air.cols.opcode_selector.is_beq row 0) * ((1 - (air.cols.a_lt_b row 0)) - (air.cols.a_gt_b row 0))) + ((air.cols.opcode_selector.is_bne row 0) * ((air.cols.a_lt_b row 0) + (air.cols.a_gt_b row 0)))) + (((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bltu row 0)) * (air.cols.a_lt_b row 0))) + (((air.cols.opcode_selector.is_bge row 0) + (air.cols.opcode_selector.is_bgeu row 0)) * (1 - (air.cols.a_lt_b row 0))))) - (air.cols.opcode_selector.is_jal row 0)) - (air.cols.opcode_selector.is_jalr row 0)) - (air.cols.is_halt row 0)) * (((1 * (air.cols.next_pc_0 row 0)) + (65536 * (air.cols.next_pc_1 row 0))) - (((1 * (air.cols.pc_0 row 0)) + (65536 * (air.cols.pc_1 row 0))) + 4))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isFirstRow air row) * ((air.public_values 40) - (air.cols.pc_0 row 0))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isFirstRow air row) * ((air.public_values 41) - (air.cols.pc_1 row 0))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isFirstRow air row) * (air.public_values 42)) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_last row 0) * ((air.public_values 43) - (air.cols.next_pc_0 row 0))) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_last row 0) * ((air.public_values 44) - (air.cols.next_pc_1 row 0))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_last row 0) * (air.public_values 45)) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isFirstRow air row) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isTransitionRow air row) * ((air.cols.is_real row 1) * ((air.cols.pc_0 row 1) - (air.cols.next_pc_0 row 0)))) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isTransitionRow air row) * ((air.cols.is_real row 1) * ((air.cols.pc_1 row 1) - (air.cols.next_pc_1 row 0)))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isTransitionRow air row) * ((air.cols.is_real row 1) * ((air.cols.clk row 1) - (((air.cols.clk row 0) + 4) + (air.cols.num_extra_clk row 0))))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isTransitionRow air row) * ((1 - (air.cols.is_real row 0)) * (air.cols.is_real row 1))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isTransitionRow air row) * ((air.cols.is_last row 0) - ((air.cols.is_real row 0) - (air.cols.is_real row 1)))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isLastRow air row) * ((air.cols.is_last row 0) - (air.cols.is_real row 0))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * ((air.cols.opcode_selector.imm_b row 0) - 1)) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * ((air.cols.opcode_selector.imm_c row 0) - 1)) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_ecall row 0)) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_memory row 0)) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_store row 0)) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_beq row 0)) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_bne row 0)) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_blt row 0)) = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_bge row 0)) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_bltu row 0)) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_bgeu row 0)) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_jalr row 0)) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((1 - (air.cols.is_real row 0)) * (air.cols.opcode_selector.is_jal row 0)) = 0

      @[simp]
      lemma constraint_64_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_64 air row ↔ constraint_64 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def row_constraint_list (air : Valid_CpuChip F ExtF) (row : ℕ) : List Prop :=
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
          constraint_64 air row
        ]

    end row_constraints

    section row_buses

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_CpuChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [
          -- Looking Program (Regional)
          ((air.cols.is_real row 0), [2, (air.cols.pc_0 row 0), (air.cols.pc_1 row 0), (air.cols.instruction.opcode row 0), (air.cols.instruction.opcode row 0), (air.cols.instruction.op_a_0 row 0), (air.cols.instruction.op_b_0 row 0), (air.cols.instruction.op_b_1 row 0), (air.cols.instruction.op_b_sign row 0), (air.cols.instruction.op_c_0 row 0), (air.cols.instruction.op_c_1 row 0), (air.cols.instruction.op_c_sign row 0), (air.cols.instruction.op_a_is_x0 row 0), (air.cols.opcode_selector.imm_b row 0), (air.cols.opcode_selector.imm_c row 0), (air.cols.opcode_selector.is_ecall row 0), (air.cols.opcode_selector.is_memory row 0), (air.cols.opcode_selector.is_store row 0), (air.cols.opcode_selector.is_beq row 0), (air.cols.opcode_selector.is_bne row 0), (air.cols.opcode_selector.is_blt row 0), (air.cols.opcode_selector.is_bge row 0), (air.cols.opcode_selector.is_bltu row 0), (air.cols.opcode_selector.is_bgeu row 0), (air.cols.opcode_selector.is_jalr row 0), (air.cols.opcode_selector.is_jal row 0), (air.cols.pc_carry row 0)]),
          -- Looking Byte (Regional)
          ((1 - (air.cols.opcode_selector.imm_b row 0)), [5, 8, (air.cols.op_b_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          -- Looking Byte (Regional)
          ((1 - (air.cols.opcode_selector.imm_b row 0)), [5, 9, (air.cols.op_b_access.access.diff_hi9 row 0), 0, 9, 0]),
          -- Looking Memory (Regional)
          ((1 - (air.cols.opcode_selector.imm_b row 0)), [1, (air.public_values 48), ((((air.cols.clk row 0) + 2) - ((air.cols.op_b_access.access.diff_16bit_limb row 0) + ((air.cols.op_b_access.access.diff_hi9 row 0) * 65536))) - 1), (air.cols.instruction.op_b_0 row 0), 0, 0, (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0)]),
          -- Looked Memory (Regional)
          ((0 - (1 - (air.cols.opcode_selector.imm_b row 0))), [1, (air.public_values 48), ((air.cols.clk row 0) + 2), (air.cols.instruction.op_b_0 row 0), 0, 0, (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0)]),
          -- Looking Byte (Regional)
          ((1 - (air.cols.opcode_selector.imm_c row 0)), [5, 8, (air.cols.op_c_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          -- Looking Byte (Regional)
          ((1 - (air.cols.opcode_selector.imm_c row 0)), [5, 9, (air.cols.op_c_access.access.diff_hi9 row 0), 0, 9, 0]),
          -- Looking Memory (Regional)
          ((1 - (air.cols.opcode_selector.imm_c row 0)), [1, (air.public_values 48), ((((air.cols.clk row 0) + 1) - ((air.cols.op_c_access.access.diff_16bit_limb row 0) + ((air.cols.op_c_access.access.diff_hi9 row 0) * 65536))) - 1), (air.cols.instruction.op_c_0 row 0), 0, 0, (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0)]),
          -- Looked Memory (Regional)
          ((0 - (1 - (air.cols.opcode_selector.imm_c row 0))), [1, (air.public_values 48), ((air.cols.clk row 0) + 1), (air.cols.instruction.op_c_0 row 0), 0, 0, (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0)]),
          -- Looking Byte (Regional)
          ((air.cols.is_real row 0), [5, 8, (air.cols.op_a_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          -- Looking Byte (Regional)
          ((air.cols.is_real row 0), [5, 9, (air.cols.op_a_access.access.diff_hi9 row 0), 0, 9, 0]),
          -- Looking Memory (Regional)
          ((air.cols.is_real row 0), [1, (air.public_values 48), ((((air.cols.clk row 0) + 3) - ((air.cols.op_a_access.access.diff_16bit_limb row 0) + ((air.cols.op_a_access.access.diff_hi9 row 0) * 65536))) - 1), (air.cols.instruction.op_a_0 row 0), 0, 0, (air.cols.op_a_access.prev_value_0 row 0), (air.cols.op_a_access.prev_value_1 row 0), (air.cols.op_a_access.prev_value_2 row 0), (air.cols.op_a_access.prev_value_3 row 0)]),
          -- Looked Memory (Regional)
          ((0 - (air.cols.is_real row 0)), [1, (air.public_values 48), ((air.cols.clk row 0) + 3), (air.cols.instruction.op_a_0 row 0), 0, 0, (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0)]),
          -- Looking Memory (Regional)
          ((air.cols.opcode_selector.is_memory row 0), [1, (air.cols.instruction.opcode row 0), (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0), (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0), (air.cols.instruction.op_a_is_x0 row 0), (air.cols.opcode_selector.is_memory row 0), (air.public_values 48), (air.cols.clk row 0)]),
          -- Looking Alu (Regional)
          ((air.cols.is_alu_not_x0 row 0), [4, (air.cols.instruction.opcode row 0), (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0), (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0)]),
          -- Looking Alu (Regional)
          (((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)), [4, (((((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bge row 0)) * 8) + ((1 - ((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bge row 0))) * 9)) + 256), (air.cols.a_lt_b row 0), (air.cols.a_gt_b row 0), 0, 0, (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0)]),
          -- Looking Ecall (Regional)
          ((air.cols.opcode_selector.is_ecall row 0), [13, (air.public_values 48), (air.cols.clk row 0), (air.cols.op_a_access.prev_value_0 row 0), (air.cols.op_a_access.prev_value_1 row 0), (air.cols.op_a_access.prev_value_2 row 0), (air.cols.op_a_access.prev_value_3 row 0), (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0), (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0), (air.cols.num_extra_clk row 0), (air.cols.is_halt row 0)])
        ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_CpuChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
    :
      CpuChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end CpuChip.ConstraintsAndBuses
