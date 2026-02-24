import PicoFV.Airs.CPUAir
import PicoFV.RVSail.RV32IM.Operations

set_option maxHeartbeats 1_000_000_000

namespace CpuAir.constraints

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[pico_encapsulation]
      def constraint_0 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_0 row 0 - air.cols.instruction.b_0 row 0) = 0

      @[pico_encapsulation]
      def constraint_1 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_1 row 0 - air.cols.instruction.b_1 row 0) = 0

      @[pico_encapsulation]
      def constraint_2 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_2 row 0 - air.cols.instruction.b_2 row 0) = 0

      @[pico_encapsulation]
      def constraint_3 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_b row 0 * (air.cols.op_b_access.value_3 row 0 - air.cols.instruction.b_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_4 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_0 row 0 - air.cols.instruction.c_0 row 0) = 0

      @[pico_encapsulation]
      def constraint_5 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_1 row 0 - air.cols.instruction.c_1 row 0) = 0

      @[pico_encapsulation]
      def constraint_6 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_2 row 0 - air.cols.instruction.c_2 row 0) = 0

      @[pico_encapsulation]
      def constraint_7 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.imm_c row 0 * (air.cols.op_c_access.value_3 row 0 - air.cols.instruction.c_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_8 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (1 - air.cols.opcode_selector.imm_b row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_9 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (air.cols.op_b_access.compare_clk row 0 * (air.cols.op_b_access.compare_clk row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_10 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (air.cols.op_b_access.compare_clk row 0 * (air.cols.chunk row 0 - air.cols.op_b_access.prev_chunk row 0)) = 0

      @[pico_encapsulation]
      def constraint_11 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_b row 0) * (air.cols.op_b_access.compare_clk row 0 * (air.cols.clk row 0 + 2) + (1 - air.cols.op_b_access.compare_clk row 0) * air.cols.chunk row 0 - (air.cols.op_b_access.compare_clk row 0 * air.cols.op_b_access.prev_clk row 0 + (1 - air.cols.op_b_access.compare_clk row 0) * air.cols.op_b_access.prev_chunk row 0) - 1 - (air.cols.op_b_access.diff_16bit_limb row 0 + air.cols.op_b_access.diff_8bit_limb row 0 * 65536)) = 0

      @[pico_encapsulation]
      def constraint_12 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (1 - air.cols.opcode_selector.imm_c row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_13 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (air.cols.op_c_access.compare_clk row 0 * (air.cols.op_c_access.compare_clk row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_14 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (air.cols.op_c_access.compare_clk row 0 * (air.cols.chunk row 0 - air.cols.op_c_access.prev_chunk row 0)) = 0

      @[pico_encapsulation]
      def constraint_15 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.opcode_selector.imm_c row 0) * (air.cols.op_c_access.compare_clk row 0 * (air.cols.clk row 0 + 1) + (1 - air.cols.op_c_access.compare_clk row 0) * air.cols.chunk row 0 - (air.cols.op_c_access.compare_clk row 0 * air.cols.op_c_access.prev_clk row 0 + (1 - air.cols.op_c_access.compare_clk row 0) * air.cols.op_c_access.prev_chunk row 0) - 1 - (air.cols.op_c_access.diff_16bit_limb row 0 + air.cols.op_c_access.diff_8bit_limb row 0 * 65536)) = 0

      @[pico_encapsulation]
      def constraint_16 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_0 row 0 = 0

      @[pico_encapsulation]
      def constraint_17 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_1 row 0 = 0

      @[pico_encapsulation]
      def constraint_18 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_2 row 0 = 0

      @[pico_encapsulation]
      def constraint_19 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.instruction.a_is_0 row 0 * air.cols.op_a_access.access.value_3 row 0 = 0

      @[pico_encapsulation]
      def constraint_20 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_real row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_21 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.op_a_access.access.compare_clk row 0 * (air.cols.op_a_access.access.compare_clk row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_22 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.op_a_access.access.compare_clk row 0 * (air.cols.chunk row 0 - air.cols.op_a_access.access.prev_chunk row 0)) = 0

      @[pico_encapsulation]
      def constraint_23 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.op_a_access.access.compare_clk row 0 * (air.cols.clk row 0 + 3) + (1 - air.cols.op_a_access.access.compare_clk row 0) * air.cols.chunk row 0 - (air.cols.op_a_access.access.compare_clk row 0 * air.cols.op_a_access.access.prev_clk row 0 + (1 - air.cols.op_a_access.access.compare_clk row 0) * air.cols.op_a_access.access.prev_chunk row 0) - 1 - (air.cols.op_a_access.access.diff_16bit_limb row 0 + air.cols.op_a_access.access.diff_8bit_limb row 0 * 65536)) = 0

      @[pico_encapsulation]
      def constraint_24 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 + air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0) * (air.cols.op_a_access.access.value_0 row 0 - air.cols.op_a_access.prev_value_0 row 0) = 0

      @[pico_encapsulation]
      def constraint_25 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 + air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0) * (air.cols.op_a_access.access.value_1 row 0 - air.cols.op_a_access.prev_value_1 row 0) = 0

      @[pico_encapsulation]
      def constraint_26 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 + air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0) * (air.cols.op_a_access.access.value_2 row 0 - air.cols.op_a_access.prev_value_2 row 0) = 0

      @[pico_encapsulation]
      def constraint_27 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 + air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 + air.cols.opcode_selector.is_sw row 0) * (air.cols.op_a_access.access.value_3 row 0 - air.cols.op_a_access.prev_value_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_28 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.branching row 0 * (1 * air.cols.opcode_specific.specific_0 row 0 + 256 * air.cols.opcode_specific.specific_1 row 0 + 65536 * air.cols.opcode_specific.specific_2 row 0 + 16777216 * air.cols.opcode_specific.specific_3 row 0 - air.cols.pc row 0) = 0

      @[pico_encapsulation]
      def constraint_29 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * air.cols.is_real row 1 * (air.cols.branching row 0 * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.pc row 1)) = 0

      @[pico_encapsulation]
      def constraint_30 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.branching row 0 * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.next_pc row 0)) = 0

      @[pico_encapsulation]
      def constraint_31 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_4 row 0 * (air.cols.opcode_specific.specific_4 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_32 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_33 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_6 row 0 * (air.cols.opcode_specific.specific_6 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_34 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_35 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_8 row 0 * (air.cols.opcode_specific.specific_8 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_36 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_37 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_38 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_39 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (0 + 1 * air.cols.opcode_specific.specific_4 row 0 + 2 * air.cols.opcode_specific.specific_5 row 0 + 4 * air.cols.opcode_specific.specific_6 row 0 + 8 * air.cols.opcode_specific.specific_7 row 0 + 16 * air.cols.opcode_specific.specific_8 row 0 + 32 * air.cols.opcode_specific.specific_9 row 0 + 64 * air.cols.opcode_specific.specific_10 row 0 + 128 * air.cols.opcode_specific.specific_11 row 0 - air.cols.opcode_specific.specific_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_40 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_11 row 0 = 0

      @[pico_encapsulation]
      def constraint_41 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (1 - (air.cols.opcode_specific.specific_12 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) - air.cols.opcode_specific.specific_13 row 0) = 0

      @[pico_encapsulation]
      def constraint_42 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_43 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_13 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_44 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_13 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_45 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_0 row 0 + air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_2 row 0)) = 0

      @[pico_encapsulation]
      def constraint_46 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_18 row 0 * (air.cols.opcode_specific.specific_18 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_47 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_19 row 0 * (air.cols.opcode_specific.specific_19 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_48 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_20 row 0 * (air.cols.opcode_specific.specific_20 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_49 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_21 row 0 * (air.cols.opcode_specific.specific_21 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_50 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_22 row 0 * (air.cols.opcode_specific.specific_22 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_51 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_23 row 0 * (air.cols.opcode_specific.specific_23 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_52 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_24 row 0 * (air.cols.opcode_specific.specific_24 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_53 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_25 row 0 * (air.cols.opcode_specific.specific_25 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_54 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (0 + 1 * air.cols.opcode_specific.specific_18 row 0 + 2 * air.cols.opcode_specific.specific_19 row 0 + 4 * air.cols.opcode_specific.specific_20 row 0 + 8 * air.cols.opcode_specific.specific_21 row 0 + 16 * air.cols.opcode_specific.specific_22 row 0 + 32 * air.cols.opcode_specific.specific_23 row 0 + 64 * air.cols.opcode_specific.specific_24 row 0 + 128 * air.cols.opcode_specific.specific_25 row 0 - air.cols.opcode_specific.specific_17 row 0) = 0

      @[pico_encapsulation]
      def constraint_55 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_25 row 0 = 0

      @[pico_encapsulation]
      def constraint_56 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (1 - (air.cols.opcode_specific.specific_26 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) - air.cols.opcode_specific.specific_27 row 0) = 0

      @[pico_encapsulation]
      def constraint_57 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_27 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_58 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_27 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_59 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_27 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_60 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0)) = 0

      @[pico_encapsulation]
      def constraint_61 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * air.cols.is_real row 1 * (air.cols.not_branching row 0 * (air.cols.pc row 0 + 4 - air.cols.pc row 1)) = 0

      @[pico_encapsulation]
      def constraint_62 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.not_branching row 0 * (air.cols.is_real row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_63 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.not_branching row 0 * (air.cols.pc row 0 + 4 - air.cols.next_pc row 0)) = 0

      @[pico_encapsulation]
      def constraint_64 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.branching row 0 + air.cols.not_branching row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_65 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.branching row 0 * (air.cols.branching row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_66 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * (air.cols.not_branching row 0 * (air.cols.not_branching row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_67 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_beq row 0 * air.cols.branching row 0 * (air.cols.opcode_specific.specific_28 row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_68 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_beq row 0 * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_69 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_bne row 0 * air.cols.branching row 0 * (air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_70 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_bne row 0 * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_28 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_71 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bltu row 0) * air.cols.branching row 0) * (air.cols.opcode_specific.specific_30 row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_72 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bltu row 0) * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_73 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.branching row 0) * (air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_28 row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_74 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bgeu row 0) * ((air.cols.branching row 0 - 1) * (air.cols.opcode_specific.specific_30 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_75 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_0 row 0 - air.cols.op_b_access.value_0 row 0) = 0

      @[pico_encapsulation]
      def constraint_76 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_1 row 0 - air.cols.op_b_access.value_1 row 0) = 0

      @[pico_encapsulation]
      def constraint_77 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_2 row 0 - air.cols.op_b_access.value_2 row 0) = 0

      @[pico_encapsulation]
      def constraint_78 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0) * air.cols.opcode_specific.specific_28 row 0) * (air.cols.op_a_access.access.value_3 row 0 - air.cols.op_b_access.value_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_79 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 - 1) * air.cols.branching row 0 = 0

      @[pico_encapsulation]
      def constraint_80 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * ((air.cols.instruction.a_is_0 row 0 - 1) * (1 * air.cols.op_a_access.access.value_0 row 0 + 256 * air.cols.op_a_access.access.value_1 row 0 + 65536 * air.cols.op_a_access.access.value_2 row 0 + 16777216 * air.cols.op_a_access.access.value_3 row 0 - (air.cols.pc row 0 + 4))) = 0

      @[pico_encapsulation]
      def constraint_81 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (1 * air.cols.opcode_specific.specific_0 row 0 + 256 * air.cols.opcode_specific.specific_1 row 0 + 65536 * air.cols.opcode_specific.specific_2 row 0 + 16777216 * air.cols.opcode_specific.specific_3 row 0 - air.cols.pc row 0) = 0

      @[pico_encapsulation]
      def constraint_82 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * air.cols.is_real row 1 * ((air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.pc row 1)) = 0

      @[pico_encapsulation]
      def constraint_83 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * ((air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 * air.cols.opcode_specific.specific_14 row 0 + 256 * air.cols.opcode_specific.specific_15 row 0 + 65536 * air.cols.opcode_specific.specific_16 row 0 + 16777216 * air.cols.opcode_specific.specific_17 row 0 - air.cols.next_pc row 0)) = 0

      @[pico_encapsulation]
      def constraint_84 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_28 row 0 * (air.cols.opcode_specific.specific_28 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_85 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_29 row 0 * (air.cols.opcode_specific.specific_29 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_86 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_30 row 0 * (air.cols.opcode_specific.specific_30 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_87 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_31 row 0 * (air.cols.opcode_specific.specific_31 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_88 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_32 row 0 * (air.cols.opcode_specific.specific_32 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_89 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_33 row 0 * (air.cols.opcode_specific.specific_33 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_90 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_34 row 0 * (air.cols.opcode_specific.specific_34 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_91 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_35 row 0 * (air.cols.opcode_specific.specific_35 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_92 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (0 + 1 * air.cols.opcode_specific.specific_28 row 0 + 2 * air.cols.opcode_specific.specific_29 row 0 + 4 * air.cols.opcode_specific.specific_30 row 0 + 8 * air.cols.opcode_specific.specific_31 row 0 + 16 * air.cols.opcode_specific.specific_32 row 0 + 32 * air.cols.opcode_specific.specific_33 row 0 + 64 * air.cols.opcode_specific.specific_34 row 0 + 128 * air.cols.opcode_specific.specific_35 row 0 - air.cols.op_a_access.access.value_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_93 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_35 row 0 = 0

      @[pico_encapsulation]
      def constraint_94 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 - (air.cols.opcode_specific.specific_36 row 0 * (0 + air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 + air.cols.opcode_specific.specific_31 row 0 + air.cols.opcode_specific.specific_32 row 0 + air.cols.opcode_specific.specific_33 row 0 + air.cols.opcode_specific.specific_34 row 0 - 7)) - air.cols.opcode_specific.specific_37 row 0) = 0

      @[pico_encapsulation]
      def constraint_95 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_37 row 0 * (air.cols.opcode_specific.specific_37 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_96 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_37 row 0 * (0 + air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0 + air.cols.opcode_specific.specific_31 row 0 + air.cols.opcode_specific.specific_32 row 0 + air.cols.opcode_specific.specific_33 row 0 + air.cols.opcode_specific.specific_34 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_97 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_37 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_98 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_37 row 0 * (air.cols.op_a_access.access.value_0 row 0 + air.cols.op_a_access.access.value_1 row 0 + air.cols.op_a_access.access.value_2 row 0)) = 0

      @[pico_encapsulation]
      def constraint_99 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_4 row 0 * (air.cols.opcode_specific.specific_4 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_100 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_101 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_6 row 0 * (air.cols.opcode_specific.specific_6 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_102 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_103 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_8 row 0 * (air.cols.opcode_specific.specific_8 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_104 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_105 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_106 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_107 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (0 + 1 * air.cols.opcode_specific.specific_4 row 0 + 2 * air.cols.opcode_specific.specific_5 row 0 + 4 * air.cols.opcode_specific.specific_6 row 0 + 8 * air.cols.opcode_specific.specific_7 row 0 + 16 * air.cols.opcode_specific.specific_8 row 0 + 32 * air.cols.opcode_specific.specific_9 row 0 + 64 * air.cols.opcode_specific.specific_10 row 0 + 128 * air.cols.opcode_specific.specific_11 row 0 - air.cols.opcode_specific.specific_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_108 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * air.cols.opcode_specific.specific_11 row 0 = 0

      @[pico_encapsulation]
      def constraint_109 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (1 - (air.cols.opcode_specific.specific_12 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) - air.cols.opcode_specific.specific_13 row 0) = 0

      @[pico_encapsulation]
      def constraint_110 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_111 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_13 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_112 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * air.cols.opcode_specific.specific_13 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_113 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_jal row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_0 row 0 + air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_2 row 0)) = 0

      @[pico_encapsulation]
      def constraint_114 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_18 row 0 * (air.cols.opcode_specific.specific_18 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_115 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_19 row 0 * (air.cols.opcode_specific.specific_19 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_116 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_20 row 0 * (air.cols.opcode_specific.specific_20 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_117 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_21 row 0 * (air.cols.opcode_specific.specific_21 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_118 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_22 row 0 * (air.cols.opcode_specific.specific_22 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_119 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_23 row 0 * (air.cols.opcode_specific.specific_23 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_120 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_24 row 0 * (air.cols.opcode_specific.specific_24 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_121 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_25 row 0 * (air.cols.opcode_specific.specific_25 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_122 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (0 + 1 * air.cols.opcode_specific.specific_18 row 0 + 2 * air.cols.opcode_specific.specific_19 row 0 + 4 * air.cols.opcode_specific.specific_20 row 0 + 8 * air.cols.opcode_specific.specific_21 row 0 + 16 * air.cols.opcode_specific.specific_22 row 0 + 32 * air.cols.opcode_specific.specific_23 row 0 + 64 * air.cols.opcode_specific.specific_24 row 0 + 128 * air.cols.opcode_specific.specific_25 row 0 - air.cols.opcode_specific.specific_17 row 0) = 0

      @[pico_encapsulation]
      def constraint_123 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_25 row 0 = 0

      @[pico_encapsulation]
      def constraint_124 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (1 - (air.cols.opcode_specific.specific_26 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) - air.cols.opcode_specific.specific_27 row 0) = 0

      @[pico_encapsulation]
      def constraint_125 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_27 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_126 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_27 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_127 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * air.cols.opcode_specific.specific_27 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_128 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0) * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0)) = 0

      @[pico_encapsulation]
      def constraint_129 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (1 * air.cols.opcode_specific.specific_0 row 0 + 256 * air.cols.opcode_specific.specific_1 row 0 + 65536 * air.cols.opcode_specific.specific_2 row 0 + 16777216 * air.cols.opcode_specific.specific_3 row 0 - air.cols.pc row 0) = 0

      @[pico_encapsulation]
      def constraint_130 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_4 row 0 * (air.cols.opcode_specific.specific_4 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_131 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_132 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_6 row 0 * (air.cols.opcode_specific.specific_6 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_133 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_134 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_8 row 0 * (air.cols.opcode_specific.specific_8 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_135 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_136 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_137 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[pico_encapsulation]
    def constraint_138 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (0 + 1 * air.cols.opcode_specific.specific_4 row 0 + 2 * air.cols.opcode_specific.specific_5 row 0 + 4 * air.cols.opcode_specific.specific_6 row 0 + 8 * air.cols.opcode_specific.specific_7 row 0 + 16 * air.cols.opcode_specific.specific_8 row 0 + 32 * air.cols.opcode_specific.specific_9 row 0 + 64 * air.cols.opcode_specific.specific_10 row 0 + 128 * air.cols.opcode_specific.specific_11 row 0 - air.cols.opcode_specific.specific_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_139 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * air.cols.opcode_specific.specific_11 row 0 = 0

      @[pico_encapsulation]
      def constraint_140 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (1 - (air.cols.opcode_specific.specific_12 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) - air.cols.opcode_specific.specific_13 row 0) = 0

      @[pico_encapsulation]
      def constraint_141 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_142 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_13 row 0 * (0 + air.cols.opcode_specific.specific_4 row 0 + air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_6 row 0 + air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_8 row 0 + air.cols.opcode_specific.specific_9 row 0 + air.cols.opcode_specific.specific_10 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_143 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * air.cols.opcode_specific.specific_13 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_144 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_auipc row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_0 row 0 + air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_2 row 0)) = 0

      @[pico_encapsulation]
      def constraint_145 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_mul_send_to_table row 0 - air.cols.op_a_access.prev_value_1 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0

      @[pico_encapsulation]
      def constraint_146 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_0 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 3)) - air.cols.opcode_specific.specific_1 row 0) = 0

      @[pico_encapsulation]
      def constraint_147 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_1 row 0 * (air.cols.opcode_specific.specific_1 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_148 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 3)) = 0

      @[pico_encapsulation]
      def constraint_149 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_2 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 240)) - air.cols.opcode_specific.specific_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_150 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_3 row 0 * (air.cols.opcode_specific.specific_3 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_151 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_3 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 240)) = 0

      @[pico_encapsulation]
      def constraint_152 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_0 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_153 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_1 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_154 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_2 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_155 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_1 row 0 * (air.cols.op_a_access.access.value_3 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_156 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_0 row 0 - air.cols.op_a_access.prev_value_0 row 0)) = 0

      @[pico_encapsulation]
      def constraint_157 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_1 row 0 - air.cols.op_a_access.prev_value_1 row 0)) = 0

      @[pico_encapsulation]
      def constraint_158 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_2 row 0 - air.cols.op_a_access.prev_value_2 row 0)) = 0

      @[pico_encapsulation]
      def constraint_159 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * ((air.cols.opcode_specific.specific_1 row 0 + air.cols.opcode_specific.specific_3 row 0 - 1) * (air.cols.op_a_access.access.value_3 row 0 - air.cols.op_a_access.prev_value_3 row 0)) = 0

      @[pico_encapsulation]
      def constraint_160 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 - (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 + air.cols.opcode_specific.specific_9 row 0)) = 0

      @[pico_encapsulation]
      def constraint_161 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_18 row 0 * (air.cols.opcode_specific.specific_18 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_162 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_19 row 0 * (air.cols.opcode_specific.specific_19 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_163 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_20 row 0 * (air.cols.opcode_specific.specific_20 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_164 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_21 row 0 * (air.cols.opcode_specific.specific_21 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_165 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_22 row 0 * (air.cols.opcode_specific.specific_22 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_166 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_23 row 0 * (air.cols.opcode_specific.specific_23 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_167 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_24 row 0 * (air.cols.opcode_specific.specific_24 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_168 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_25 row 0 * (air.cols.opcode_specific.specific_25 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_169 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (0 + 1 * air.cols.opcode_specific.specific_18 row 0 + 2 * air.cols.opcode_specific.specific_19 row 0 + 4 * air.cols.opcode_specific.specific_20 row 0 + 8 * air.cols.opcode_specific.specific_21 row 0 + 16 * air.cols.opcode_specific.specific_22 row 0 + 32 * air.cols.opcode_specific.specific_23 row 0 + 64 * air.cols.opcode_specific.specific_24 row 0 + 128 * air.cols.opcode_specific.specific_25 row 0 - air.cols.opcode_specific.specific_31 row 0) = 0

      @[pico_encapsulation]
      def constraint_170 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * air.cols.opcode_specific.specific_25 row 0 = 0

      @[pico_encapsulation]
      def constraint_171 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (1 - (air.cols.opcode_specific.specific_26 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) - air.cols.opcode_specific.specific_27 row 0) = 0

      @[pico_encapsulation]
      def constraint_172 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_27 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_173 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_27 row 0 * (0 + air.cols.opcode_specific.specific_18 row 0 + air.cols.opcode_specific.specific_19 row 0 + air.cols.opcode_specific.specific_20 row 0 + air.cols.opcode_specific.specific_21 row 0 + air.cols.opcode_specific.specific_22 row 0 + air.cols.opcode_specific.specific_23 row 0 + air.cols.opcode_specific.specific_24 row 0 - 7)) = 0

      @[pico_encapsulation]
      def constraint_174 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * air.cols.opcode_specific.specific_27 row 0 * 0 = 0

      @[pico_encapsulation]
      def constraint_175 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.ecall_range_check_operand row 0 * (air.cols.opcode_specific.specific_27 row 0 * (air.cols.opcode_specific.specific_28 row 0 + air.cols.opcode_specific.specific_29 row 0 + air.cols.opcode_specific.specific_30 row 0)) = 0

      @[pico_encapsulation]
      def constraint_176 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_6 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 16)) - air.cols.opcode_specific.specific_7 row 0) = 0

      @[pico_encapsulation]
      def constraint_177 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.opcode_specific.specific_7 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_178 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 16)) = 0

      @[pico_encapsulation]
      def constraint_179 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_8 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 26)) - air.cols.opcode_specific.specific_9 row 0) = 0

      @[pico_encapsulation]
      def constraint_180 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.opcode_specific.specific_9 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_181 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 26)) = 0

      @[pico_encapsulation]
      def constraint_182 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_10 row 0 * (air.cols.opcode_specific.specific_10 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_183 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_11 row 0 * (air.cols.opcode_specific.specific_11 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_184 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_12 row 0 * (air.cols.opcode_specific.specific_12 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_185 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_13 row 0 * (air.cols.opcode_specific.specific_13 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_186 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_14 row 0 * (air.cols.opcode_specific.specific_14 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_187 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_15 row 0 * (air.cols.opcode_specific.specific_15 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_188 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_16 row 0 * (air.cols.opcode_specific.specific_16 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_189 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_17 row 0 * (air.cols.opcode_specific.specific_17 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_190 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (0 + air.cols.opcode_specific.specific_10 row 0 + air.cols.opcode_specific.specific_11 row 0 + air.cols.opcode_specific.specific_12 row 0 + air.cols.opcode_specific.specific_13 row 0 + air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0 + air.cols.opcode_specific.specific_17 row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_191 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0))) * (0 + air.cols.opcode_specific.specific_10 row 0 + air.cols.opcode_specific.specific_11 row 0 + air.cols.opcode_specific.specific_12 row 0 + air.cols.opcode_specific.specific_13 row 0 + air.cols.opcode_specific.specific_14 row 0 + air.cols.opcode_specific.specific_15 row 0 + air.cols.opcode_specific.specific_16 row 0 + air.cols.opcode_specific.specific_17 row 0) = 0

      @[pico_encapsulation]
      def constraint_192 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_10 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_193 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_11 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_194 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_12 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 2) = 0

      @[pico_encapsulation]
      def constraint_195 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_13 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 3) = 0

      @[pico_encapsulation]
      def constraint_196 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_14 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 4) = 0

      @[pico_encapsulation]
      def constraint_197 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_15 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 5) = 0

      @[pico_encapsulation]
      def constraint_198 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_16 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 6) = 0

      @[pico_encapsulation]
      def constraint_199 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_17 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - 7) = 0

      @[pico_encapsulation]
      def constraint_200 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (air.cols.op_b_access.value_1 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_201 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (air.cols.op_b_access.value_2 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_202 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_7 row 0 + air.cols.opcode_specific.specific_9 row 0)) * (air.cols.op_b_access.value_3 row 0 - 0) = 0

      @[pico_encapsulation]
      def constraint_203 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 0 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 4 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 8 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 12 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 16 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 20 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 24 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 28 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_0 row 0) = 0

      @[pico_encapsulation]
      def constraint_204 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 1 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 5 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 9 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 13 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 17 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 21 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 25 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 29 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_1 row 0) = 0

      @[pico_encapsulation]
      def constraint_205 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 2 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 6 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 10 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 14 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 18 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 22 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 26 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 30 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_2 row 0) = 0

      @[pico_encapsulation]
      def constraint_206 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_7 row 0 * (0 + air.public_values 3 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 7 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 11 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 15 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 19 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 23 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 27 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 31 * air.cols.opcode_specific.specific_17 row 0 - air.cols.op_c_access.value_3 row 0) = 0

      @[pico_encapsulation]
      def constraint_207 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_0 row 0 - air.cols.opcode_specific.specific_28 row 0) = 0

      @[pico_encapsulation]
      def constraint_208 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_1 row 0 - air.cols.opcode_specific.specific_29 row 0) = 0

      @[pico_encapsulation]
      def constraint_209 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_2 row 0 - air.cols.opcode_specific.specific_30 row 0) = 0

      @[pico_encapsulation]
      def constraint_210 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (air.cols.op_c_access.value_3 row 0 - air.cols.opcode_specific.specific_31 row 0) = 0

      @[pico_encapsulation]
      def constraint_211 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * air.cols.opcode_specific.specific_9 row 0 * (0 + air.public_values 32 * air.cols.opcode_specific.specific_10 row 0 + air.public_values 33 * air.cols.opcode_specific.specific_11 row 0 + air.public_values 34 * air.cols.opcode_specific.specific_12 row 0 + air.public_values 35 * air.cols.opcode_specific.specific_13 row 0 + air.public_values 36 * air.cols.opcode_specific.specific_14 row 0 + air.public_values 37 * air.cols.opcode_specific.specific_15 row 0 + air.public_values 38 * air.cols.opcode_specific.specific_16 row 0 + air.public_values 39 * air.cols.opcode_specific.specific_17 row 0 - (1 * air.cols.op_c_access.value_0 row 0 + 256 * air.cols.op_c_access.value_1 row 0 + 65536 * air.cols.op_c_access.value_2 row 0 + 16777216 * air.cols.op_c_access.value_3 row 0)) = 0

      @[pico_encapsulation]
      def constraint_212 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_4 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) - air.cols.opcode_specific.specific_5 row 0) = 0

      @[pico_encapsulation]
      def constraint_213 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_214 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) = 0

      @[pico_encapsulation]
      def constraint_215 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 + air.cols.opcode_selector.is_unimpl row 0) * air.cols.is_real row 1 = 0

      @[pico_encapsulation]
      def constraint_216 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * air.cols.next_pc row 0 = 0

      @[pico_encapsulation]
      def constraint_217 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_0 row 0 - air.cols.opcode_specific.specific_28 row 0) = 0

      @[pico_encapsulation]
      def constraint_218 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_1 row 0 - air.cols.opcode_specific.specific_29 row 0) = 0

      @[pico_encapsulation]
      def constraint_219 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_2 row 0 - air.cols.opcode_specific.specific_30 row 0) = 0

      @[pico_encapsulation]
      def constraint_220 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (air.cols.op_b_access.value_3 row 0 - air.cols.opcode_specific.specific_31 row 0) = 0

      @[pico_encapsulation]
      def constraint_221 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0 * (1 * air.cols.op_b_access.value_0 row 0 + 256 * air.cols.op_b_access.value_1 row 0 + 65536 * air.cols.op_b_access.value_2 row 0 + 16777216 * air.cols.op_b_access.value_3 row 0 - air.public_values 42) = 0

      @[pico_encapsulation]
      def constraint_222 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * air.cols.is_real row 1 * (air.cols.chunk row 0 - air.cols.chunk row 1) = 0

      @[pico_encapsulation]
      def constraint_223 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row * air.cols.clk row 0 = 0

      @[pico_encapsulation]
      def constraint_224 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * air.cols.is_real row 1 * (air.cols.clk row 0 + 4 + air.cols.op_a_access.prev_value_2 row 0 * air.cols.opcode_selector.is_ecall row 0 - air.cols.clk row 1) = 0

      @[pico_encapsulation]
      def constraint_225 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.clk row 0 - (air.cols.clk_16bit_limb row 0 + air.cols.clk_8bit_limb row 0 * 65536)) = 0

      @[pico_encapsulation]
      def constraint_226 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (1 - (air.cols.opcode_specific.specific_4 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) - air.cols.opcode_specific.specific_5 row 0) = 0

      @[pico_encapsulation]
      def constraint_227 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.opcode_specific.specific_5 row 0 - 1)) = 0

      @[pico_encapsulation]
      def constraint_228 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.opcode_selector.is_ecall row 0 * (air.cols.opcode_specific.specific_5 row 0 * (air.cols.op_a_access.prev_value_0 row 0 - 0)) = 0

      @[pico_encapsulation]
      def constraint_229 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_sequential_instr row 0 - (1 - (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 + air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0 + air.cols.opcode_specific.specific_5 row 0 * air.cols.opcode_selector.is_ecall row 0))) = 0

      @[pico_encapsulation]
      def constraint_230 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * air.cols.is_real row 1 * (air.cols.is_sequential_instr row 0 * (air.cols.pc row 0 + 4 - air.cols.pc row 1)) = 0

      @[pico_encapsulation]
      def constraint_231 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_sequential_instr row 0 * (air.cols.pc row 0 + 4 - air.cols.next_pc row 0)) = 0

      @[pico_encapsulation]
      def constraint_232 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.public_values 44 - air.cols.chunk row 0) = 0

      @[pico_encapsulation]
      def constraint_233 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row * (air.public_values 40 - air.cols.pc row 0) = 0

      @[pico_encapsulation]
      def constraint_234 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 0 - air.cols.is_real row 1) * (air.public_values 41 - air.cols.next_pc row 0) = 0

      @[pico_encapsulation]
      def constraint_235 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row * (air.cols.is_real row 0 * (air.public_values 41 - air.cols.next_pc row 0)) = 0

      @[pico_encapsulation]
      def constraint_236 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        air.cols.is_real row 0 * (air.cols.is_real row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_237 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row * (air.cols.is_real row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_238 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row * (air.cols.is_real row 0 - 1) * air.cols.is_real row 1 = 0

      @[pico_encapsulation]
      def constraint_239 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * (air.cols.opcode_selector.imm_b row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_240 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * (air.cols.opcode_selector.imm_c row 0 - 1) = 0

      @[pico_encapsulation]
      def constraint_241 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_alu row 0 = 0

      @[pico_encapsulation]
      def constraint_242 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_ecall row 0 = 0

      @[pico_encapsulation]
      def constraint_243 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lb row 0 = 0

      @[pico_encapsulation]
      def constraint_244 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lbu row 0 = 0

      @[pico_encapsulation]
      def constraint_245 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lh row 0 = 0

      @[pico_encapsulation]
      def constraint_246 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lhu row 0 = 0

      @[pico_encapsulation]
      def constraint_247 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_lw row 0 = 0

      @[pico_encapsulation]
      def constraint_248 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_sb row 0 = 0

      @[pico_encapsulation]
      def constraint_249 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_sh row 0 = 0

      @[pico_encapsulation]
      def constraint_250 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_sw row 0 = 0

      @[pico_encapsulation]
      def constraint_251 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_beq row 0 = 0

      @[pico_encapsulation]
      def constraint_252 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bne row 0 = 0

      @[pico_encapsulation]
      def constraint_253 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_blt row 0 = 0

      @[pico_encapsulation]
      def constraint_254 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bge row 0 = 0

      @[pico_encapsulation]
      def constraint_255 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bltu row 0 = 0

      @[pico_encapsulation]
      def constraint_256 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_bgeu row 0 = 0

      @[pico_encapsulation]
      def constraint_257 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_jalr row 0 = 0

      @[pico_encapsulation]
      def constraint_258 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_jal row 0 = 0

      @[pico_encapsulation]
      def constraint_259 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_auipc row 0 = 0

      @[pico_encapsulation]
      def constraint_260 (air : Valid_CpuAir F ExtF) (row : ℕ) : Prop :=
        (1 - air.cols.is_real row 0) * air.cols.opcode_selector.is_unimpl row 0 = 0

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

    @[simp]
    def allHold_simplified
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      List.Forall (·) (row_constraint_list air row)

  end constraint_simplification

end CpuAir.constraints

namespace CPUAir.Buses

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
        (-(air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0), #v[9 - air.cols.opcode_selector.is_blt row 0 - air.cols.opcode_selector.is_bge row 0, air.cols.opcode_specific.specific_30 row 0, 0, 0, 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-(air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 + air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0), #v[9 - air.cols.opcode_selector.is_blt row 0 - air.cols.opcode_selector.is_bge row 0, air.cols.opcode_specific.specific_29 row 0, 0, 0, 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0]),
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
        (-(1 - air.cols.opcode_selector.imm_c row 0), #v[air.cols.op_c_access.prev_chunk row 0, air.cols.op_c_access.prev_clk row 0, air.cols.instruction.c_0 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (  1 - air.cols.opcode_selector.imm_c row 0,  #v[air.cols.chunk row 0, 1 + air.cols.clk row 0, air.cols.instruction.c_0 row 0, air.cols.op_c_access.value_0 row 0, air.cols.op_c_access.value_1 row 0, air.cols.op_c_access.value_2 row 0, air.cols.op_c_access.value_3 row 0]),
        (-(1 - air.cols.opcode_selector.imm_b row 0), #v[air.cols.op_b_access.prev_chunk row 0, air.cols.op_b_access.prev_clk row 0, air.cols.instruction.b_0 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (  1 - air.cols.opcode_selector.imm_b row 0,  #v[air.cols.chunk row 0, 2 + air.cols.clk row 0, air.cols.instruction.b_0 row 0, air.cols.op_b_access.value_0 row 0, air.cols.op_b_access.value_1 row 0, air.cols.op_b_access.value_2 row 0, air.cols.op_b_access.value_3 row 0]),
        (-air.cols.is_real row 0, #v[air.cols.op_a_access.access.prev_chunk row 0, air.cols.op_a_access.access.prev_clk row 0, air.cols.instruction.a_0 row 0, air.cols.op_a_access.prev_value_0 row 0, air.cols.op_a_access.prev_value_1 row 0, air.cols.op_a_access.prev_value_2 row 0, air.cols.op_a_access.prev_value_3 row 0]),
        ( air.cols.is_real row 0, #v[air.cols.chunk row 0, 3 + air.cols.clk row 0, air.cols.instruction.a_0 row 0, air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0, air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0])
      ]
    }

  @[simp]
  def CPU_bus_operations (air : Valid_CpuAir FKB ExtF) (row : ℕ) :=
    RV32IM.bus_operations (bus_row air row) ++ [ .WritePC (BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)) ]

end CPUAir.Buses
