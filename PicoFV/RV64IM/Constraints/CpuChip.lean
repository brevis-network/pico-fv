import PicoFV.Fundamentals.KoalaBear
import PicoFV.RV64IM.Extraction.CpuChip
import PicoFV.RV64IM.Airs.CpuChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# CpuChip — abstract constraints & buses (RV64, Pico v3.1.1)

`CpuChip`'s Pico Rust source is `vm/src/chips/chips/riscv_cpu/` at
commit `2acc7c1828fb4ec1bed5963511bb370870c5b608`, with `constraints.rs`
calling out to `register/`, `branch/`, `jump/`, `ecall/`,
`public_values/` and `chunk_clk/`.

The `ConstraintsAndBuses` namespace below restates each of the 65
extracted constraints over the named columns of `Valid_CpuChip`, with a
`_equiv` lemma proving it equal to the raw form in
`Extraction/CpuChip.lean`, and restates the 17 bus messages the chip
emits per row.

The v3.1.1 chip checks much less itself than the 2.x one did (65
constraints against 218). What it no longer does, it takes from
elsewhere: the pc's range from the Program table, the next pc from the
next row, the chunk's final pc from the public values. The constraints
here are therefore mostly definitional — the operand values, the class
selectors, the row chain — with real arithmetic only in the branch
target, the jump return address and JALR's four-limb addition.
-/

namespace CpuChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- ======================================================================
      -- Immediate operands (0-7)
      -- `register/constraints.rs:29-42`. When `imm_b` is set the operand did not come from a
      -- register, so the row's `op_b` value is pinned to the instruction's immediate: the two
      -- u16 limbs as given, and limbs 2 and 3 to the sign fill `0xFFFF * sign`. Same for `op_c`.
      -- ======================================================================

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

      -- ======================================================================
      -- Writes to x0 (8-11)
      -- `register/constraints.rs:75`. A row whose destination is `x0` reads back zero, so the
      -- chip pins the whole `op_a` value to zero rather than dispatching a write.
      -- ======================================================================

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

      -- ======================================================================
      -- `is_real` is boolean (12)
      -- `register/constraints.rs:80-90`. The op_a register access is gated by `is_real`, and
      -- `eval_memory_access_lite` asserts its gate boolean (`machine/builder/riscv_memory.rs:137`).
      -- Stated twice by the chip: constraint 44 is the same assertion from `constraints.rs:340`.
      -- ======================================================================

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ======================================================================
      -- Branches and stores leave `op_a` alone (13-16)
      -- `register/constraints.rs:119-123`. Neither class writes a register, so the access's
      -- value equals its previous value limb by limb.
      -- ======================================================================

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

      -- ======================================================================
      -- The ALU dispatch multiplicity (17)
      -- `constraints.rs:143-146`. `is_alu_not_x0 = is_alu_instruction * (1 - op_a_0)`, with the
      -- ALU class derived as the one-hot complement
      -- `is_real - (is_beq + ... + is_bgeu + is_ecall + is_memory + is_jal + is_jalr)`
      -- (`opcode_selector/columns.rs:22-45`).
      -- ======================================================================

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_alu_not_x0 row 0) - (((air.cols.is_real row 0) - ((((((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)) + (air.cols.opcode_selector.is_ecall row 0)) + (air.cols.opcode_selector.is_memory row 0)) + (air.cols.opcode_selector.is_jal row 0)) + (air.cols.opcode_selector.is_jalr row 0))) * (1 - (air.cols.instruction.op_a_is_x0 row 0)))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ======================================================================
      -- Branch rows (18-19)
      -- `branch/constraints.rs:74-86`. A branch takes its offset as an immediate, and on a taken
      -- branch the next pc is `pc + offset`, read over the two-limb pc. The taken predicate is
      -- `is_beq * (1 - a_lt_b - a_gt_b) + is_bne * (a_lt_b + a_gt_b) + (is_blt + is_bltu) * a_lt_b
      -- + (is_bge + is_bgeu) * (1 - a_lt_b)`, using `a_eq_b = 1 - a_lt_b - a_gt_b`.
      -- ======================================================================

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

      -- ======================================================================
      -- Jump return address (20-23)
      -- `jump/constraints.rs:29-38` (the gadget is `Pc::add_limb_with_carry`, `compiler/addr.rs:321`)
      -- and `jump/constraints.rs:43-46`. On a jump that writes a
      -- register, `op_a = pc + 4` through `Pc::add_limb_with_carry`: `pc_carry` is the carry out
      -- of limb 0, limb 1 absorbs it, and limbs 2 and 3 are zero. Limb 3 is zeroed on every jump.
      -- ======================================================================

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

      -- ======================================================================
      -- JAL (24-25)
      -- `jump/constraints.rs:64-77`. The target is `pc + offset`, and the offset is an immediate.
      -- ======================================================================

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

      -- ======================================================================
      -- JALR (26-30)
      -- `jump/constraints.rs:112-126`. `jalr_lsb` is bit 0 of the unmasked target, and the four
      -- limb carries of `op_b + op_c = next_pc + jalr_lsb` are each asserted boolean; `2130673921`
      -- is `inv(2^16)` in KoalaBear, so `k * inv(2^16)` is the carry out of a limb.
      -- ======================================================================

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

      -- ======================================================================
      -- ECALL bookkeeping (31-32)
      -- `ecall/constraints.rs:52-56`. Off an ecall row the halt flag and the extra-clock count
      -- are zero.
      -- ======================================================================

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

      -- ======================================================================
      -- Halt (33-35)
      -- `ecall/constraints.rs:99-101`. A halting row is the chunk's last real row and its next pc
      -- is zero.
      -- ======================================================================

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

      -- ======================================================================
      -- The chunk's first clk (36)
      -- `chunk_clk/constraints.rs:62-63`. Row 0's clk is `CHUNK_CLK_START = 4`.
      -- ======================================================================

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((Circuit.isFirstRow air row) * ((air.cols.clk row 0) - 4)) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ======================================================================
      -- Sequential and branch-not-taken rows (37)
      -- `constraints.rs:318-326`. One field equation `next_pc = pc + 4`, gated by
      -- `is_real - taken - is_jal - is_jalr - is_halt`. A pc fits in two limbs, so the addition
      -- stays inside `[0, p)` and needs no carry witness.
      -- ======================================================================

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_CpuChip F ExtF) (row : ℕ) : Prop :=
        ((((((air.cols.is_real row 0) - (((((air.cols.opcode_selector.is_beq row 0) * ((1 - (air.cols.a_lt_b row 0)) - (air.cols.a_gt_b row 0))) + ((air.cols.opcode_selector.is_bne row 0) * ((air.cols.a_lt_b row 0) + (air.cols.a_gt_b row 0)))) + (((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bltu row 0)) * (air.cols.a_lt_b row 0))) + (((air.cols.opcode_selector.is_bge row 0) + (air.cols.opcode_selector.is_bgeu row 0)) * (1 - (air.cols.a_lt_b row 0))))) - (air.cols.opcode_selector.is_jal row 0)) - (air.cols.opcode_selector.is_jalr row 0)) - (air.cols.is_halt row 0)) * (((1 * (air.cols.next_pc_0 row 0)) + (65536 * (air.cols.next_pc_1 row 0))) - (((1 * (air.cols.pc_0 row 0)) + (65536 * (air.cols.pc_1 row 0))) + 4))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_CpuChip F ExtF) (row : ℕ)
      : CpuChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- ======================================================================
      -- Public values (38-43)
      -- `public_values/constraints.rs:30-50`. Row 0's pc is the chunk's start pc and the last real
      -- row's next pc is the chunk's final pc, each in two limbs with the third pinned to zero.
      -- ======================================================================

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

      -- ======================================================================
      -- The row chain (44-51)
      -- `constraints.rs:340-341` and `410-450`. Row 0 is real; the successor's pc and clk follow
      -- this row's `next_pc` and `clk + 4 + num_extra_clk`; `is_real` never comes back on, so the
      -- real rows are a physical prefix; and `is_last` is the drop in `is_real` on a transition
      -- row, or `is_real` itself on the last physical row.
      -- ======================================================================

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

      -- ======================================================================
      -- Padding rows (52-64)
      -- `constraints.rs:209-228`. Off a real row every selector that would send a message is
      -- zero, and the two immediate flags are one, so no register read is dispatched either.
      -- ======================================================================

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

      @[simp]
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

      -- ======================================================================
      -- The 17 messages the chip emits per row, in the order
      -- `Extraction/CpuChip.lean` lists them. The bus id is the head of each
      -- entry: 1 Memory, 2 Program, 4 ALU, 5 Byte, 13 Ecall.
      --
      --   * Program (1): the instruction fetch, 26 fields, multiplicity
      --     `is_real` (`constraints.rs:42-49`, built at `:465-480`).
      --   * op_b register read (4): two timestamp range checks, the previous
      --     access and this one, gated by `1 - imm_b`
      --     (`register/constraints.rs:49-59`).
      --   * op_c register read (4): the same at `clk + 1` (`register/constraints.rs:61-71`).
      --   * op_a register access (4): the same at `clk + 3`, on every real row
      --     (`register/constraints.rs:80-90`).
      --   * memory dispatch (1): gated by `is_memory`, 17 fields.
      --   * ALU dispatch (1): gated by `is_alu_not_x0` (`constraints.rs:147`).
      --   * ALU compare (1): one merged branch comparison for every branch
      --     row, opcode `SLT`/`SLTU + 256` (`branch/constraints.rs:98-117`).
      --   * Ecall (1): gated by `is_ecall`, 20 fields.
      --
      -- Each register access carries a `BitRange(9)` check on its `diff_hi9`
      -- limb, which is byte sub-opcode 9 with the bit count in field 3.
      -- ======================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_CpuChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [
          ((air.cols.is_real row 0), [2, (air.cols.pc_0 row 0), (air.cols.pc_1 row 0), (air.cols.instruction.opcode row 0), (air.cols.instruction.opcode row 0), (air.cols.instruction.op_a row 0), (air.cols.instruction.op_b_0 row 0), (air.cols.instruction.op_b_1 row 0), (air.cols.instruction.op_b_sign row 0), (air.cols.instruction.op_c_0 row 0), (air.cols.instruction.op_c_1 row 0), (air.cols.instruction.op_c_sign row 0), (air.cols.instruction.op_a_is_x0 row 0), (air.cols.opcode_selector.imm_b row 0), (air.cols.opcode_selector.imm_c row 0), (air.cols.opcode_selector.is_ecall row 0), (air.cols.opcode_selector.is_memory row 0), (air.cols.opcode_selector.is_store row 0), (air.cols.opcode_selector.is_beq row 0), (air.cols.opcode_selector.is_bne row 0), (air.cols.opcode_selector.is_blt row 0), (air.cols.opcode_selector.is_bge row 0), (air.cols.opcode_selector.is_bltu row 0), (air.cols.opcode_selector.is_bgeu row 0), (air.cols.opcode_selector.is_jalr row 0), (air.cols.opcode_selector.is_jal row 0), (air.cols.pc_carry row 0)]),
          ((1 - (air.cols.opcode_selector.imm_b row 0)), [5, 8, (air.cols.op_b_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          ((1 - (air.cols.opcode_selector.imm_b row 0)), [5, 9, (air.cols.op_b_access.access.diff_hi9 row 0), 0, 9, 0]),
          ((1 - (air.cols.opcode_selector.imm_b row 0)), [1, (air.public_values 48), ((((air.cols.clk row 0) + 2) - ((air.cols.op_b_access.access.diff_16bit_limb row 0) + ((air.cols.op_b_access.access.diff_hi9 row 0) * 65536))) - 1), (air.cols.instruction.op_b_0 row 0), 0, 0, (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0)]),
          ((0 - (1 - (air.cols.opcode_selector.imm_b row 0))), [1, (air.public_values 48), ((air.cols.clk row 0) + 2), (air.cols.instruction.op_b_0 row 0), 0, 0, (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0)]),
          ((1 - (air.cols.opcode_selector.imm_c row 0)), [5, 8, (air.cols.op_c_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          ((1 - (air.cols.opcode_selector.imm_c row 0)), [5, 9, (air.cols.op_c_access.access.diff_hi9 row 0), 0, 9, 0]),
          ((1 - (air.cols.opcode_selector.imm_c row 0)), [1, (air.public_values 48), ((((air.cols.clk row 0) + 1) - ((air.cols.op_c_access.access.diff_16bit_limb row 0) + ((air.cols.op_c_access.access.diff_hi9 row 0) * 65536))) - 1), (air.cols.instruction.op_c_0 row 0), 0, 0, (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0)]),
          ((0 - (1 - (air.cols.opcode_selector.imm_c row 0))), [1, (air.public_values 48), ((air.cols.clk row 0) + 1), (air.cols.instruction.op_c_0 row 0), 0, 0, (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0)]),
          ((air.cols.is_real row 0), [5, 8, (air.cols.op_a_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          ((air.cols.is_real row 0), [5, 9, (air.cols.op_a_access.access.diff_hi9 row 0), 0, 9, 0]),
          ((air.cols.is_real row 0), [1, (air.public_values 48), ((((air.cols.clk row 0) + 3) - ((air.cols.op_a_access.access.diff_16bit_limb row 0) + ((air.cols.op_a_access.access.diff_hi9 row 0) * 65536))) - 1), (air.cols.instruction.op_a row 0), 0, 0, (air.cols.op_a_access.prev_value_0 row 0), (air.cols.op_a_access.prev_value_1 row 0), (air.cols.op_a_access.prev_value_2 row 0), (air.cols.op_a_access.prev_value_3 row 0)]),
          ((0 - (air.cols.is_real row 0)), [1, (air.public_values 48), ((air.cols.clk row 0) + 3), (air.cols.instruction.op_a row 0), 0, 0, (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0)]),
          ((air.cols.opcode_selector.is_memory row 0), [1, (air.cols.instruction.opcode row 0), (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0), (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0), (air.cols.instruction.op_a_is_x0 row 0), (air.cols.opcode_selector.is_memory row 0), (air.public_values 48), (air.cols.clk row 0)]),
          ((air.cols.is_alu_not_x0 row 0), [4, (air.cols.instruction.opcode row 0), (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0), (air.cols.op_c_access.access.value_0 row 0), (air.cols.op_c_access.access.value_1 row 0), (air.cols.op_c_access.access.value_2 row 0), (air.cols.op_c_access.access.value_3 row 0)]),
          (((((((air.cols.opcode_selector.is_beq row 0) + (air.cols.opcode_selector.is_bne row 0)) + (air.cols.opcode_selector.is_blt row 0)) + (air.cols.opcode_selector.is_bge row 0)) + (air.cols.opcode_selector.is_bltu row 0)) + (air.cols.opcode_selector.is_bgeu row 0)), [4, (((((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bge row 0)) * 8) + ((1 - ((air.cols.opcode_selector.is_blt row 0) + (air.cols.opcode_selector.is_bge row 0))) * 9)) + 256), (air.cols.a_lt_b row 0), (air.cols.a_gt_b row 0), 0, 0, (air.cols.op_a_access.access.value_0 row 0), (air.cols.op_a_access.access.value_1 row 0), (air.cols.op_a_access.access.value_2 row 0), (air.cols.op_a_access.access.value_3 row 0), (air.cols.op_b_access.access.value_0 row 0), (air.cols.op_b_access.access.value_1 row 0), (air.cols.op_b_access.access.value_2 row 0), (air.cols.op_b_access.access.value_3 row 0)]),
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
