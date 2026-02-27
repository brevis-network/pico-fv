import PicoFV.Equivalence.ALU

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

namespace Equivalence

  open Plonky3

  open RV32IM
  open RV32IM_Interactions
  open CpuAir.ConstraintsAndBuses
  open CpuAir.Interactions

  attribute [local simp]
    program_bus_entry

  section Auxiliaries


    def pico_CpuAir_control_flow_assumptions
      (air : Valid_CpuAir FKB ExtF)
    :=
      -- Public value 41 (`next_pc`) holds the starting program
      -- counter for the next chunk. It is either zero (if the last
      -- execution was HALT), or is the first pc of the first row
      -- of the next chunk. In the former case, zero is divisible
      -- by four. In the latter case, `is_real` must hold on the
      -- first row on the next chunk (by constraint 237), and so
      -- that program counter must be on the program bus, meaning
      -- it is divisible by four by the program bus properties.
      (air.public_values 41).val % 4 = 0

    lemma is_real_rotation
      (air : Valid_CpuAir FKB ExtF)
      (row rotation : ℕ)
    : air.cols.is_real row rotation = air.cols.is_real ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.is_real Valid_CpuAir.cols Valid_CpuAir.last_row; simp

      obtain ⟨ valid_circuit, valid_cols, valid_per_col ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ), air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 := by aesop
      specialize valid_circuit 111 row rotation

      have valid_col_111 : ∀ row rotation, air.col_111 row rotation := by aesop
      unfold Raw_CpuAir.col_111 at valid_col_111
      iterate 2 rw [valid_col_111] at valid_circuit
      clear valid_col_111
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all

      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_111 row rotation := by aesop
      unfold Raw_CpuCols.col_111 at valid_cols

      clear *- valid_circuit valid_cols
      grind

    lemma pc_rotation
      (air : Valid_CpuAir FKB ExtF)
      (row rotation : ℕ)
    : air.cols.pc row rotation = air.cols.pc ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.pc Valid_CpuAir.cols Valid_CpuAir.last_row; simp

      obtain ⟨ valid_circuit, valid_cols, valid_per_col ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ), air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 := by aesop
      specialize valid_circuit 4 row rotation

      have valid_col_4 : ∀ row rotation, air.col_4 row rotation := by aesop
      unfold Raw_CpuAir.col_4 at valid_col_4
      iterate 2 rw [valid_col_4] at valid_circuit
      clear valid_col_4
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all

      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_4 row rotation := by aesop
      unfold Raw_CpuCols.col_4 at valid_cols

      clear *- valid_circuit valid_cols
      grind

    lemma pc_next_row_mod_four_eq_zero
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_transition_row : ¬ (Circuit.isTransitionRow air row = 0))
      (h_is_real : air.cols.is_real row 1 = 1)
      (h_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
    :
      (air.cols.pc row 1).val % 4 = 0
    := by
      replace h_row : (row + 1) ≤ air.last_row
      := by
        simp [Circuit.isTransitionRow] at h_transition_row
        simp [Circuit.last_row] at h_transition_row
        omega
      rw [is_real_rotation, Nat.mod_eq_of_lt (by omega)] at h_is_real
      rw [pc_rotation, Nat.mod_eq_of_lt (b := air.last_row + 1) (by omega)]
      specialize h_axioms (row + 1) (by omega)
      simp [
        bus_row_axioms,
        bus_row,
        h_is_real
      ] at h_axioms
      grind

    lemma next_pc_mod_four_eq_zero
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (h_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      (air.cols.next_pc row 0).val % 4 = 0
    := by
      by_cases h_transition : Circuit.isTransitionRow air row = 0
      -- Last row
      . obtain relevant_constraints
        : constraint_235 air row
        := by
          specialize h_constraints row h_row
          simp [allHold_simplified] at h_constraints
          grind
        simp [Circuit.isTransitionRow] at h_transition
        simp [
          constraint_and_interaction_simplification,
          Circuit.isLastRow,
          ← h_transition,
          h_is_real,
          sub_eq_zero
        ] at relevant_constraints
        rw [← relevant_constraints]
        exact pico_assumptions
      -- Transition row
      . simp_all
        by_cases h_is_real_next : air.cols.is_real row 1 = 0
        -- Final real row
        . obtain relevant_constraints
          : constraint_234 air row
          := by
            specialize h_constraints row h_row
            simp [allHold_simplified] at h_constraints
            grind
          simp [
            constraint_and_interaction_simplification,
            sub_eq_zero,
            *
          ] at relevant_constraints
          rw [← relevant_constraints]
          exact pico_assumptions
        . specialize h_constraints row (by omega)
          have h_breakdown
          :
            air.cols.is_sequential_instr row 0 = 1 ∨
            air.cols.is_branch_instruction row 0 = 1 ∨
            air.cols.is_jump_instruction row 0 = 1
          := by
            simp [Valid_CpuCols.is_branch_instruction, Valid_CpuCols.is_jump_instruction]
            obtain ⟨ h_halt, h_seq ⟩
            : constraint_215 air row ∧ constraint_229 air row
            := by
              simp [allHold_simplified] at h_constraints
              grind
            simp [
              constraint_and_interaction_simplification,
              cpu_ecall_cols_simplification,
              sub_eq_zero,
              *
            ] at h_halt h_seq
            rw [h_seq]; clear h_seq
            have h_row_axioms := h_assumptions row (by omega)
            simp [bus_row_assumptions, bus_row, h_is_real] at h_row_axioms
            replace h_row_axioms := h_row_axioms.1
            obtain ⟨ instr, data, props, h_data, h_deser, h_props ⟩ := h_row_axioms
            have ⟨ h_op_bounds, h_op_neq_26, h_op_neq_29 ⟩ := ProgramBusEntry.inversion_opcode_bounds h_data h_deser
            have h_selectors := ProgramBusEntry.inversion_opcode_selectors h_data h_deser
            simp at h_op_bounds h_op_neq_26 h_op_neq_29 h_selectors; clear h_data h_deser h_props
            repeat rw [Fin.ext_iff (a := air.cols.instruction.opcode row 0)] at h_selectors
            interval_cases (air.cols.instruction.opcode row 0).val <;>
              simp at h_selectors <;>
              simp [h_selectors] at h_halt ⊢ <;>
              omega
          suffices : air.cols.next_pc row 0 = air.cols.pc row 1
          . replace h_row : (row + 1) ≤ air.last_row
            := by
              simp [Circuit.isTransitionRow] at h_transition
              simp [Circuit.last_row] at h_transition
              omega
            rw [this, pc_rotation, Nat.mod_eq_of_lt (b := air.last_row + 1) (by omega)]
            rw [is_real_rotation, Nat.mod_eq_of_lt (b := air.last_row + 1) (by omega)] at h_is_real_next
            specialize h_axioms (row + 1) h_row
            simp [bus_row_axioms, bus_row, *] at h_axioms
            grind
          . obtain h | h | h := h_breakdown
            . obtain relevant_constraints
              : constraint_230 air row ∧ constraint_231 air row
              := by
                simp [allHold_simplified] at h_constraints
                grind
              simp [constraint_and_interaction_simplification, *] at relevant_constraints
              omega
            . simp [Valid_CpuCols.is_branch_instruction] at h
              obtain relevant_constraints
              : constraint_29 air row ∧ constraint_30 air row ∧ constraint_61 air row ∧
                constraint_63 air row ∧ constraint_64 air row ∧ constraint_65 air row ∧ constraint_66 air row
              := by
                simp [allHold_simplified] at h_constraints
                grind
              simp [constraint_and_interaction_simplification, sub_eq_zero, *] at relevant_constraints
              grind
            . simp [Valid_CpuCols.is_jump_instruction] at h
              obtain relevant_constraints
              : constraint_82 air row ∧ constraint_83 air row
              := by
                simp [allHold_simplified] at h_constraints
                grind
              simp [constraint_and_interaction_simplification, sub_eq_zero, *] at relevant_constraints
              grind

    lemma branching_pc
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      air.cols.branching row 0 = 1 →
        U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                    BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                    BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                    BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
          = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
    := by
      intro h_branch

      simp [
        bus_row_assumptions,
        bus_row,
        h_branch,
        cpu_branch_cols_simplification,
      ] at h_assumptions
      replace h_assumptions := h_assumptions.2.2.1
      simp [ ALUBus.Spec ] at h_assumptions

      have relevant_constraints :
        constraint_28 air row ∧ constraint_31 air row ∧ constraint_32 air row ∧ constraint_33 air row ∧
        constraint_34 air row ∧ constraint_35 air row ∧ constraint_36 air row ∧ constraint_37 air row ∧
        constraint_38 air row ∧ constraint_39 air row ∧ constraint_40 air row ∧ constraint_41 air row ∧
        constraint_41 air row ∧ constraint_43 air row ∧ constraint_44 air row ∧ constraint_45 air row
      := by
        simp [allHold_simplified] at h_constraints
        grind
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_branch_instr,
        h_branch,
        sub_eq_zero,
      ] at relevant_constraints
      simp [← relevant_constraints.1, ← BitVec.toNat_inj, U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_assumptions; omega)]
      simp [Fin.val_add, Fin.val_mul]
      rw [Nat.mod_eq_of_lt (b := KB_prime) (by grind)]
      grind

    lemma branching_npc
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      air.cols.branching row 0 = 1 →
        U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                    BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                    BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                    BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
          = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
    := by
      intro h_branch

      simp [
        bus_row_assumptions,
        bus_row,
        h_branch,
        cpu_branch_cols_simplification,
      ] at h_assumptions
      replace h_assumptions := h_assumptions.2.2.1
      simp [ ALUBus.Spec ] at h_assumptions

      have relevant_constraints :
        constraint_30 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧ constraint_48 air row ∧
        constraint_49 air row ∧ constraint_50 air row ∧ constraint_51 air row ∧ constraint_52 air row ∧
        constraint_53 air row ∧ constraint_54 air row ∧ constraint_55 air row ∧ constraint_56 air row ∧
        constraint_57 air row ∧ constraint_58 air row ∧ constraint_59 air row ∧ constraint_60 air row
      := by
        simp [allHold_simplified] at h_constraints
        grind
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_branch_instr,
        h_branch,
        h_is_real,
        sub_eq_zero,
      ] at relevant_constraints
      simp [← relevant_constraints.1, ← BitVec.toNat_inj, U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_assumptions; omega)]
      simp [Fin.val_add, Fin.val_mul]
      rw [Nat.mod_eq_of_lt (b := KB_prime) (by grind)]
      grind

    lemma non_branching_npc
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      air.cols.branching row 0 = 0 →
        BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega) + 4#32
          = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
    := by
      intro h_branch

      have relevant_constraints :
        constraint_63 air row ∧ constraint_64 air row
      := by
        simp [allHold_simplified] at h_constraints
        grind
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_branch_instr,
        h_branch,
        h_is_real,
        sub_eq_zero,
      ] at relevant_constraints

      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms

      simp [← BitVec.toNat_inj]; grind

    lemma is_branch_instruction_characterisation
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      let beq := air.cols.opcode_selector.is_beq row 0
      let bne := air.cols.opcode_selector.is_bne row 0
      let blt := air.cols.opcode_selector.is_blt row 0
      let bge := air.cols.opcode_selector.is_bge row 0
      let bltu := air.cols.opcode_selector.is_bltu row 0
      let bgeu := air.cols.opcode_selector.is_bgeu row 0
      let store := air.cols.is_store_instruction row 0
      (
        (beq = 1 ∧ bne = 0 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 0) ∨
        (beq = 0 ∧ bne = 1 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 0) ∨
        (beq = 0 ∧ bne = 0 ∧ blt = 1 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 0) ∨
        (beq = 0 ∧ bne = 0 ∧ blt = 0 ∧ bge = 1 ∧ bltu = 0 ∧ bgeu = 0) ∨
        (beq = 0 ∧ bne = 0 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 1 ∧ bgeu = 0) ∨
        (beq = 0 ∧ bne = 0 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 1)
      ) ∧ store = 0
    := by
      simp [ bus_row_assumptions ] at h_assumptions
      replace h_assumptions := h_assumptions.1
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_assumptions
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_assumptions
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have opcode_bounds :=
        @ProgramBusEntry.inversion_opcode_bounds
          instr
          ⟨ -1, data ⟩
          props
          (ProgramBusEntry.deserialise (program_bus_entry air row))
          (by simp [h_eq, h_is_real])
          (by simp [h_is_real]; aesop)
      have opcode_selectors :=
        @ProgramBusEntry.inversion_opcode_selectors
          instr
          ⟨ -1, data ⟩
          props
          (ProgramBusEntry.deserialise (program_bus_entry air row))
          (by simp [h_eq, h_is_real])
          (by simp [h_is_real]; aesop)
      clear h_eq h_eq_entry
      simp [program_bus_entry] at opcode_bounds opcode_selectors
      obtain ⟨ opcode_range, opcode_not_26, opcode_not_29 ⟩ := opcode_bounds
      simp [Valid_CpuCols.is_branch_instruction] at h_branch_instr
      repeat rw [Fin.ext_iff (a := air.cols.instruction.opcode row 0)] at opcode_selectors
      interval_cases (air.cols.instruction.opcode row 0).val <;> simp_all [Valid_CpuCols.is_store_instruction]

    lemma a_lt_b_meaning
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      air.cols.branch_a_lt_b row 0 =
      if (air.cols.opcode_selector.is_blt row 0 = 1 ∨ air.cols.opcode_selector.is_bge row 0 = 1)
      then
        (if (U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)] <
            U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        then 1 else 0)
      else
        (if (U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)] <
            U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        then 1 else 0)
    := by
      obtain ⟨ h_cases, h_store ⟩ := is_branch_instruction_characterisation air row h_is_real h_assumptions h_branch_instr
      simp [ bus_row_assumptions ] at h_assumptions
      replace h_assumptions := h_assumptions.2.1
      simp [
        bus_row,
        h_branch_instr,
        h_is_real,
        cpu_branch_cols_simplification,
      ] at h_assumptions
      replace h_assumptions := h_assumptions.2.2.1
      obtain h | h | h | h | h | h := h_cases <;> split_ifs
      all_goals simp_all [ ALUBus.Spec ]
      all_goals simp [← BitVec.toNat_inj, U32.toNat] at h_assumptions
      all_goals omega

    lemma a_gt_b_meaning
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      air.cols.branch_a_gt_b row 0 =
      if (air.cols.opcode_selector.is_blt row 0 = 1 ∨ air.cols.opcode_selector.is_bge row 0 = 1)
      then
        (if (U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)] <
            U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        then 1 else 0)
      else
        (if (U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)] <
            U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
              BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        then 1 else 0)
    := by
      obtain ⟨ h_cases, h_store ⟩ := is_branch_instruction_characterisation air row h_is_real h_assumptions h_branch_instr
      simp [ bus_row_assumptions ] at h_assumptions
      replace h_assumptions := h_assumptions.2.1
      simp [
        bus_row,
        h_branch_instr,
        h_is_real,
        cpu_branch_cols_simplification,
      ] at h_assumptions
      replace h_assumptions := h_assumptions.2.2.2.1
      obtain h | h | h | h | h | h := h_cases <;> split_ifs
      all_goals simp_all [ ALUBus.Spec ]
      all_goals simp [← BitVec.toNat_inj, U32.toNat] at h_assumptions
      all_goals omega

    lemma a_prev_eq
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_branch_instr : air.cols.is_branch_instruction row 0 = 1)
    :
      air.cols.op_a_access.access.value_0 row 0 = air.cols.op_a_access.prev_value_0 row 0 ∧
      air.cols.op_a_access.access.value_1 row 0 = air.cols.op_a_access.prev_value_1 row 0 ∧
      air.cols.op_a_access.access.value_2 row 0 = air.cols.op_a_access.prev_value_2 row 0 ∧
      air.cols.op_a_access.access.value_3 row 0 = air.cols.op_a_access.prev_value_3 row 0
    := by
      obtain relevant_constraints :
        constraint_24 air row ∧ constraint_25 air row ∧ constraint_26 air row ∧ constraint_27 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        sub_eq_zero,
        h_branch_instr,
      ] at relevant_constraints
      simp [(is_branch_instruction_characterisation air row h_is_real h_assumptions h_branch_instr).2] at relevant_constraints
      assumption

    lemma c_val_eq
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_c_imm : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
      air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
      air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
      air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
    := by
      obtain relevant_constraints :
        constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        sub_eq_zero,
        h_c_imm,
      ] at relevant_constraints
      assumption

  end Auxiliaries

  section BTYPE

    lemma equivalence_BEQ
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 18)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 13 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.BTYPE (imm, reg2, reg1, bop.BEQ)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_assumptions : bus_row_assumptions (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode] at h_opcode_props
      obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_prev_eq air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      -- C-value equalities
      have h_c_val_eq := c_val_eq air row h_constraints (by aesop)
      -- Branching is boolean
      have h_b_branching : constraint_65 air row
        := by simp [allHold_simplified] at h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_branching,
        sub_eq_zero
      ] at h_b_branching
      -- Characterisation of branching
      have h_eq_branching :
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)] =
        U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]) =
        (air.cols.branching row 0 = 1)
      := by
        obtain relevant_constraints
        : constraint_67 air row ∧ constraint_68 air row ∧
          constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧ constraint_78 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          cpu_branch_cols_simplification,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors
        ] at relevant_constraints
        obtain ⟨ h_a_eq_b, h_lt_gt, h_eq_0, h_eq_1, h_eq_2, h_eq_3 ⟩ := relevant_constraints
        have h_lt := a_lt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        have h_gt := a_gt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        simp [h_selectors] at h_lt h_gt
        simp [← BitVec.toNat_inj]
        split_ifs at h_lt <;> split_ifs at h_gt <;> simp_all <;>
        rcases h_b_branching <;> simp_all <;> omega
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_npc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := non_branching_npc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
      -- Proof
      extract_lets reg1 reg2 imm'
      rw [
        OpcodeSpec.RV32.execute_BEQ_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      . simp [
          OpcodeSpec.RV32.spec_BEQ,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [h_prev_eq]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs <;> simp_all
      . intro h_branch
        simp [h_prev_eq, h_eq_branching] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_asm_alu
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real pico_assumptions

    lemma equivalence_BNE
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 19)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 13 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.BTYPE (imm, reg2, reg1, bop.BNE)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_assumptions : bus_row_assumptions (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode] at h_opcode_props
      obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_prev_eq air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      -- C-value equalities
      have h_c_val_eq := c_val_eq air row h_constraints (by aesop)
      -- Branching is boolean
      have h_b_branching : constraint_65 air row
        := by simp [allHold_simplified] at h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_branching,
        sub_eq_zero
      ] at h_b_branching
      -- Characterisation of branching
      have h_eq_branching :
        (¬ (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)] =
        U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])) =
        (air.cols.branching row 0 = 1)
      := by
        obtain relevant_constraints
        : constraint_69 air row ∧ constraint_70 air row ∧
          constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧ constraint_78 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          cpu_branch_cols_simplification,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors
        ] at relevant_constraints
        obtain ⟨ h_a_eq_b, h_lt_gt, h_eq_0, h_eq_1, h_eq_2, h_eq_3 ⟩ := relevant_constraints
        have h_lt := a_lt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        have h_gt := a_gt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        simp [h_selectors] at h_lt h_gt
        simp [← BitVec.toNat_inj]
        split_ifs at h_lt <;> split_ifs at h_gt <;> simp_all <;>
        rcases h_b_branching <;> simp_all <;> omega
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_npc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := non_branching_npc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
      -- Proof
      extract_lets reg1 reg2 imm'
      rw [
        OpcodeSpec.RV32.execute_BNE_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      . simp [
          OpcodeSpec.RV32.spec_BNE,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [h_prev_eq]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs <;> simp_all
      . intro h_branch
        simp [h_prev_eq, h_eq_branching] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_asm_alu
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real pico_assumptions

    lemma equivalence_BLT
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 20)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 13 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.BTYPE (imm, reg2, reg1, bop.BLT)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_assumptions : bus_row_assumptions (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode] at h_opcode_props
      obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_prev_eq air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      -- C-value equalities
      have h_c_val_eq := c_val_eq air row h_constraints (by aesop)
      -- Branching is boolean
      have h_b_branching : constraint_65 air row
        := by simp [allHold_simplified] at h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_branching,
        sub_eq_zero
      ] at h_b_branching
      -- Characterisation of branching
      have h_eq_branching :
        (¬ (U32.toInt
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)] <
        U32.toInt
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])) =
        (air.cols.branching row 0 = 0)
      := by
        obtain relevant_constraints
        : constraint_71 air row ∧ constraint_72 air row ∧
          constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧ constraint_78 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          cpu_branch_cols_simplification,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors
        ] at relevant_constraints
        obtain ⟨ h_a_eq_b, h_lt_gt, h_eq_0, h_eq_1, h_eq_2, h_eq_3 ⟩ := relevant_constraints
        have h_lt := a_lt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        have h_gt := a_gt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_lt_gt <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_npc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := non_branching_npc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
      -- Proof
      extract_lets reg1 reg2 imm'
      rw [
        OpcodeSpec.RV32.execute_BLT_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      . simp [
          OpcodeSpec.RV32.spec_BLT,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [h_prev_eq]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs <;> simp_all
      . intro h_branch
        simp [h_prev_eq] at h_branch
        specialize h_branching_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        specialize h_branching_next_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_asm_alu
        specialize h_asm_alu (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real pico_assumptions

    lemma equivalence_BGE
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 21)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 13 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.BTYPE (imm, reg2, reg1, bop.BGE)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_assumptions : bus_row_assumptions (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode] at h_opcode_props
      obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_prev_eq air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      -- C-value equalities
      have h_c_val_eq := c_val_eq air row h_constraints (by aesop)
      -- Branching is boolean
      have h_b_branching : constraint_65 air row
        := by simp [allHold_simplified] at h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_branching,
        sub_eq_zero
      ] at h_b_branching
      -- Characterisation of branching
      have h_eq_branching :
        (U32.toInt
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)] <
        U32.toInt
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]) =
        (air.cols.branching row 0 = 0)
      := by
        obtain relevant_constraints
        : constraint_73 air row ∧ constraint_74 air row ∧
          constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧ constraint_78 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          cpu_branch_cols_simplification,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors
        ] at relevant_constraints
        obtain ⟨ h_a_eq_b, h_lt_gt, h_eq_0, h_eq_1, h_eq_2, h_eq_3 ⟩ := relevant_constraints
        have h_lt := a_lt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        have h_gt := a_gt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_a_eq_b <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_npc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := non_branching_npc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
      -- Proof
      extract_lets reg1 reg2 imm'
      rw [
        OpcodeSpec.RV32.execute_BGE_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      . simp [
          OpcodeSpec.RV32.spec_BGE,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [h_prev_eq]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs <;> simp_all
      . intro h_branch
        simp [h_prev_eq] at h_branch
        specialize h_branching_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        specialize h_branching_next_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_asm_alu
        specialize h_asm_alu (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real pico_assumptions

    lemma equivalence_BLTU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 22)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 13 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.BTYPE (imm, reg2, reg1, bop.BLTU)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_assumptions : bus_row_assumptions (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode] at h_opcode_props
      obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_prev_eq air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      -- C-value equalities
      have h_c_val_eq := c_val_eq air row h_constraints (by aesop)
      -- Branching is boolean
      have h_b_branching : constraint_65 air row
        := by simp [allHold_simplified] at h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_branching,
        sub_eq_zero
      ] at h_b_branching
      -- Characterisation of branching
      have h_eq_branching :
        (¬ (U32.toNat
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)] <
        U32.toNat
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])) =
        (air.cols.branching row 0 = 0)
      := by
        obtain relevant_constraints
        : constraint_71 air row ∧ constraint_72 air row ∧
          constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧ constraint_78 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          cpu_branch_cols_simplification,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors
        ] at relevant_constraints
        obtain ⟨ h_a_eq_b, h_lt_gt, h_eq_0, h_eq_1, h_eq_2, h_eq_3 ⟩ := relevant_constraints
        have h_lt := a_lt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        have h_gt := a_gt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_lt_gt <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_npc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := non_branching_npc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
      -- Proof
      extract_lets reg1 reg2 imm'
      rw [
        OpcodeSpec.RV32.execute_BLTU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      . simp [
          OpcodeSpec.RV32.spec_BLTU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [h_prev_eq]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs <;> simp_all
      . intro h_branch
        simp [h_prev_eq] at h_branch
        specialize h_branching_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        specialize h_branching_next_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_asm_alu
        specialize h_asm_alu (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real pico_assumptions

    lemma equivalence_BGEU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_assumptions (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 23)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 13 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.BTYPE (imm, reg2, reg1, bop.BGEU)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_assumptions : bus_row_assumptions (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode] at h_opcode_props
      obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_prev_eq air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      -- C-value equalities
      have h_c_val_eq := c_val_eq air row h_constraints (by aesop)
      -- Branching is boolean
      have h_b_branching : constraint_65 air row
        := by simp [allHold_simplified] at h_constraints; aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_branching,
        sub_eq_zero
      ] at h_b_branching
      -- Characterisation of branching
      have h_eq_branching :
        (U32.toNat
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)] <
        U32.toNat
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]) =
        (air.cols.branching row 0 = 0)
      := by
        obtain relevant_constraints
        : constraint_73 air row ∧ constraint_74 air row ∧
          constraint_75 air row ∧ constraint_76 air row ∧ constraint_77 air row ∧ constraint_78 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          cpu_branch_cols_simplification,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors
        ] at relevant_constraints
        obtain ⟨ h_a_eq_b, h_lt_gt, h_eq_0, h_eq_1, h_eq_2, h_eq_3 ⟩ := relevant_constraints
        have h_lt := a_lt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        have h_gt := a_gt_b_meaning air row h_is_real (h_all_assumptions row (by omega)) h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_a_eq_b <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_npc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := non_branching_npc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
      -- Proof
      extract_lets reg1 reg2 imm'
      rw [
        OpcodeSpec.RV32.execute_BGEU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      . simp [
          OpcodeSpec.RV32.spec_BGEU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [h_prev_eq]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs <;> simp_all
      . intro h_branch
        simp [h_prev_eq] at h_branch
        specialize h_branching_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        specialize h_branching_next_pc (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_asm_alu
        specialize h_asm_alu (by clear *- h_b_branching h_eq_branching h_branch; grind)
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real pico_assumptions

  end BTYPE

end Equivalence
