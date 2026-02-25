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

    -- Public value 41 (`next_pc`) holds the starting program
    -- counter for the next chunk. It is either zero (if the last
    -- execution was HALT), or is the first pc of the first row
    -- of the next chunk. In the former case, zero is divisible
    -- by four. In the latter case, `is_real` must hold on the
    -- first row on the next chunk (by constraint 237), and so
    -- that program counter must be on the program bus, meaning
    -- it is divisible by four by the program bus properties.
    axiom Axiom.next_pc_public_value_mod_four_eq_zero
      (air : Valid_CpuAir FKB ExtF)
    :
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
        exact Axiom.next_pc_public_value_mod_four_eq_zero air
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
          exact Axiom.next_pc_public_value_mod_four_eq_zero air
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
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      -- Constraint processing
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at h_constraints
      obtain h_eqs :
        air.cols.ecall_mul_send_to_table row 0 = 0 ∧
        air.cols.ecall_range_check_operand row 0 = 0 ∧
        air.cols.is_sequential_instr row 0 = 0
      := by aesop
      simp [h_eqs] at h_constraints
      replace h_constraints := h_constraints.2

      obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h0, h1, h2, h_eq_a0, h_eq_a1, h_eq_a2,
               h_eq_a3, h3, h4, h5, h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_constraints ⟩ := h_constraints
      clear h0 h1 h2 h3 h4 h5
      obtain ⟨ hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07, hb08, hb09,
               hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
               hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29,
               hb30, hb31, hb32, hb33, hb34, hb35, hb36, hb37, hb38, hb39,
               hb40, hb41, h_constraints ⟩ := h_constraints
      clear h_constraints
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      obtain ⟨ h_npc, h_lt, h_gt ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- More constraints
      have h_eq_pc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
        . simp
        . simp [← hb00, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ h0, h1, h2, h3, hpc0, hpc1, hpc2, hpc3, rest ⟩ := h_npc
            clear *- hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
                     hpc0 hpc1 hpc2
            simp [← hb11, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      have h_eq_npc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
        . simp [h_npc]
        . simp [← hb02, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ hnpc0, hnpc1, hnpc2, hnpc3, h0, h1, h2, h3, rest ⟩ := h_npc
            clear *- hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
                     hnpc0 hnpc1 hnpc2
            simp [← hb25, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      clear hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
            hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
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
        obtain hb34 | hb34 := hb34 <;> simp_all [ALUBus.Spec, ← CpuAir.is_branch_instruction_def]
        split_ifs at h_gt with h_if
        . rw [if_neg (by omega)] at h_lt
          have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
          := by
            clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
            omega
          have h_eq_gt : air.cols.branch_a_gt_b row 0 = 1
          := by
            clear *- h_gt
            simp [← BitVec.toNat_inj, U32.toNat] at h_gt
            omega
          simp_all
          intro h_branch; simp [← BitVec.toNat_inj] at h_branch
          omega
        . intro h_branch
          simp [← BitVec.toNat_inj] at h_branch
          simp [h_branch] at h_lt h_gt
          have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
          := by
            clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
            omega
          have h_eq_gt : air.cols.branch_a_gt_b row 0 = 0
          := by
            clear *- h_gt
            simp [← BitVec.toNat_inj, U32.toNat] at h_gt
            omega
          simp_all
      clear h_lt h_gt
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
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs with h_if
        . simp_all
        . have h_eq_branching : air.cols.branching row 0 = 0
            := by obtain hb34 | hb34 := hb34 <;> simp_all
          simp_all
          simp [← hb32, ← BitVec.toNat_inj, Fin.val_add]
          omega
      . simp [OpcodeSpec.RV32.spec_BEQ, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . intro h_branch
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_eq_branching] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_npc
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_npc.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real

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
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      -- Constraint processing
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at h_constraints
      obtain h_eqs :
        air.cols.ecall_mul_send_to_table row 0 = 0 ∧
        air.cols.ecall_range_check_operand row 0 = 0 ∧
        air.cols.is_sequential_instr row 0 = 0
      := by aesop
      simp [h_eqs] at h_constraints
      replace h_constraints := h_constraints.2

      obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h0, h1, h2, h_eq_a0, h_eq_a1, h_eq_a2,
               h_eq_a3, h3, h4, h5, h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_constraints ⟩ := h_constraints
      clear h0 h1 h2 h3 h4 h5
      obtain ⟨ hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07, hb08, hb09,
               hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
               hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29,
               hb30, hb31, hb32, hb33, hb34, hb35, hb36, hb37, hb38, hb39,
               hb40, hb41, h_constraints ⟩ := h_constraints
      clear h_constraints
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      obtain ⟨ h_npc, h_lt, h_gt ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- More constraints
      have h_eq_pc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
        . simp
        . simp [← hb00, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ h0, h1, h2, h3, hpc0, hpc1, hpc2, hpc3, rest ⟩ := h_npc
            clear *- hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
                     hpc0 hpc1 hpc2
            simp [← hb11, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      have h_eq_npc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
        . simp [h_npc]
        . simp [← hb02, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ hnpc0, hnpc1, hnpc2, hnpc3, h0, h1, h2, h3, rest ⟩ := h_npc
            clear *- hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
                     hnpc0 hnpc1 hnpc2
            simp [← hb25, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      clear hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
            hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
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
        obtain hb34 | hb34 := hb34 <;> simp_all [ALUBus.Spec, ← CpuAir.is_branch_instruction_def]
        split_ifs at h_gt with h_if
        . rw [if_neg (by omega)] at h_lt
          have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
          := by
            clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
            omega
          have h_eq_gt : air.cols.branch_a_gt_b row 0 = 1
          := by
            clear *- h_gt
            simp [← BitVec.toNat_inj, U32.toNat] at h_gt
            omega
          simp_all
          intro h_branch; simp [← BitVec.toNat_inj] at h_branch
          omega
        . intro h_branch
          simp [← BitVec.toNat_inj] at h_branch
          simp [h_branch] at h_lt h_gt
          have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
          := by
            clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
            omega
          have h_eq_gt : air.cols.branch_a_gt_b row 0 = 0
          := by
            clear *- h_gt
            simp [← BitVec.toNat_inj, U32.toNat] at h_gt
            omega
          simp_all
      clear h_lt h_gt
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
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs with h_if
        . have h_eq_branching : air.cols.branching row 0 = 0
            := by obtain hb34 | hb34 := hb34 <;> simp_all
          simp_all
          simp [← hb32, ← BitVec.toNat_inj, Fin.val_add]
          omega
        . simp_all
      . simp [OpcodeSpec.RV32.spec_BNE, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . intro h_branch
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_eq_branching] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_npc
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_npc.2.2.2.2.2.2.2.2.2.2.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions h_all_constraints row h_row h_is_real

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
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      -- Constraint processing
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at h_constraints
      obtain h_eqs :
        air.cols.ecall_mul_send_to_table row 0 = 0 ∧
        air.cols.ecall_range_check_operand row 0 = 0 ∧
        air.cols.is_sequential_instr row 0 = 0
      := by aesop
      simp [h_eqs] at h_constraints
      replace h_constraints := h_constraints.2

      obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h0, h1, h2, h_eq_a0, h_eq_a1, h_eq_a2,
               h_eq_a3, h3, h4, h5, h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_constraints ⟩ := h_constraints
      clear h0 h1 h2 h3 h4 h5
      obtain ⟨ hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07, hb08, hb09,
               hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
               hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29,
               hb30, hb31, hb32, hb33, hb34, hb35, hb36, hb37, hb38, hb39,
               hb40, hb41, h_constraints ⟩ := h_constraints
      clear h_constraints
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      obtain ⟨ h_npc, h_lt, h_gt ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- More constraints
      have h_eq_pc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
        . simp
        . simp [← hb00, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ h0, h1, h2, h3, hpc0, hpc1, hpc2, hpc3, rest ⟩ := h_npc
            clear *- hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
                     hpc0 hpc1 hpc2
            simp [← hb11, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      have h_eq_npc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
        . simp [h_npc]
        . simp [← hb02, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ hnpc0, hnpc1, hnpc2, hnpc3, h0, h1, h2, h3, rest ⟩ := h_npc
            clear *- hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
                     hnpc0 hnpc1 hnpc2
            simp [← hb25, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      clear hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
            hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
      have h_eq_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toInt <
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toInt) =
        (air.cols.branching row 0 = 1)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all [ALUBus.Spec, ← CpuAir.is_branch_instruction_def]
        . simp_all
          split_ifs at h_gt with h_if
          . rw [if_neg (by clear *- h_if; omega)] at h_lt
            have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
            := by
              clear *- h_lt
              simp [← BitVec.toNat_inj, U32.toNat] at h_lt
              omega
            have h_eq_gt : air.cols.branch_a_gt_b row 0 = 1
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
            clear *- h_if; omega
          . have h_eq_gt : air.cols.branch_a_gt_b row 0 = 0
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
        . simp_all
          split_ifs at h_lt with h_if
          . assumption
          . exfalso; clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
      have h_eq_not_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toInt ≤
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toInt) =
        (air.cols.branching row 0 = 0)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all
      clear h_lt h_gt
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
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs with h_if
        . simp_all
          simp [← hb32, ← BitVec.toNat_inj, Fin.val_add]
          omega
        . simp_all
      . simp [OpcodeSpec.RV32.spec_BLT, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . intro h_branch
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_npc
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        simp_all
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real

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
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      -- Constraint processing
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at h_constraints
      obtain h_eqs :
        air.cols.ecall_mul_send_to_table row 0 = 0 ∧
        air.cols.ecall_range_check_operand row 0 = 0 ∧
        air.cols.is_sequential_instr row 0 = 0
      := by aesop
      simp [h_eqs] at h_constraints
      replace h_constraints := h_constraints.2

      obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h0, h1, h2, h_eq_a0, h_eq_a1, h_eq_a2,
               h_eq_a3, h3, h4, h5, h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_constraints ⟩ := h_constraints
      clear h0 h1 h2 h3 h4 h5
      obtain ⟨ hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07, hb08, hb09,
               hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
               hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29,
               hb30, hb31, hb32, hb33, hb34, hb35, hb36, hb37, hb38, hb39,
               hb40, hb41, h_constraints ⟩ := h_constraints
      clear h_constraints
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      obtain ⟨ h_npc, h_lt, h_gt ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- More constraints
      have h_eq_pc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
        . simp
        . simp [← hb00, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ h0, h1, h2, h3, hpc0, hpc1, hpc2, hpc3, rest ⟩ := h_npc
            clear *- hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
                     hpc0 hpc1 hpc2
            simp [← hb11, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      have h_eq_npc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
        . simp [h_npc]
        . simp [← hb02, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ hnpc0, hnpc1, hnpc2, hnpc3, h0, h1, h2, h3, rest ⟩ := h_npc
            clear *- hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
                     hnpc0 hnpc1 hnpc2
            simp [← hb25, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      clear hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
            hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
      have h_eq_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toInt ≥
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toInt) =
        (air.cols.branching row 0 = 1)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all [ALUBus.Spec, ← CpuAir.is_branch_instruction_def]
        . simp_all
          split_ifs at h_lt with h_if
          . assumption
          . exfalso; clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
        . simp_all
          split_ifs at h_gt with h_if
          . rw [if_neg (by clear *- h_if; omega)] at h_lt
            have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
            := by
              clear *- h_lt
              simp [← BitVec.toNat_inj, U32.toNat] at h_lt
              omega
            have h_eq_gt : air.cols.branch_a_gt_b row 0 = 1
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
            clear *- h_if; omega
          . have h_eq_gt : air.cols.branch_a_gt_b row 0 = 0
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
      have h_eq_not_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toInt <
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toInt) =
        (air.cols.branching row 0 = 0)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all
      clear h_lt h_gt
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
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs with h_if
        . simp_all
          simp [← hb32, ← BitVec.toNat_inj, Fin.val_add]
          omega
        . simp_all
      . simp [OpcodeSpec.RV32.spec_BGE, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . intro h_branch
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_npc
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        simp_all
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real

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
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      -- Constraint processing
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at h_constraints
      obtain h_eqs :
        air.cols.ecall_mul_send_to_table row 0 = 0 ∧
        air.cols.ecall_range_check_operand row 0 = 0 ∧
        air.cols.is_sequential_instr row 0 = 0
      := by aesop
      simp [h_eqs] at h_constraints
      replace h_constraints := h_constraints.2

      obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h0, h1, h2, h_eq_a0, h_eq_a1, h_eq_a2,
               h_eq_a3, h3, h4, h5, h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_constraints ⟩ := h_constraints
      clear h0 h1 h2 h3 h4 h5
      obtain ⟨ hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07, hb08, hb09,
               hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
               hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29,
               hb30, hb31, hb32, hb33, hb34, hb35, hb36, hb37, hb38, hb39,
               hb40, hb41, h_constraints ⟩ := h_constraints
      clear h_constraints
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      obtain ⟨ h_npc, h_lt, h_gt ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- More constraints
      have h_eq_pc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
        . simp
        . simp [← hb00, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ h0, h1, h2, h3, hpc0, hpc1, hpc2, hpc3, rest ⟩ := h_npc
            clear *- hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
                     hpc0 hpc1 hpc2
            simp [← hb11, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      have h_eq_npc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
        . simp [h_npc]
        . simp [← hb02, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ hnpc0, hnpc1, hnpc2, hnpc3, h0, h1, h2, h3, rest ⟩ := h_npc
            clear *- hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
                     hnpc0 hnpc1 hnpc2
            simp [← hb25, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      clear hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
            hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
      have h_eq_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toNat <
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toNat) =
        (air.cols.branching row 0 = 1)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all [ALUBus.Spec, ← CpuAir.is_branch_instruction_def]
        . simp_all
          split_ifs at h_gt with h_if
          . rw [if_neg (by omega)] at h_lt
            have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
            := by
              clear *- h_lt
              simp [← BitVec.toNat_inj, U32.toNat] at h_lt
              omega
            have h_eq_gt : air.cols.branch_a_gt_b row 0 = 1
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
            omega
          . have h_eq_gt : air.cols.branch_a_gt_b row 0 = 0
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
        . simp_all
          split_ifs at h_lt with h_if
          . assumption
          . exfalso; clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
      have h_eq_not_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toNat ≤
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toNat) =
        (air.cols.branching row 0 = 0)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all
      clear h_lt h_gt
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
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs with h_if
        . simp_all
          simp [← hb32, ← BitVec.toNat_inj, Fin.val_add]
          omega
        . simp_all
      . simp [OpcodeSpec.RV32.spec_BLTU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . intro h_branch
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_npc
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        simp_all
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real

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
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      -- Constraint processing
      simp [
        pico_encapsulation,
        cpu_branch_cols_simplification,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at h_constraints
      obtain h_eqs :
        air.cols.ecall_mul_send_to_table row 0 = 0 ∧
        air.cols.ecall_range_check_operand row 0 = 0 ∧
        air.cols.is_sequential_instr row 0 = 0
      := by aesop
      simp [h_eqs] at h_constraints
      replace h_constraints := h_constraints.2

      obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h0, h1, h2, h_eq_a0, h_eq_a1, h_eq_a2,
               h_eq_a3, h3, h4, h5, h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3, h_constraints ⟩ := h_constraints
      clear h0 h1 h2 h3 h4 h5
      obtain ⟨ hb00, hb01, hb02, hb03, hb04, hb05, hb06, hb07, hb08, hb09,
               hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19,
               hb20, hb21, hb22, hb23, hb24, hb25, hb26, hb27, hb28, hb29,
               hb30, hb31, hb32, hb33, hb34, hb35, hb36, hb37, hb38, hb39,
               hb40, hb41, h_constraints ⟩ := h_constraints
      clear h_constraints
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_branch_cols_simplification,
      ] at h_asm_alu
      obtain ⟨ h_npc, h_lt, h_gt ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- More constraints
      have h_eq_pc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_pc 3 air.cols row 0)]
        . simp
        . simp [← hb00, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ h0, h1, h2, h3, hpc0, hpc1, hpc2, hpc3, rest ⟩ := h_npc
            clear *- hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
                     hpc0 hpc1 hpc2
            simp [← hb11, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      have h_eq_npc_bv :
        air.cols.branching row 0 = 1 →
          U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                      BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
      := by
        intro h_branching; simp_all [ALUBus.Spec]
        trans U32.toBV #v[BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 0 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 1 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 2 air.cols row 0),
                          BitVec.ofNat 8 ↑(Valid_CpuCols.branch_next_pc 3 air.cols row 0)]
        . simp [h_npc]
        . simp [← hb02, ← BitVec.toNat_inj, U32.toNat]
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by clear *- h_npc; omega)]
          simp [Fin.val_add, Fin.val_mul]
          rw [Nat.mod_eq_of_lt]
          . omega
          . obtain ⟨ hnpc0, hnpc1, hnpc2, hnpc3, h0, h1, h2, h3, rest ⟩ := h_npc
            clear *- hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
                     hnpc0 hnpc1 hnpc2
            simp [← hb25, Fin.val_add, Fin.val_mul]
            rw [Nat.mod_eq_of_lt (by grind)]
            grind
      clear hb02 hb03 hb04 hb05 hb06 hb07 hb08 hb09 hb11 hb12 hb13 hb14 hb15 hb16
            hb17 hb18 hb19 hb20 hb21 hb22 hb23 hb25 hb26 hb27 hb28 hb29 hb30
      have h_eq_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toNat ≥
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toNat) =
        (air.cols.branching row 0 = 1)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all [ALUBus.Spec, ← CpuAir.is_branch_instruction_def]
        . simp_all
          split_ifs at h_lt with h_if
          . assumption
          . exfalso; clear *- h_lt
            simp [← BitVec.toNat_inj, U32.toNat] at h_lt
        . simp_all
          split_ifs at h_gt with h_if
          . rw [if_neg (by omega)] at h_lt
            have h_eq_lt : air.cols.branch_a_lt_b row 0 = 0
            := by
              clear *- h_lt
              simp [← BitVec.toNat_inj, U32.toNat] at h_lt
              omega
            have h_eq_gt : air.cols.branch_a_gt_b row 0 = 1
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
            omega
          . have h_eq_gt : air.cols.branch_a_gt_b row 0 = 0
            := by
              clear *- h_gt
              simp [← BitVec.toNat_inj, U32.toNat] at h_gt
              omega
            simp_all
      have h_eq_not_branching :
        ((U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_a_access.prev_value_3 row 0)]).toNat <
        (U32.toBV
          #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
             BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]).toNat) =
        (air.cols.branching row 0 = 0)
      := by
        obtain hb34 | hb34 := hb34 <;> simp_all
      clear h_lt h_gt
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
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        congr
        split_ifs with h_if
        . simp_all
          simp [← hb32, ← BitVec.toNat_inj, Fin.val_add]
          omega
        . simp_all
      . simp [OpcodeSpec.RV32.spec_BGEU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . intro h_branch
        simp [h_eq_pa0, h_eq_pa1, h_eq_pa2, h_eq_pa3] at h_branch
        simp [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, *] at h_npc
        simp [
          *,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        simp_all
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real

  end BTYPE

end Equivalence
