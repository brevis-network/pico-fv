import PicoFV.Constraints.CpuAir

import PicoFV.RVSail.RV32IM.Opcodes.Opcodes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

namespace Equivalence

  open Plonky3

  open RV32IM
  open RV32IM_Interactions
  open CpuAir.ConstraintsAndBuses
  open CpuAir.Interactions
  open CpuAir.Interpretations

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
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
          have instruction_breakdown := instruction_breakdown air row h_is_real (h_wf row h_row) (by simp; exact h_constraints)
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
          . obtain h | h | h | h := instruction_breakdown
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
            . exfalso
              obtain relevant_constraints
              : constraint_215 air row
              := by
                simp [allHold_simplified] at h_constraints
                grind
              simp [constraint_and_interaction_simplification, cpu_ecall_cols_simplification, *] at relevant_constraints
              have := opcode_selectors_breakdown air row h_is_real (h_wf row h_row) (by simp; exact h_constraints)
              omega

  end Auxiliaries

  section RTYPE

    lemma equivalence_ADD
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.ADD)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_ADD_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_ADD,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SUB
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 1 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SUB)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SUB_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SUB,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_XOR
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 2 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.XOR)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_XOR_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_XOR,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_OR
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 3 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.OR)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_OR_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_OR,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_AND
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 4 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.AND)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_AND_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_AND,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SLL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 5 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SLL)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SLL_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SLL,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SRL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 6 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SRL)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SRL_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SRL,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SRA
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 7 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SRA)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SRA_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SRA,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SLT
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 8 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SLT)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SLT_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SLT,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      . -- Case split
        split_ifs <;> decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SLTU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 9 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SLTU)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SLTU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SLTU,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      . -- Case split
        split_ifs <;> decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

  end RTYPE

  section ITYPE

    lemma equivalence_ADDI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 0 ∧ air.cols.opcode_selector.imm_b row 0 = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.ITYPE (imm, reg1, reg0, iop.ADDI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_ADDI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_ADDI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [relevant_constraints, h_c0, h_c1, h_c2, h_c3]
        simp [Transpiler.imm_to_KB_BV_sgn]
        bv_decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_XORI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 2 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.ITYPE (imm, reg1, reg0, iop.XORI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_XORI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_XORI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [relevant_constraints, h_c0, h_c1, h_c2, h_c3]
        simp [Transpiler.imm_to_KB_BV_sgn]
        bv_decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_ORI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 3 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.ITYPE (imm, reg1, reg0, iop.ORI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_ORI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_ORI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [relevant_constraints, h_c0, h_c1, h_c2, h_c3]
        simp [Transpiler.imm_to_KB_BV_sgn]
        bv_decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_ANDI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 4 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.ITYPE (imm, reg1, reg0, iop.ANDI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_ANDI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_ANDI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [relevant_constraints, h_c0, h_c1, h_c2, h_c3]
        simp [Transpiler.imm_to_KB_BV_sgn]
        bv_decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SLTI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 8 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.ITYPE (imm, reg1, reg0, iop.SLTI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SLTI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SLTI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [relevant_constraints, h_c0, h_c1, h_c2, h_c3]
        simp [
          Transpiler.imm_to_KB_BV_sgn,
          Transpiler.imm_to_KB_Int_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        split_ifs <;> decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SLTIU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 9 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.ITYPE (imm, reg1, reg0, iop.SLTIU)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SLTIU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SLTIU,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [relevant_constraints, h_c0, h_c1, h_c2, h_c3]
        simp [
          Transpiler.imm_to_KB_BV_sgn,
          Transpiler.imm_to_KB_Nat_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        split_ifs <;> decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

  end ITYPE

  section SHIFTIOP

    lemma equivalence_SLLI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 5 ∧ air.cols.opcode_selector.imm_b row 0 = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 6 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.SHIFTIOP (imm, reg1, reg0, sop.SLLI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SLLI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SLLI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SRLI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 6 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 6 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.SHIFTIOP (imm, reg1, reg0, sop.SRLI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SRLI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SRLI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

    lemma equivalence_SRAI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 7 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 6 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.SHIFTIOP (imm, reg1, reg0, sop.SRAI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_SRAI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
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
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_SRAI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, operand_ranges ] at h_asm_alu
      rw [h_asm_alu]
      -- Check for differences
      congr
      -- Get the upper bound on the pc
      simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
      -- Isolate relevant constraints
      have relevant_constraints :
        constraint_229 air row ∧ constraint_231 air row
      := by
        simp [allHold_simplified] at h_constraints
        aesop
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        h_is_real,
        h_selectors,
        sub_eq_zero
      ] at relevant_constraints
      clear *- h_axioms relevant_constraints
      simp [← BitVec.toNat_inj]; grind

  end SHIFTIOP

  section MUL

    lemma equivalence_MUL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 30)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.MUL (reg2, reg1, reg0, { result_part := VectorHalf.Low, signed_rs1 := sl, signed_rs2 := sr })) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, sl, sr, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_MUL_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_MUL,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_MULH
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 31)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.MUL (reg2, reg1, reg0, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Signed })) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_MULH_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_MULH,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_MULHU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 32)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.MUL (reg2, reg1, reg0, { result_part := VectorHalf.High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_MULHU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_MULHU,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_MULHSU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 33)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.MUL (reg2, reg1, reg0, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_MULHSU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_MULHSU,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

  end MUL

  section DIV

    lemma equivalence_DIV
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 34)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.DIV (reg2, reg1, reg0, false)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_DIV_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_DIV,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_DIVU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 35)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.DIV (reg2, reg1, reg0, true)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_DIVU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_DIVU,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

  end DIV

  section REM

    lemma equivalence_REM
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 36)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.REM (reg2, reg1, reg0, false)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_REM_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_REM,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_REMU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 37)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.REM (reg2, reg1, reg0, true)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same (by tauto)] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV32.execute_REMU_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (r1_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (r2_val :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
               BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)])
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_REMU,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1,
        h_reg_rs2
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      simp [operation_list_effect_state_writeReg_same h_reg1]
      simp [operation_list_effect_state_writeReg_same h_reg2]
      congr 3
      . -- The specification is verbatim on the ALU bus
        replace h_asm_alu := h_asm_alu.1
        simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
        aesop
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

  end REM

  section BTYPE

    lemma equivalence_BEQ
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_unchanged air row h_is_real (h_all_assumptions row h_row) h_constraints (by left; exact h_is_branching)
      -- C-value equalities
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
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
        have h_lt := branch_instruction_a_lt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        have h_gt := branch_instruction_a_gt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        simp [h_selectors] at h_lt h_gt
        simp [← BitVec.toNat_inj]
        split_ifs at h_lt <;> split_ifs at h_gt <;> simp_all <;>
        rcases h_b_branching <;> simp_all <;> omega
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := not_branching_next_pc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
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
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_branching_pc h_branching_next_pc h_non_branching_npc ⊢
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
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

    lemma equivalence_BNE
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_unchanged air row h_is_real (h_all_assumptions row h_row) h_constraints (by left; exact h_is_branching)
      -- C-value equalities
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
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
        have h_lt := branch_instruction_a_lt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        have h_gt := branch_instruction_a_gt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        simp [h_selectors] at h_lt h_gt
        simp [← BitVec.toNat_inj]
        split_ifs at h_lt <;> split_ifs at h_gt <;> simp_all <;>
        rcases h_b_branching <;> simp_all <;> omega
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := not_branching_next_pc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
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
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_branching_pc h_branching_next_pc h_non_branching_npc ⊢
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
        simp_all [
          ALUBus.Spec,
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

    lemma equivalence_BLT
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_unchanged air row h_is_real (h_all_assumptions row h_row) h_constraints (by left; exact h_is_branching)
      -- C-value equalities
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
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
        have h_lt := branch_instruction_a_lt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        have h_gt := branch_instruction_a_gt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_lt_gt <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := not_branching_next_pc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
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
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_branching_pc h_branching_next_pc h_non_branching_npc ⊢
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
        simp_all [
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

    lemma equivalence_BGE
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_unchanged air row h_is_real (h_all_assumptions row h_row) h_constraints (by left; exact h_is_branching)
      -- C-value equalities
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
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
        have h_lt := branch_instruction_a_lt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        have h_gt := branch_instruction_a_gt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_a_eq_b <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := not_branching_next_pc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
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
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_branching_pc h_branching_next_pc h_non_branching_npc ⊢
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
        simp_all [
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

    lemma equivalence_BLTU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_unchanged air row h_is_real (h_all_assumptions row h_row) h_constraints (by left; exact h_is_branching)
      -- C-value equalities
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
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
        have h_lt := branch_instruction_a_lt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        have h_gt := branch_instruction_a_gt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_lt_gt <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := not_branching_next_pc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
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
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_branching_pc h_branching_next_pc h_non_branching_npc ⊢
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
        simp_all [
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

    lemma equivalence_BGEU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Branching
      have h_is_branching : air.cols.is_branch_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_branch_instruction, h_selectors]
      -- Previous a-equalities
      have h_prev_eq := a_unchanged air row h_is_real (h_all_assumptions row h_row) h_constraints (by left; exact h_is_branching)
      -- C-value equalities
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
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
        have h_lt := branch_instruction_a_lt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        have h_gt := branch_instruction_a_gt_b air row h_is_real (h_all_assumptions row (by omega)) h_constraints h_is_branching
        simp [h_selectors] at h_lt h_gt
        split_ifs at h_lt with h_if_lt <;> split_ifs at h_gt with h_if_gt <;> simp_all
        . clear *- h_if_lt h_if_gt; omega
        . rcases h_a_eq_b <;> simp_all
      -- Program counter characterisation
      have h_branching_pc := branching_pc air row (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_branching_next_pc := branching_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints h_is_branching
      have h_non_branching_npc := not_branching_next_pc air row h_is_real (h_all_axioms row h_row) h_constraints h_is_branching
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
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_branching_pc h_branching_next_pc h_non_branching_npc ⊢
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
        simp_all [
          Transpiler.imm_to_KB_BV_sgn,
          show BitVec.signExtend 32 (BitVec.setWidth 13 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide
        ]
        rw [← h_asm_alu.2.2]
        simp [← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

  end BTYPE

  instance : LawfulBEq regidx where
    rfl := by intro ⟨ op, pf ⟩; simp at pf; interval_cases op <;> rfl
    eq_of_beq := by
      intro ⟨ op₁, pf₁ ⟩ ⟨ op₂, pf₂ ⟩
      simp at pf₁ pf₂
      interval_cases op₁ <;> interval_cases op₂ <;> simp <;> rfl

  section JTYPE

    instance : LawfulBEq regidx where
      rfl := by intro ⟨ op, pf ⟩; simp at pf; interval_cases op <;> rfl
      eq_of_beq := by
        intro ⟨ op₁, pf₁ ⟩ ⟨ op₂, pf₂ ⟩
        simp at pf₁ pf₂
        interval_cases op₁ <;> interval_cases op₂ <;> simp

    lemma equivalence_JAL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 24)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg1 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let imm : BitVec 21 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)]
      execute_instruction (instruction.JAL (imm, reg1)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
      obtain ⟨ imm, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_imm_mod_2 ⟩ := h_eq_props
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        cpu_jump_cols_simplification,
      ] at h_asm_alu
      have h_asm_alu_jal := h_asm_alu.2
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Jump constraints
      have h_is_jump : air.cols.is_jump_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_jump_instruction, h_selectors]
      -- B-value equalities (immediate via constraints 0-3)
      have h_b_val_eq : air.cols.op_b_access.value_0 row 0 = air.cols.instruction.b_0 row 0 ∧
                         air.cols.op_b_access.value_1 row 0 = air.cols.instruction.b_1 row 0 ∧
                         air.cols.op_b_access.value_2 row 0 = air.cols.instruction.b_2 row 0 ∧
                         air.cols.op_b_access.value_3 row 0 = air.cols.instruction.b_3 row 0
      := by
        obtain relevant_constraints
        : constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row ∧ constraint_3 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          h_selectors,
        ] at relevant_constraints
        assumption
      -- Jump-specific constraints
      have h_constraint_80 : constraint_80 air row := by
        simp [allHold_simplified] at h_constraints; aesop
      have h_constraint_81 : constraint_81 air row := by
        simp [allHold_simplified] at h_constraints; aesop
      have h_constraint_83 : constraint_83 air row := by
        simp [allHold_simplified] at h_constraints; aesop
      simp [constraint_and_interaction_simplification, cpu_jump_cols_simplification, h_selectors, h_is_real] at h_constraint_80 h_constraint_81 h_constraint_83
      -- Auxiliaries
      have h_jpc_eq := jal_pc air row (h_all_assumptions row h_row) h_constraints
          (by simp [h_selectors])
      have h_jnpc_eq := jump_next_pc air row h_is_real (h_all_assumptions row h_row) h_constraints
      have h_alu := h_asm_alu_jal.2.2
      clear h_asm_alu h_asm_alu_jal
      -- BitVec extension
      have h_se : BitVec.signExtend 32 (BitVec.setWidth 21 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm := by bv_decide
      -- Proof
      extract_lets reg1 imm'
      rw [
        OpcodeSpec.RV32.execute_JAL_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (imm :=
          U32.toBV
            #v[BitVec.ofNat 8 ↑(air.cols.op_b_access.value_0 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_1 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_2 row 0),
                BitVec.ofNat 8 ↑(air.cols.op_b_access.value_3 row 0)])
        (misa := misa)
        (h_misa := by clear *- risc_v_assumptions; tauto)
        (by split_ands <;> aesop)
      ]
      -- Goal 1: States match
      . simp [
          OpcodeSpec.RV32.spec_JAL,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
          h_reg_rd
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_jpc_eq h_jnpc_eq ⊢
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp_all [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, sub_eq_zero]
        -- Branch on zero or non-zero register write
        subst reg1
        replace h_constraint_80 :
           air.cols.instruction.a_is_0 row 0 - 1 = 0 ∨
           (air.cols.instruction.a_is_0 row 0 = 0 ∧
            air.cols.op_a_access.access.value_0 row 0 + 256 * air.cols.op_a_access.access.value_1 row 0 + 65536 * air.cols.op_a_access.access.value_2 row 0 + 16777216 * air.cols.op_a_access.access.value_3 row 0 - (air.cols.pc row 0 + 4) = 0)
        := by
          simp [h_a_is_0]
          clear *- h_constraint_80
          grind
        rcases h_constraint_80 with h_x0 | ⟨ h_nx0, h_val ⟩
        . simp [h_a_is_0] at h_x0
          split_ifs at h_x0 with h_if_x0 <;> simp at h_x0 h_if_x0
          subst rd
          simp [
            operation_list_effect,
            operation_effect,
            h_a0,
            write_xreg,
            Transpiler.reg_to_KB,
            regidx_to_fin
          ]
        . rw [jump_pc_plus_four air row h_is_real
                (h_all_assumptions row h_row)
                (by simp; exact (h_all_constraints row h_row))
                (by simp [Valid_CpuCols.is_jump_instruction, h_selectors])
                h_nx0
              ]
          congr
          simp [← BitVec.toNat_inj]; omega
      . obtain ⟨ h_eq_b0, h_eq_b1, h_eq_b2, h_eq_b3 ⟩ := h_b_val_eq
        simp_all [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, sub_eq_zero]
        simp [← h_alu.2.2, ← BitVec.toNat_inj]
        exact next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions
          (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions

    lemma equivalence_JALR
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_assumptions : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 25)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (pico_assumptions : pico_CpuAir_control_flow_assumptions air)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let imm : BitVec 12 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                         BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)]
      execute_instruction (instruction.JALR (imm, reg1, reg0)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_axioms : bus_row_axioms (bus_row air row) := by specialize h_all_axioms row (by omega); assumption
      have h_wf : bus_row_wf_asm (bus_row air row) := by specialize h_all_assumptions row (by omega); assumption
      have h_constraints : CpuAir.Extraction.allHold air row := by specialize h_all_constraints row (by omega); assumption
      have operand_ranges := operand_range air row h_is_real h_wf h_constraints
      -- Axioms
      simp [ bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
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
      obtain ⟨ imm', rs1', rd', h_eq_instr ⟩ := h_opcode_props
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
        cpu_jump_cols_simplification,
      ] at h_asm_alu
      have h_asm_alu_jalr := h_asm_alu.2
      replace h_asm_alu := h_asm_alu.1
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd,
        h_reg_rs1
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg2] at h_reg1
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
      -- RISC-V assumptions
      simp [RISC_V_assumptions] at risc_v_assumptions
      -- Jump constraints
      have h_is_jump : air.cols.is_jump_instruction row 0 = 1
        := by simp [Valid_CpuCols.is_jump_instruction, h_selectors]
      -- C-value equalities (immediate)
      have h_c_val_eq := imm_c_eqs air row h_constraints (by aesop)
      -- Jump-specific constraints
      have h_constraint_80 : constraint_80 air row := by
        simp [allHold_simplified] at h_constraints; aesop
      have h_constraint_83 : constraint_83 air row := by
        simp [allHold_simplified] at h_constraints; aesop
      simp [constraint_and_interaction_simplification, cpu_jump_cols_simplification, h_selectors, h_is_real] at h_constraint_80 h_constraint_83
      -- Auxiliaries
      have h_alu := h_asm_alu_jalr.2.2
      clear h_asm_alu h_asm_alu_jalr
      -- Proof
      extract_lets reg0 reg1 imm_val
      rw [
        OpcodeSpec.RV32.execute_JALR_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (rs1_val :=
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
        (h_cur_privilege := by clear *- risc_v_assumptions; tauto)
        (h_mseccfg := by tauto)
        (by split_ands <;> aesop)
      ]
      -- Goal 1: States match
      . simp [
          OpcodeSpec.RV32.spec_JALR,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
          h_reg_rd,
          h_reg_rs1
        ]
        simp [BitVec.ofNatLT_eq_ofNat] at h_alu ⊢
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp_all [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, sub_eq_zero]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        -- Sign extension round-trip
        have h_se : BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 32 imm')) = BitVec.signExtend 32 imm' := by bv_decide
        rw [h_se]
        -- Rewrite using ALU equality
        rw [← h_alu.2]
        -- Establish jump_next_pc_bv = next_pc_bv and mask identity
        have h_jnpc_eq := jump_next_pc air row h_is_real (h_all_assumptions row h_row) (by simp; exact h_all_constraints row h_row) h_is_jump
        rw [h_jnpc_eq]
        -- Mask &&& next_pc = next_pc (since next_pc % 4 = 0)
        have h_mod4 := next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions
            (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions
        have h_mask_eq : 4294967294#32 &&& BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega)
            = BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega) := by
          have h_bit0 : (BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega))[0] = false := by
            simp [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNatLT]; omega
          bv_decide
        rw [h_mask_eq]
        simp [BitVec.ofNatLT_eq_ofNat] at h_jnpc_eq ⊢
        -- Now WritePC values match. Handle WriteReg via constraint_80.
        subst reg0
        by_cases h_x0 : rd' = regidx.Regidx 0#5
        . subst rd'
          simp [
            operation_list_effect,
            operation_effect,
            h_a0,
            write_xreg,
            Transpiler.reg_to_KB,
            regidx_to_fin,
          ]
        . have h_a_not_0 : air.cols.instruction.a_is_0 row 0 = 0 := by
            simp only [h_a_is_0]
            rw [show (rd' == regidx.Regidx 0#5) = false from beq_eq_false_iff_ne.mpr h_x0]
            simp
          rw [jump_pc_plus_four air row h_is_real
                (h_all_assumptions row h_row)
                (by simp; exact (h_all_constraints row h_row))
                (by simp [Valid_CpuCols.is_jump_instruction, h_selectors])
                h_a_not_0]
          congr
          simp [← BitVec.toNat_inj]; omega
      -- Goal 2: Success condition (alignment)
      . obtain ⟨ h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ := h_c_val_eq
        simp_all [ALUBus.Spec, Transpiler.imm_to_KB_BV_sgn, sub_eq_zero]
        -- Sign extension round-trip
        have h_se : BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 32 imm')) = BitVec.signExtend 32 imm' := by bv_decide
        simp [h_se]
        -- Rewrite to jump_next_pc_bv using ALU equality
        simp [← h_alu.2]
        -- Establish jump_next_pc_bv = next_pc_bv
        have h_jnpc_eq := jump_next_pc air row h_is_real (h_all_assumptions row h_row) (by simp; exact h_all_constraints row h_row) h_is_jump
        simp [h_jnpc_eq]
        -- BitVec.ofBool next_pc_bv[1] = 0#1
        have h_mod4 := next_pc_mod_four_eq_zero air h_all_axioms h_all_assumptions
            (by simp; exact h_all_constraints) row h_row h_is_real pico_assumptions
        have h_bit1 : (BitVec.ofNatLT (w := 32) (air.cols.next_pc row 0).val (by omega))[1] = false := by
          simp [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNatLT, Nat.testBit]; omega
        simp [h_bit1]

  end JTYPE

  section UTYPE

    lemma equivalence_LUI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 0 ∧ air.cols.opcode_selector.imm_b row 0 = 1 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let imm : BitVec 20 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)] >>> 12
      execute_instruction (instruction.UTYPE (imm, reg0, uop.LUI)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ imm, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_imm_mod ⟩ := h_eq_props
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 imm'
      rw [
        OpcodeSpec.RV32.execute_LUI_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_LUI,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      -- Prepare the ALU assumptions
      replace h_asm_alu := h_asm_alu.1
      simp [ h_opcode, h_selectors, ALUBus.Spec, and_assoc ] at h_asm_alu
      rw [h_asm_alu.2.2.2.2.2.2.2.2.2.2.2.2]
      -- Check for differences
      congr
      . -- Isolate relevant constraints
        have relevant_constraints :
          constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row ∧ constraint_3 air row ∧
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        subst imm'
        simp [relevant_constraints, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3]
        simp [Transpiler.imm_to_KB_BV_sgn]
        simp [U32.toBV]
        bv_decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

    lemma equivalence_AUIPC
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 27 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let imm : BitVec 20 := U32.toBV #v[BitVec.ofNat 8 ↑(air.cols.op_c_access.value_0 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_1 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_2 row 0),
                                        BitVec.ofNat 8 ↑(air.cols.op_c_access.value_3 row 0)] >>> 12
      execute_instruction (instruction.UTYPE (imm, reg0, uop.AUIPC)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_auipc_pc := auipc_pc air row h_wf h_constraints
      -- General assumptions
      simp [ bus_row_wf_asm ] at h_wf
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_wf
      -- Recover program bus assumptions
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
      obtain ⟨ imm, rd, h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_imm_mod ⟩ := h_eq_props
      simp [h_selectors] at h_auipc_pc
      -- Process bus hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0 ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
      -- Use equivalence with operation effect specification
      extract_lets reg0 imm'
      rw [
        OpcodeSpec.RV32.execute_AUIPC_equiv
        (pc_val := BitVec.ofNatLT (w := 32) (air.cols.pc row 0).val (by omega))
        (by split_ands <;> aesop)
      ]
      -- Show that the effect is the same
      simp [
        OpcodeSpec.RV32.spec_AUIPC,
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_reg_rd
      ]
      simp [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      -- Prepare the ALU assumptions (AUIPC uses ALU entry index 6)
      replace h_asm_alu := h_asm_alu.2.2.2.2.2.2
      simp [ h_selectors, ALUBus.Spec ] at h_asm_alu
      rw [h_asm_alu.2.2]
      -- Check for differences
      congr 4
      . -- Isolate relevant constraints (0-3 for op_b = instruction.b, 129 for specific = PC)
        have relevant_constraints :
          constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row ∧ constraint_3 air row ∧
          constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row ∧
          constraint_129 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          cpu_auipc_cols_simplification,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        subst imm'
        simp [relevant_constraints, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3, cpu_auipc_cols_simplification]
        simp [Transpiler.imm_to_KB_BV_sgn, h_auipc_pc]
        bv_decide
      . -- Get the upper bound on the pc
        simp [ bus_row_axioms, bus_row, h_is_real ] at h_axioms
        -- Isolate relevant constraints
        have relevant_constraints :
          constraint_229 air row ∧ constraint_231 air row
        := by
          simp [allHold_simplified] at h_constraints
          aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors,
          sub_eq_zero
        ] at relevant_constraints
        clear *- h_axioms relevant_constraints
        simp [← BitVec.toNat_inj]; grind

  end UTYPE

end Equivalence
