import PicoFV.Constraints.CPUAir
import PicoFV.RVSail.RV32IM.Opcodes.Opcodes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

namespace Equivalence

  open RV32IM
  open RV32IM_Interactions
  open CpuAir.constraints
  open CPUAir.Buses

  attribute [local simp]
    program_bus_entry

  section RTYPE

    lemma equivalence_ADD
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_ADD,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_ADD, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SUB
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SUB,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_SUB, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_XOR
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_XOR,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_XOR, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_OR
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_OR,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_OR, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_AND
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_AND,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_AND, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SLL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SLL,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_SLL, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SRL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SRL,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_SRL, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SRA
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SRA,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_SRA, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SLT
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SLT,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        . split_ifs <;> simp
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SLT, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SLTU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SLTU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        . split_ifs <;> simp
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SLTU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end RTYPE

  section ITYPE

    lemma equivalence_ADDI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_constraints : CpuAir.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 1)
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_ADDI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h_c0, h_c1, h_c2, h_c3]
          simp [Transpiler.imm_to_KB_BV_sgn]
          bv_decide
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_ADDI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_XORI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_XORI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h_c0, h_c1, h_c2, h_c3]
          simp [Transpiler.imm_to_KB_BV_sgn]
          bv_decide
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_XORI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_ORI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_ORI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h_c0, h_c1, h_c2, h_c3]
          simp [Transpiler.imm_to_KB_BV_sgn]
          bv_decide
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_ORI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_ANDI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_ANDI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h_c0, h_c1, h_c2, h_c3]
          simp [Transpiler.imm_to_KB_BV_sgn]
          bv_decide
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_ANDI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SLTI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SLTI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h_c0, h_c1, h_c2, h_c3]
          simp [Transpiler.imm_to_KB_BV_sgn, Transpiler.imm_to_KB_Int_sgn]
          rw [show BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide]
          split_ifs <;> simp
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SLTI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SLTIU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SLTIU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3, h_c0, h_c1, h_c2, h_c3]
          simp [Transpiler.imm_to_KB_BV_sgn, Transpiler.imm_to_KB_Nat_sgn]
          rw [show BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 32 imm)) = BitVec.signExtend 32 imm by bv_decide]
          split_ifs <;> simp
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SLTIU, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end ITYPE

  section SHIFTIOP

    lemma equivalence_SLLI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SLLI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SLLI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SRLI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SRLI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SRLI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_SRAI
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc, h_eq_c0, h_eq_c1, h_eq_c2, h_eq_c3 ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4 ∧
        air.cols.op_c_access.value_0 row 0 = air.cols.instruction.c_0 row 0 ∧
        air.cols.op_c_access.value_1 row 0 = air.cols.instruction.c_1 row 0 ∧
        air.cols.op_c_access.value_2 row 0 = air.cols.instruction.c_2 row 0 ∧
        air.cols.op_c_access.value_3 row 0 = air.cols.instruction.c_3 row 0
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
      -- Hypotheses
      simp [
        bus_operations,
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg0] at h_bus_hypotheses
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
      extract_lets reg0 reg1 imm'
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_SRAI,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg0]
        rw [h_spec]; congr
        . simp [h_next_pc, ← BitVec.toNat_inj]
          omega
      . simp [OpcodeSpec.RV32.spec_SRAI, *]
        split_ands
        . rw [← h_reg0]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end SHIFTIOP

  section MUL

    lemma equivalence_MUL
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      obtain ⟨ rs2, rs1, rd, sl', sr', h_eq_instr ⟩ := h_opcode_props
      subst instr; simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst data; simp at h_eq_entry
      obtain ⟨ h_opcode',
              h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
              h_a_is_0, h_selectors ⟩ := h_eq_entry; clear h_opcode'
      simp [h_props] at h_eq_props; clear h_props
      simp [← h_a0, ← h_b0, ← h_c0, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_MUL,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_MUL, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_MULH
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_MULH,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_MULH, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_MULHU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_MULHU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_MULHU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_MULHSU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_MULHSU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_MULHSU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end MUL

  section DIV

    lemma equivalence_DIV
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_DIV,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_DIV, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_DIVU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_DIVU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_DIVU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end DIV

  section REM

    lemma equivalence_REM
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_REM,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_REM, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    lemma equivalence_REMU
      [Field ExtF]
      (air : Valid_CpuAir FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_axioms : bus_row_axioms (bus_row air row))
      (h_assumptions : bus_row_assumptions (bus_row air row))
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
      -- Additionals
      obtain ⟨ h_branching, h_next_pc ⟩ :
        air.cols.branching row 0 = 0 ∧
        air.cols.next_pc row 0 = air.cols.pc row 0 + 4
      := by
        simp [
          constraint_and_interaction_simplification,
          h_is_real,
          h_selectors
        ] at h_constraints
        have : air.cols.branching row 0 = 0 := by aesop
        simp [this, sub_eq_zero] at h_constraints ⊢
        aesop
      -- ALU bus assumptions
      simp [
        bus_row,
        h_is_real,
        h_opcode,
        h_selectors,
        h_branching,
        ALUBus.Spec
      ] at h_asm_alu
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, h_spec ⟩ := h_asm_alu
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
      obtain ⟨ h_reg1, h_bus_hypotheses ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_reg1] at h_bus_hypotheses
      obtain ⟨ h_reg0, h_bus_hypotheses ⟩ := h_bus_hypotheses; clear h_bus_hypotheses
      -- Proof
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
      ]
      . simp [
          OpcodeSpec.RV32.spec_REMU,
          bus_operations,
          bus_row,
          h_is_real,
          h_opcode,
          h_selectors,
        ]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [operation_list_effect_state_writeReg_same h_reg2]
        simp [operation_list_effect_state_writeReg_same h_reg1]
        rw [h_spec]; congr
        simp [h_next_pc, ← BitVec.toNat_inj]
        omega
      . simp [OpcodeSpec.RV32.spec_REMU, *]
        split_ands
        . rw [← h_reg1]; rfl
        . rw [← h_reg2]; rfl
        . simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end REM

end Equivalence
