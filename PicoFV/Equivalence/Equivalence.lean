import PicoFV.Constraints.CPUAir

import PicoFV.RVSail.RV32IM.Opcodes.Opcodes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

namespace Equivalence

  open RV32IM
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 0 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.ADD)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 1 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SUB)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 2 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.XOR)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 3 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.OR)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 4 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.AND)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 5 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SLL)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 6 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SRL)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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
      (h_axioms : Interaction.bus_row_axioms (bus_row air row))
      (h_assumptions : Interaction.bus_row_assumptions (bus_row air row))
      (h_constraints : allHold_simplified air row h_row)
      (h_opcode : air.cols.instruction.opcode = 7 ∧ air.cols.opcode_selector.imm_c = 0)
      (h_bus_hypotheses : (operation_list_effect (RV32IM.bus_operations (bus_row air row)) state).hypotheses)
    :
      let reg0 : regidx := .Regidx (air.cols.instruction.a_0 row 0).val
      let reg1 : regidx := .Regidx (air.cols.instruction.b_0 row 0).val
      let reg2 : regidx := .Regidx (air.cols.instruction.c_0 row 0).val
      execute_instruction (instruction.RTYPE (reg2, reg1, reg0, rop.SRA)) state =
      (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Axioms
      simp [ Interaction.bus_row_axioms, bus_row ] at h_axioms
      -- General assumptions
      simp [ Interaction.bus_row_assumptions ] at h_assumptions
      obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_reg ⟩ := h_assumptions
      -- Program bus assumptions
      simp [
        bus_row,
        h_is_real,
        Interaction.ProgramBusEntry.operand_properties,
        -Vector.getElem_mk,
        -Interaction.ProgramBusEntry.mk.injEq
      ] at h_asm_prog
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
      have h_eq_mult : mult = -1 := by aesop
      subst mult
      have h_opcode_props
        := @Interaction.ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ -1, data ⟩
            props
            (Interaction.ProgramBusEntry.deserialise (program_bus_entry air row))
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
          pico_encapsulation,
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
        Interaction.ALUBus.Spec
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

  end RTYPE

end Equivalence
