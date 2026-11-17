import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section ITYPE

    -- ========================================================================
    -- ITYPE — the 64-bit register-immediate ALU class, six opcodes:
    --   ADDI = 0, XORI = 2, ORI = 3, ANDI = 4, SLTI = 8, SLTIU = 9.
    -- They share their opcodes with ADD, XOR, OR, AND, SLT and SLTU, which
    -- `imm_c = 0` tells apart (`ProgramBusEntry.decoded_from`), so each
    -- theorem takes `imm_c = 1`. The decoder fixes `imm_b = 0` for opcodes 2,
    -- 3, 4, 8 and 9. Opcode 0 is also `LUI` and `AUIPC` with `imm_b = 1` and
    -- `imm_c = 1`, so ADDI keeps `imm_b = 0` as a hypothesis and closes
    -- through the two lemmas `eq_operation_list_effect_state_of_reg_imm` is
    -- made of, which take `imm_b = 0` directly. The other five close through
    -- `eq_operation_list_effect_state_of_reg_imm`, which leaves the opcode's
    -- arm of `ALUBus.Spec`. `imm` is read back from `op_c`, and
    -- `op_c_value_eq_signExtend_imm12` gives back the 64-bit value Sail adds,
    -- combines or compares.
    -- ========================================================================

    /-- Equivalence for ADDI (opcode 0, `iop.ADDI`). `imm` is read back from the chip's `op_c`
        columns, the low 12 bits of the sign-extended 64-bit form
        (`op_c_value_eq_signExtend_imm12`). Opcode 0 with `imm_c = 1` is also `LUI` or `AUIPC`
        when `imm_b = 1` (`ProgramBusEntry.decoded_from` at 0), so the theorem takes
        `imm_b = 0`.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_ADDI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ADDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real h_wf
        (h_all_constraints row h_row) h_opcode.1 (by simp) h_opcode.2.1 h_opcode.2.2
      intro rd rs1 imm
      obtain ⟨ h_pc, h_rs1 ⟩ := readReg_PC_and_read_xreg_of_reg_imm air row h_is_real h_wf
        h_opcode.1 rfl h_opcode.2.1 h_opcode.2.2 h_bus_hypotheses
      rw [OpcodeSpec.RV64.execute_ADDI_equiv
        (by rw [OpcodeSpec.RV64.spec_ADDI_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩)]
      refine operation_list_effect_state_eq_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl h_opcode.2.1 h_opcode.2.2
        h_bus_hypotheses _ (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- Equivalence for XORI (opcode 2, `iop.XORI`). `imm` is read back from the chip's `op_c`
        columns, the low 12 bits of the sign-extended 64-bit form
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 2 a register `op_b`, so
        the theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`).

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_XORI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 2 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.XORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real h_wf
        (h_all_constraints row h_row) h_opcode.1 (by simp)
        (imm_b_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode.1]; rfl)) h_opcode.2
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_XORI_equiv
          (by rw [OpcodeSpec.RV64.spec_XORI_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- Equivalence for ORI (opcode 3, `iop.ORI`). `imm` is read back from the chip's `op_c`
        columns, the low 12 bits of the sign-extended 64-bit form
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 3 a register `op_b`, so
        the theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`).

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_ORI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 3 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real h_wf
        (h_all_constraints row h_row) h_opcode.1 (by simp)
        (imm_b_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode.1]; rfl)) h_opcode.2
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_ORI_equiv
          (by rw [OpcodeSpec.RV64.spec_ORI_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- Equivalence for ANDI (opcode 4, `iop.ANDI`). `imm` is read back from the chip's `op_c`
        columns, the low 12 bits of the sign-extended 64-bit form
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 4 a register `op_b`, so
        the theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`).

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_ANDI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 4 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ANDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real h_wf
        (h_all_constraints row h_row) h_opcode.1 (by simp)
        (imm_b_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode.1]; rfl)) h_opcode.2
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_ANDI_equiv
          (by rw [OpcodeSpec.RV64.spec_ANDI_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- Equivalence for SLTI (opcode 8, `iop.SLTI`), the signed set-less-than against an
        immediate. `imm` is read back from the chip's `op_c` columns, the low 12 bits of the
        sign-extended 64-bit form (`op_c_value_eq_signExtend_imm12`). The decoder gives
        opcode 8 a register `op_b`, so the theorem does not take `imm_b = 0`
        (`imm_b_eq_zero_of_opcode`). The ALU message at opcode 8 is the CPU's own `SLT`
        request; the branch comparisons use opcodes 264 and 265.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLTI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 8 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real h_wf
        (h_all_constraints row h_row) h_opcode.1 (by simp)
        (imm_b_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode.1]; rfl)) h_opcode.2
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_SLTI_equiv
          (by rw [OpcodeSpec.RV64.spec_SLTI_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- Equivalence for SLTIU (opcode 9, `iop.SLTIU`), the unsigned set-less-than against an
        immediate. `imm` is read back from the chip's `op_c` columns, the low 12 bits of the
        sign-extended 64-bit form (`op_c_value_eq_signExtend_imm12`); the comparison is
        unsigned against that sign-extended value. The decoder gives opcode 9 a register
        `op_b`, so the theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). The ALU
        message at opcode 9 is the CPU's own `SLTU` request; the branch comparisons use
        opcodes 264 and 265.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLTIU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 9 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTIU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real h_wf
        (h_all_constraints row h_row) h_opcode.1 (by simp)
        (imm_b_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode.1]; rfl)) h_opcode.2
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_SLTIU_equiv
          (by rw [OpcodeSpec.RV64.spec_SLTIU_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

  end ITYPE

end Equivalence
