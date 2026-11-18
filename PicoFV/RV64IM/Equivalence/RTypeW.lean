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

  section RTYPEW

    -- ========================================================================
    -- RTYPEW — the RV64-only 32-bit register-register class, five opcodes:
    --   ADDW = 40, SUBW = 41, SLLW = 42, SRLW = 43, SRAW = 44.
    -- Opcodes 40, 42, 43 and 44 are shared with ADDIW and the SHIFTIWOP class,
    -- which `imm_c = 1` tells apart (`ProgramBusEntry.decoded_from`), so the
    -- ADDW, SLLW, SRLW and SRAW theorems take `imm_c = 0`. No immediate form
    -- shares 41, so the decoder already gives SUBW `imm_c = 0`
    -- (`ALURowFacts.imm_c_eq_zero`) and its theorem takes the opcode alone. The
    -- row reads both operands from registers (`imm_b = 0`, `imm_c = 0`) and sets
    -- no class selector; `eq_operation_list_effect_state_of_reg_reg` does
    -- everything but the opcode's arm of `ALUBus.Spec`, which applies
    -- `setWidth 32` to both operands and sign-extends the 32-bit result. Every
    -- theorem closes through `alu_reg_reg_close` (`Common.lean`).
    -- ========================================================================

    /-- Equivalence for ADDW (opcode 40, `ropw.ADDW`), the 32-bit add.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_ADDW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 40 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.ADDW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_ADDW_equiv OpcodeSpec.RV64.spec_ADDW_hypotheses
        [execute_RTYPEW_pure]

    /-- Equivalence for SUBW (opcode 41, `ropw.SUBW`), the 32-bit subtract.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SUBW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 41)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SUBW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_SUBW_equiv OpcodeSpec.RV64.spec_SUBW_hypotheses
        [execute_RTYPEW_pure]

    /-- Equivalence for SLLW (opcode 42, `ropw.SLLW`), the 32-bit shift left logical.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLLW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 42 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLLW_equiv OpcodeSpec.RV64.spec_SLLW_hypotheses
        [execute_RTYPEW_pure]

    /-- Equivalence for SRLW (opcode 43, `ropw.SRLW`), the 32-bit shift right logical.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRLW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 43 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SRLW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SRLW_equiv OpcodeSpec.RV64.spec_SRLW_hypotheses
        [execute_RTYPEW_pure]

    /-- Equivalence for SRAW (opcode 44, `ropw.SRAW`), the 32-bit shift right arithmetic.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRAW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 44 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SRAW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SRAW_equiv OpcodeSpec.RV64.spec_SRAW_hypotheses
        [execute_RTYPEW_pure]

  end RTYPEW

end Equivalence
