import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section DIV_FAMILY

    -- ========================================================================
    -- DIV_FAMILY — the divide and remainder class, eight opcodes:
    --   DIV = 34, DIVU = 35, REM = 36, REMU = 37,
    --   DIVW = 49, DIVUW = 50, REMW = 51, REMUW = 52.
    -- No immediate form shares any of them, so the decoder gives each
    -- `imm_c = 0` (`ALURowFacts.imm_c_eq_zero`) and every theorem takes the
    -- opcode alone. Sail's last field is `is_unsigned`: `false` for the signed
    -- opcodes, `true` for the unsigned ones (`ProgramBusEntry.decoded_from`).
    -- The row reads both operands from registers and sets no class selector;
    -- `eq_operation_list_effect_state_of_reg_reg` does everything but the
    -- opcode's arm of `ALUBus.Spec`, which states the quotient or remainder,
    -- division by zero and signed overflow included (the 32-bit opcodes divide
    -- the low 32 bits of each operand). So no theorem assumes anything about
    -- the divisor. Every theorem closes through `alu_reg_reg_close`
    -- (`Common.lean`).
    -- ========================================================================

    /-- Equivalence for DIV (opcode 34, `instruction.DIV` with `is_unsigned := false`),
        the signed 64-bit quotient.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_DIV
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
      (h_opcode : air.cols.instruction.opcode row 0 = 34)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIV_equiv OpcodeSpec.RV64.spec_DIV_hypotheses []

    /-- Equivalence for DIVU (opcode 35, `instruction.DIV` with `is_unsigned := true`),
        the unsigned 64-bit quotient.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_DIVU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 35)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIVU_equiv OpcodeSpec.RV64.spec_DIVU_hypotheses []

    /-- Equivalence for REM (opcode 36, `instruction.REM` with `is_unsigned := false`),
        the signed 64-bit remainder.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_REM
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
      (h_opcode : air.cols.instruction.opcode row 0 = 36)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REM_equiv OpcodeSpec.RV64.spec_REM_hypotheses []

    /-- Equivalence for REMU (opcode 37, `instruction.REM` with `is_unsigned := true`),
        the unsigned 64-bit remainder.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_REMU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 37)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REMU_equiv OpcodeSpec.RV64.spec_REMU_hypotheses []

    /-- Equivalence for DIVW (opcode 49, `instruction.DIVW` with `is_unsigned := false`),
        the signed 32-bit quotient, sign-extended.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_DIVW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 49)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIVW_equiv OpcodeSpec.RV64.spec_DIVW_hypotheses []

    /-- Equivalence for DIVUW (opcode 50, `instruction.DIVW` with `is_unsigned := true`),
        the unsigned 32-bit quotient, sign-extended.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_DIVUW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 50)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIVUW_equiv OpcodeSpec.RV64.spec_DIVUW_hypotheses []

    /-- Equivalence for REMW (opcode 51, `instruction.REMW` with `is_unsigned := false`),
        the signed 32-bit remainder, sign-extended.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_REMW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 51)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REMW_equiv OpcodeSpec.RV64.spec_REMW_hypotheses []

    /-- Equivalence for REMUW (opcode 52, `instruction.REMW` with `is_unsigned := true`),
        the unsigned 32-bit remainder, sign-extended.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_REMUW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 52)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REMUW_equiv OpcodeSpec.RV64.spec_REMUW_hypotheses []

  end DIV_FAMILY

end Equivalence
