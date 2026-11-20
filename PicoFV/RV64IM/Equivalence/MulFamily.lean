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

  section MUL_FAMILY

    -- ========================================================================
    -- MUL_FAMILY — the multiply class, five opcodes:
    --   MUL = 30, MULH = 31, MULHU = 32, MULHSU = 33, MULW = 48.
    -- No immediate form shares any of them, so the decoder gives each
    -- `imm_c = 0` (`ALURowFacts.imm_c_eq_zero`) and every theorem takes the
    -- opcode alone. `MUL` decodes with any signedness (`ProgramBusEntry.decoded_from`
    -- at 30), since the low 64 bits of the product do not depend on it, so its
    -- theorem holds for every `srs1` and `srs2`. The row reads both operands from
    -- registers and sets no class selector;
    -- `eq_operation_list_effect_state_of_reg_reg` does everything but the
    -- opcode's arm of `ALUBus.Spec`, which states the operands' range and
    -- the product (`MULW` multiplies the low 32 bits of each operand). Every
    -- theorem closes through `alu_reg_reg_close` (`Common.lean`).
    -- ========================================================================

    /-- Equivalence for MUL (opcode 30, `instruction.MUL` with `result_part := .Low`), the low 64
        bits of the product. The decoder accepts any signedness for opcode 30, and the low half
        does not depend on it, so the theorem holds for every `srs1` and `srs2`.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_MUL
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
      (h_opcode : air.cols.instruction.opcode row 0 = 30)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (srs1 srs2 : Signedness)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.Low,
            signed_rs1   := srs1,
            signed_rs2   := srs2 })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MUL_equiv OpcodeSpec.RV64.spec_MUL_hypotheses []

    /-- Equivalence for MULH (opcode 31, `instruction.MUL` with `result_part := .High`,
        `signed_rs1 := .Signed`, `signed_rs2 := .Signed`), the high 64 bits of the signed
        product.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_MULH
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
      (h_opcode : air.cols.instruction.opcode row 0 = 31)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Signed })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULH_equiv OpcodeSpec.RV64.spec_MULH_hypotheses []

    /-- Equivalence for MULHU (opcode 32, `instruction.MUL` with `result_part := .High`,
        `signed_rs1 := .Unsigned`, `signed_rs2 := .Unsigned`), the high 64 bits of the unsigned
        product.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_MULHU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 32)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Unsigned,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULHU_equiv OpcodeSpec.RV64.spec_MULHU_hypotheses []

    /-- Equivalence for MULHSU (opcode 33, `instruction.MUL` with `result_part := .High`,
        `signed_rs1 := .Signed`, `signed_rs2 := .Unsigned`), the high 64 bits of the
        signed-by-unsigned product.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_MULHSU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 33)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULHSU_equiv OpcodeSpec.RV64.spec_MULHSU_hypotheses []

    /-- Equivalence for MULW (opcode 48, `instruction.MULW`), the 32-bit multiply: the low 32
        bits of the product of the operands' low 32 bits, sign-extended.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_MULW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 48)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MULW (rs2, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULW_equiv OpcodeSpec.RV64.spec_MULW_hypotheses []

  end MUL_FAMILY

end Equivalence
