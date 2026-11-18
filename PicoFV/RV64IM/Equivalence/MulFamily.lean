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

  section MUL_FAMILY

    -- ========================================================================
    -- MUL_FAMILY — the multiply class, five opcodes:
    --   MUL = 30, MULH = 31, MULHU = 32, MULHSU = 33, MULW = 48.
    -- No immediate form shares any of them, so the decoder gives each
    -- `imm_c = 0` (`imm_c_eq_zero_of_opcode`) and every theorem takes the
    -- opcode alone. `MUL` decodes with any signedness (`ProgramBusEntry.decoded_from`
    -- at 30), since the low 64 bits of the product do not depend on it, so its
    -- theorem holds for every `srs1` and `srs2`. The row reads both operands from
    -- registers and sets no class selector;
    -- `eq_operation_list_effect_state_of_reg_reg` does everything but the
    -- opcode's arm of `ALUBus.Spec`, which states the operands' range and
    -- the product (`MULW` multiplies the low 32 bits of each operand).
    -- ========================================================================

    -- The proof every MUL_FAMILY theorem shares, given the opcode's two Sail lemmas: `imm_c = 0`
    -- from the opcode, then one call to `eq_operation_list_effect_state_of_reg_reg` with the row's
    -- `ALURowFacts`, whose Sail side is the opcode's specification lemma, leaving the opcode's
    -- arm of `ALUBus.Spec`. It names the theorem's own hypotheses, so it is unhygienic.
    set_option hygiene false in
    local macro "mul_close " equiv:ident hyps:ident : tactic => `(tactic| (
      intro rd rs1 rs2
      have h_imm_c := imm_c_eq_zero_of_opcode air row h_is_real (h_all_wf row h_row)
        (by rw [h_opcode]; rfl)
      refine eq_operation_list_effect_state_of_reg_reg
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode, rfl ⟩
        h_imm_c h_bus_hypotheses _
        (fun h_pc h_rs1 h_rs2 => $equiv:ident
          (by rw [$hyps:ident]; exact ⟨ h_pc, h_rs1, h_rs2 ⟩))
        (fun h_spec => ?_)
      simp [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq]))

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
      mul_close OpcodeSpec.RV64.execute_MUL_equiv OpcodeSpec.RV64.spec_MUL_hypotheses

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
      mul_close OpcodeSpec.RV64.execute_MULH_equiv OpcodeSpec.RV64.spec_MULH_hypotheses

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
      mul_close OpcodeSpec.RV64.execute_MULHU_equiv OpcodeSpec.RV64.spec_MULHU_hypotheses

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
      mul_close OpcodeSpec.RV64.execute_MULHSU_equiv OpcodeSpec.RV64.spec_MULHSU_hypotheses

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
      mul_close OpcodeSpec.RV64.execute_MULW_equiv OpcodeSpec.RV64.spec_MULW_hypotheses

  end MUL_FAMILY

end Equivalence
