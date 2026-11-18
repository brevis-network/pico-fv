import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section SHIFTIOP

    -- ========================================================================
    -- SHIFTIOP — the 64-bit shift-immediate class, three opcodes:
    --   SLLI = 5, SRLI = 6, SRAI = 7.
    -- They share their opcodes with SLL, SRL and SRA, which `imm_c = 0`
    -- tells apart (`ProgramBusEntry.decoded_from`), so each theorem takes
    -- `imm_c = 1`; the decoder fixes `imm_b = 0` for all three. The row reads
    -- `rs1` and sends the instruction's immediate as `op_c`;
    -- `eq_operation_list_effect_state_of_reg_imm` does everything but the
    -- opcode's arm of `ALUBus.Spec`. That arm shifts by the low 6 bits of the
    -- `op_c` value the row sends. Each theorem reads its 6-bit `imm` from the
    -- instruction's encoded `op_c_0`, as it reads `rd` and `rs1`, and
    -- `op_c_value_setWidth_eq_op_c_0` (constraint 4) shows the two agree.
    -- ========================================================================

    -- The proof every SHIFTIOP theorem shares, given the opcode's two Sail lemmas: one call to
    -- `eq_operation_list_effect_state_of_reg_imm`, leaving the opcode's arm of `ALUBus.Spec`,
    -- where `imm` is rewritten to the low 6 bits of the `op_c` value the row sends. It names
    -- the theorem's own hypotheses, so it is unhygienic.
    set_option hygiene false in
    local macro "shifti_close " equiv:ident hyps:ident : tactic => `(tactic| (
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_reg_imm h_alu (h_alu.imm_b_eq_zero rfl)
        h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => $equiv:ident
          (by rw [$hyps:ident]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      have h_imm := op_c_value_setWidth_eq_op_c_0 air row (n := 6) (by norm_num) h_opcode.2
        (h_all_constraints row h_row)
      simp only [imm, ← h_imm]
      simp [op_a_value, op_b_value, h_spec_eq, execute_RTYPE_pure]
      rfl))

    /-- Equivalence for SLLI (opcode 5, `sop.SLLI`), the 64-bit shift left logical by an immediate.
        `imm` is read from the instruction's encoded `op_c_0`, as `rd` and `rs1` are.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLLI
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
      (h_opcode : air.cols.instruction.opcode row 0 = 5 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SLLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      shifti_close OpcodeSpec.RV64.execute_SLLI_equiv OpcodeSpec.RV64.spec_SLLI_hypotheses

    /-- Equivalence for SRLI (opcode 6, `sop.SRLI`), the 64-bit shift right logical by an immediate.
        `imm` is read from the instruction's encoded `op_c_0`, as `rd` and `rs1` are.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRLI
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
      (h_opcode : air.cols.instruction.opcode row 0 = 6 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      shifti_close OpcodeSpec.RV64.execute_SRLI_equiv OpcodeSpec.RV64.spec_SRLI_hypotheses

    /-- Equivalence for SRAI (opcode 7, `sop.SRAI`), the 64-bit shift right arithmetic by an
        immediate. `imm` is read from the instruction's encoded `op_c_0`, as `rd` and `rs1` are.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRAI
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
      (h_opcode : air.cols.instruction.opcode row 0 = 7 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRAI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      shifti_close OpcodeSpec.RV64.execute_SRAI_equiv OpcodeSpec.RV64.spec_SRAI_hypotheses

  end SHIFTIOP

end Equivalence
