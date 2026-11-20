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

  section ADDIW

    -- ========================================================================
    -- ADDIW — the RV64-only sign-extending 32-bit add-immediate, opcode 40 with
    -- `imm_c = 1`. It shares opcode 40 with `RTYPEW.ADDW`, which the immediate
    -- flag tells it from (`ProgramBusEntry.decoded_from` at 40), and the chip-side
    -- shape with every I-type row: one register read, `imm_b = 0`, `imm_c = 1`
    -- and no class selector.
    -- ========================================================================

    /-- Equivalence for ADDIW (opcode 40, `instruction.ADDIW`). `imm` is the low 12 bits of
        `op_c_0`, read from the instruction as `rd` and `rs1` are; `op_c_value_setWidth_eq_op_c_0`
        ties it to the `op_c` value the row sends, whose 64-bit form is its sign extension
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 40 a register `op_b`, so the
        theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). The close needs
        `(b + c).setWidth 32 = b.setWidth 32 + c.setWidth 32` between `spec_ADDIW`'s
        `setWidth 32 (r1 + signExtend 64 imm)` and the ALU chip's 32-bit sum.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_ADDIW
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
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ADDIW (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_alu : ALURowFacts air row 40 :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      have h_imm_b := h_alu.imm_b_eq_zero rfl
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real (h_all_wf row h_row)
        (h_all_constraints row h_row) h_opcode.1 (by simp) h_imm_b h_opcode.2
      rw [op_c_value_setWidth_eq_op_c_0 air row (n := 12) (by norm_num) h_opcode.2
        (h_all_constraints row h_row)] at h_imm
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm h_alu h_imm_b h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_ADDIW_equiv
          (by rw [OpcodeSpec.RV64.spec_ADDIW_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPEW_pure,
            BitVec.setWidth_add]

  end ADDIW

end Equivalence
