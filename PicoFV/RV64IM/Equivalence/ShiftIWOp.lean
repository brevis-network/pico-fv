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

  section SHIFTIWOP

    -- ========================================================================
    -- SHIFTIWOP — the RV64-only 32-bit shift-immediate class, three opcodes:
    --   SLLIW = 42, SRLIW = 43, SRAIW = 44.
    -- They share their opcodes with SLLW, SRLW and SRAW, which `imm_c = 0`
    -- tells apart (`ProgramBusEntry.decoded_from`), so each theorem takes
    -- `imm_c = 1`; the decoder fixes `imm_b = 0` for all three. The row reads
    -- `rs1` and takes `op_c` from the instruction;
    -- `eq_operation_list_effect_state_of_reg_imm` does everything but the
    -- opcode's arm of `ALUBus.Spec`. That arm shifts by the low 5 bits of `op_c`, and the
    -- theorem's 5-bit `imm` is read from the same columns, so the immediate's
    -- encoding never enters the proof.
    -- ========================================================================

    /-- Equivalence for SLLIW (opcode 42, `sopw.SLLIW`), the 32-bit shift left logical by an immediate.
        `imm` is read back from the chip's `op_c` columns, the low 5 bits of the shift amount.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLLIW
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
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (U64w.toBV (op_c_value air row)).setWidth 5
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SLLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_SLLIW_equiv
          (by rw [OpcodeSpec.RV64.spec_SLLIW_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [imm, op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPEW_pure]
      -- The shift amount mod 32 depends on the low limb of `op_c` only.
      congr 2
      simp only [U64w.toNat, U32w.toNat, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      omega

    /-- Equivalence for SRLIW (opcode 43, `sopw.SRLIW`), the 32-bit shift right logical by an immediate.
        `imm` is read back from the chip's `op_c` columns, the low 5 bits of the shift amount.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRLIW
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
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (U64w.toBV (op_c_value air row)).setWidth 5
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_SRLIW_equiv
          (by rw [OpcodeSpec.RV64.spec_SRLIW_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [imm, op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPEW_pure]
      -- The shift amount mod 32 depends on the low limb of `op_c` only.
      congr 2
      simp only [U64w.toNat, U32w.toNat, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      omega

    /-- Equivalence for SRAIW (opcode 44, `sopw.SRAIW`), the 32-bit shift right arithmetic by an immediate.
        `imm` is read back from the chip's `op_c` columns, the low 5 bits of the shift amount.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRAIW
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
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (U64w.toBV (op_c_value air row)).setWidth 5
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRAIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_opcode.1 rfl rfl h_opcode.2 h_bus_hypotheses _
        (fun h_pc h_rs1 => OpcodeSpec.RV64.execute_SRAIW_equiv
          (by rw [OpcodeSpec.RV64.spec_SRAIW_hypotheses]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [imm, op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPEW_pure]
      -- The shift amount mod 32 depends on the low limb of `op_c` only.
      congr 2
      simp only [U64w.toNat, U32w.toNat, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      omega

  end SHIFTIWOP

end Equivalence
