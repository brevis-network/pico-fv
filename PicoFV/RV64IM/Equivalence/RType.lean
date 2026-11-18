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

  section RTYPE

    -- ========================================================================
    -- RTYPE — the 64-bit register-register ALU class, ten opcodes:
    --   ADD = 0, SUB = 1, XOR = 2, OR = 3, AND = 4, SLL = 5, SRL = 6,
    --   SRA = 7, SLT = 8, SLTU = 9.
    -- Every opcode but 1 is shared with an immediate form (ADDI, XORI, ORI,
    -- ANDI, SLLI, SRLI, SRAI, SLTI, SLTIU, and LUI and AUIPC at 0), which
    -- `imm_c = 1` tells apart (`ProgramBusEntry.decoded_from`), so those nine
    -- theorems take `imm_c = 0`. No immediate form shares 1, so the decoder
    -- already gives SUB `imm_c = 0` (`imm_c_eq_zero_of_opcode`) and its theorem
    -- takes the opcode alone. The row reads both operands from registers
    -- (`imm_b = 0`, which `imm_c = 0` fixes, and `imm_c = 0`) and sets no class
    -- selector; `eq_operation_list_effect_state_of_reg_reg` does everything but
    -- the opcode's arm of `ALUBus.Spec`. The arms of XOR, OR and AND carry the
    -- operands' range as well as the result, so their pattern drops one more
    -- conjunct. SLT and SLTU read the less-than chip's arm, whose "not a branch
    -- comparison" premise that chip's own contract proof discharges.
    -- ========================================================================

    -- The proof every RTYPE theorem shares, given the opcode `h_op`, `imm_c = 0`, the opcode's
    -- two Sail lemmas and a pattern that takes the opcode's arm of `ALUBus.Spec` apart and
    -- names its result equation `h_spec_eq`: one call to
    -- `eq_operation_list_effect_state_of_reg_reg` with the row's `ALURowFacts`, whose Sail side
    -- is the opcode's specification lemma, leaving the opcode's arm of `ALUBus.Spec`. It names
    -- the theorem's own hypotheses, so it is unhygienic.
    set_option hygiene false in
    local macro "rtype_close " h_op:term:max h_imm_c:term:max equiv:ident hyps:ident
        pat:rcasesPat : tactic => `(tactic| (
      intro rd rs1 rs2
      refine eq_operation_list_effect_state_of_reg_reg
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, $h_op, rfl ⟩
        $h_imm_c h_bus_hypotheses _
        (fun h_pc h_rs1 h_rs2 => $equiv:ident
          (by rw [$hyps:ident]; exact ⟨ h_pc, h_rs1, h_rs2 ⟩))
        (fun h_spec => ?_)
      simp [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain $pat:rcasesPat := h_spec
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]))

    /-- Equivalence for ADD (opcode 0, `rop.ADD`), the 64-bit add.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_ADD
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_ADD_equiv OpcodeSpec.RV64.spec_ADD_hypotheses
        ⟨ -, h_spec_eq ⟩

    /-- Equivalence for SUB (opcode 1, `rop.SUB`), the 64-bit subtract.
        No immediate form shares opcode 1, so the decoder gives `imm_c = 0`
        (`imm_c_eq_zero_of_opcode`) and the theorem takes the opcode alone.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SUB
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
      (h_opcode : air.cols.instruction.opcode row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_imm_c := imm_c_eq_zero_of_opcode air row h_is_real (h_all_wf row h_row)
        (by rw [h_opcode]; rfl)
      rtype_close h_opcode h_imm_c
        OpcodeSpec.RV64.execute_SUB_equiv OpcodeSpec.RV64.spec_SUB_hypotheses
        ⟨ -, h_spec_eq ⟩

    /-- Equivalence for XOR (opcode 2, `rop.XOR`), the bitwise exclusive or.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_XOR
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.XOR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_XOR_equiv OpcodeSpec.RV64.spec_XOR_hypotheses
        ⟨ -, -, h_spec_eq ⟩

    /-- Equivalence for OR (opcode 3, `rop.OR`), the bitwise or.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_OR
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.OR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_OR_equiv OpcodeSpec.RV64.spec_OR_hypotheses
        ⟨ -, -, h_spec_eq ⟩

    /-- Equivalence for AND (opcode 4, `rop.AND`), the bitwise and.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_AND
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.AND)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_AND_equiv OpcodeSpec.RV64.spec_AND_hypotheses
        ⟨ -, -, h_spec_eq ⟩

    /-- Equivalence for SLL (opcode 5, `rop.SLL`), the shift left logical
        by the low 6 bits of `rs2`.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLL
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLL_equiv OpcodeSpec.RV64.spec_SLL_hypotheses
        ⟨ -, h_spec_eq ⟩

    /-- Equivalence for SRL (opcode 6, `rop.SRL`), the shift right logical
        by the low 6 bits of `rs2`.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRL
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SRL_equiv OpcodeSpec.RV64.spec_SRL_hypotheses
        ⟨ -, h_spec_eq ⟩

    /-- Equivalence for SRA (opcode 7, `rop.SRA`), the shift right arithmetic
        by the low 6 bits of `rs2`.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SRA
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRA)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SRA_equiv OpcodeSpec.RV64.spec_SRA_hypotheses
        ⟨ -, h_spec_eq ⟩

    /-- Equivalence for SLT (opcode 8, `rop.SLT`), the signed set-less-than.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLT
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLT_equiv OpcodeSpec.RV64.spec_SLT_hypotheses
        ⟨ -, h_spec_eq ⟩

    /-- Equivalence for SLTU (opcode 9, `rop.SLTU`), the unsigned set-less-than.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_SLTU
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
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rtype_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLTU_equiv OpcodeSpec.RV64.spec_SLTU_hypotheses
        ⟨ -, h_spec_eq ⟩

  end RTYPE

end Equivalence
