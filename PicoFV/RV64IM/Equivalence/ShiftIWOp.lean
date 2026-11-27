import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section SHIFTIWOP

    -- ========================================================================
    -- SHIFTIWOP — the RV64-only 32-bit shift-immediate class, three opcodes:
    --   SLLIW = 42, SRLIW = 43, SRAIW = 44.
    -- They share their opcodes with SLLW, SRLW and SRAW, which `imm_c = 0`
    -- tells apart (`ProgramBusEntry.decoded_from`), so each column-form
    -- theorem (`equivalence_<OP>_row`) takes `imm_c = 1`; the decoder fixes
    -- `imm_b = 0` for all three. The row reads `rs1` and sends the
    -- instruction's immediate as `op_c`. Each column form reads its 5-bit
    -- `imm` from the row's `op_c_0`, as it reads `rd` and `rs1`; the ALU chip
    -- shifts by the low 5 bits of the `op_c` value the row sends.
    -- `eq_operation_list_effect_state_of_shift_imm` links the two and does
    -- everything but the opcode's arm of `ALUBus.Spec`, which each proof gives
    -- last.
    --
    -- The checked theorems, `equivalence_<OP>`, take the instruction instead
    -- and the hypothesis that the decoder turns it into the row's Program
    -- message, which fixes `is_real`, the opcode, `imm_c`, the two register
    -- columns and `op_c_0` (`reg_imm_decoded`).
    -- ========================================================================

    /-- The shift amount of a 32-bit shift, `toNat % 32`, depends on a word's low limb only. -/
    private lemma toNat_mod_32_eq_low_U32w (w : U64w) :
      w.toNat % 32 = U32w.toNat #v[w[0], w[1]] % 32
    := by
      simp only [U64w.toNat, U32w.toNat, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      omega

    /-- `equivalence_SLLIW` in column form (opcode 42, `sopw.SLLIW`), the 32-bit shift left logical
        by an immediate. `imm` is the low 5 bits of `op_c_0`, read off the row as `rd` and `rs1`
        are. -/
    theorem equivalence_SLLIW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 42 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SLLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_shift_imm (n := 5) (by norm_num) h_alu
        (h_alu.imm_b_eq_zero rfl) h_opcode.2 h_bus_hypotheses
        (fun v amount => BitVec.signExtend 64 (v.setWidth 32 <<< amount.toNat))
        (fun _ _ h_reads => OpcodeSpec.RV64.execute_SLLIW_equiv
          (by rw [OpcodeSpec.RV64.spec_SLLIW_hypotheses]; exact h_reads))
        (fun h_spec => ?_)
      -- The ALU chip's arm for opcode 42.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, h_spec_eq, execute_RTYPEW_pure]
      rw [toNat_mod_32_eq_low_U32w]
      simp [op_c_value]

    /-- `equivalence_SRLIW` in column form (opcode 43, `sopw.SRLIW`), the 32-bit shift right logical
        by an immediate. `imm` is the low 5 bits of `op_c_0`, read off the row as `rd` and `rs1`
        are. -/
    theorem equivalence_SRLIW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 43 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_shift_imm (n := 5) (by norm_num) h_alu
        (h_alu.imm_b_eq_zero rfl) h_opcode.2 h_bus_hypotheses
        (fun v amount => BitVec.signExtend 64 (v.setWidth 32 >>> amount.toNat))
        (fun _ _ h_reads => OpcodeSpec.RV64.execute_SRLIW_equiv
          (by rw [OpcodeSpec.RV64.spec_SRLIW_hypotheses]; exact h_reads))
        (fun h_spec => ?_)
      -- The ALU chip's arm for opcode 43.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, h_spec_eq, execute_RTYPEW_pure]
      rw [toNat_mod_32_eq_low_U32w]
      simp [op_c_value]

    /-- `equivalence_SRAIW` in column form (opcode 44, `sopw.SRAIW`), the 32-bit shift right
        arithmetic by an immediate. `imm` is the low 5 bits of `op_c_0`, read off the row as `rd`
        and `rs1` are. -/
    theorem equivalence_SRAIW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 44 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRAIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_shift_imm (n := 5) (by norm_num) h_alu
        (h_alu.imm_b_eq_zero rfl) h_opcode.2 h_bus_hypotheses
        (fun v amount => BitVec.signExtend 64 ((v.setWidth 32).sshiftRight amount.toNat))
        (fun _ _ h_reads => OpcodeSpec.RV64.execute_SRAIW_equiv
          (by rw [OpcodeSpec.RV64.spec_SRAIW_hypotheses]; exact h_reads))
        (fun h_spec => ?_)
      -- The ALU chip's arm for opcode 44.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, h_spec_eq, execute_RTYPEW_pure]
      rw [toNat_mod_32_eq_low_U32w]
      simp [op_c_value]

    -- ========================================================================
    -- The checked SHIFTIWOP theorems, in decoded form: each takes the instruction
    -- and an address whose decoding (`Transpiler.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- Equivalence for SLLIW (opcode 42, `sopw.SLLIW`), the 32-bit shift left logical by an
        immediate: for every `SLLIW` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLLIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 5} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.SHIFTIWOP (imm, rs1, rd, sopw.SLLIW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SLLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        reg_imm_decoded air row h_decode rfl (by norm_num)
      exact equivalence_SLLIW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRLIW (opcode 43, `sopw.SRLIW`), the 32-bit shift right logical by an
        immediate: for every `SRLIW` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SRLIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 5} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.SHIFTIWOP (imm, rs1, rd, sopw.SRLIW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        reg_imm_decoded air row h_decode rfl (by norm_num)
      exact equivalence_SRLIW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRAIW (opcode 44, `sopw.SRAIW`), the 32-bit shift right arithmetic by an
        immediate: for every `SRAIW` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SRAIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 5} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.SHIFTIWOP (imm, rs1, rd, sopw.SRAIW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRAIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        reg_imm_decoded air row h_decode rfl (by norm_num)
      exact equivalence_SRAIW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- The `SHIFTIWOP` theorems' decoding hypothesis holds on every real row of a `SHIFTIWOP`
        opcode with `imm_c = 1`, which tells the shift from `SLLW`, `SRLW` and `SRAW`: there the
        Program table's promise (in `bus_row_wf_asm`) gives a 32-bit shift by an immediate of the
        operation and a 4-aligned address below `Transpiler.code_address_bound` whose decoding is
        the row's Program message. -/
    theorem shiftiwop_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : sopw)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_sopw op)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 5) (rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.code_address_bound ∧
        Transpiler.transpile_op (.SHIFTIWOP (imm, rs1, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode, deserialise_program_bus_entry] at h_from
      cases op <;>
      simp [ProgramBusEntry.decoded_from, Transpiler.opcode_of_sopw, h_imm_c] at h_from <;>
      · obtain ⟨ imm, rs1, rd, rfl ⟩ := h_from
        exact ⟨ imm, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end SHIFTIWOP

end Equivalence
