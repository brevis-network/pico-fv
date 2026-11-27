import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section ADDIW

    -- ========================================================================
    -- ADDIW — the RV64-only sign-extending 32-bit add-immediate, opcode 40 with
    -- `imm_c = 1`. It shares opcode 40 with `RTYPEW.ADDW`, which the immediate
    -- flag tells it from (`ProgramBusEntry.decoded_from` at 40), and the chip-side
    -- shape with every I-type row: one register read, `imm_b = 0`, `imm_c = 1`
    -- and no class selector. The column form, `equivalence_ADDIW_row`, takes
    -- opcode 40 and `imm_c = 1` and reads `rd`, `rs1` and `imm` off the row.
    --
    -- The checked theorem, `equivalence_ADDIW`, takes the instruction instead
    -- and the hypothesis that the decoder turns it into the row's Program
    -- message, which fixes `is_real`, the opcode, `imm_c`, the two register
    -- columns and `op_c_0` (`reg_imm_decoded`).
    -- ========================================================================

    /-- `equivalence_ADDIW` in column form (opcode 40, `instruction.ADDIW`). `imm` is the low 12
        bits of `op_c_0`, read off the row as `rd` and `rs1` are; `op_c_value_setWidth_eq_op_c_0`
        ties it to the `op_c` value the row sends, whose 64-bit form is its sign extension
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 40 a register `op_b`, so the
        theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). The close needs
        `(b + c).setWidth 32 = b.setWidth 32 + c.setWidth 32` between `spec_ADDIW`'s
        `setWidth 32 (r1 + signExtend 64 imm)` and the ALU chip's 32-bit sum. -/
    theorem equivalence_ADDIW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 40 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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

    -- ========================================================================
    -- The checked ADDIW theorem, in decoded form, takes the instruction
    -- and an address whose decoding (`Transpiler.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- Its proof passes hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- Equivalence for ADDIW (opcode 40, `instruction.ADDIW`): for every `ADDIW` instruction and
        address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding fixes
        `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_ADDIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.ADDIW (imm, rs1, rd)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ADDIW (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        reg_imm_decoded air row h_decode rfl (by norm_num)
      exact equivalence_ADDIW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- The `ADDIW` theorem's decoding hypothesis holds on every real row of opcode 40 with
        `imm_c = 1`, which tells `ADDIW` from `ADDW`: there the Program table's promise (in
        `bus_row_wf_asm`) gives an `ADDIW` and a 4-aligned address below
        `Transpiler.code_address_bound` whose decoding is the row's Program message. -/
    theorem addiw_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 40)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 12) (rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.code_address_bound ∧
        Transpiler.transpile_op (.ADDIW (imm, rs1, rd)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode, deserialise_program_bus_entry] at h_from
      simp [ProgramBusEntry.decoded_from, h_imm_c] at h_from
      obtain ⟨ imm, rs1, rd, rfl ⟩ := h_from
      exact ⟨ imm, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end ADDIW

end Equivalence
