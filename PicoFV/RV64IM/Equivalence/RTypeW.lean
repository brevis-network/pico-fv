import PicoFV.RV64IM.Equivalence.Common

-- About 2.3 times the most any proof here uses (about 436 000), so a proof that stops
-- terminating fails at its theorem instead of at the CI job's time-out.
set_option maxHeartbeats 1_000_000
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
    -- column forms (`equivalence_<OP>_row`) of ADDW, SLLW, SRLW and SRAW take
    -- `imm_c = 0`. No immediate form shares 41, so the decoder already gives
    -- SUBW `imm_c = 0` (`ALURowFacts.imm_c_eq_zero`) and its column form takes
    -- the opcode alone. The checked theorems take the decoded instruction
    -- instead, whose decoding fixes the opcode and `imm_c = 0` for all five
    -- (`rtypew_decoded`). The row reads both operands from registers
    -- (`imm_b = 0`, `imm_c = 0`) and sets no class selector;
    -- `eq_operation_list_effect_state_of_reg_reg` does everything but the
    -- opcode's arm of `ALUBus.Spec`, which applies `setWidth 32` to both
    -- operands and sign-extends the 32-bit result. Every column form closes
    -- through `alu_reg_reg_close` (`Common.lean`).
    -- ========================================================================

    /-- `equivalence_ADDW` in column form: for a row of opcode 40 with `imm_c = 0`, Sail's step on
        the `ADDW` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_ADDW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 40 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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

    /-- `equivalence_SUBW` in column form: for a row of opcode 41, Sail's step on
        the `SUBW` whose registers are read off the row's columns equals the row's effect.
        No immediate form shares opcode 41, so the decoder gives `imm_c = 0`
        (`imm_c_eq_zero_of_opcode`) and the theorem takes the opcode alone. -/
    theorem equivalence_SUBW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 41)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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

    /-- `equivalence_SLLW` in column form: for a row of opcode 42 with `imm_c = 0`, Sail's step on
        the `SLLW` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SLLW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 42 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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

    /-- `equivalence_SRLW` in column form: for a row of opcode 43 with `imm_c = 0`, Sail's step on
        the `SRLW` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SRLW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 43 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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

    /-- `equivalence_SRAW` in column form: for a row of opcode 44 with `imm_c = 0`, Sail's step on
        the `SRAW` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SRAW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 44 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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

    -- ========================================================================
    -- The checked RTYPEW theorems, in decoded form: each takes the instruction
    -- and an address whose decoding (`Transpiler.V3.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What an `RTYPEW` instruction's decoding says about the row: it is real, its opcode is
        the operation's (`Transpiler.opcode_of_ropw`), its third operand is a register
        (`imm_c = 0`), and its `op_a`, `op_b` and `op_c` columns name `rd`, `rs1` and `rs2`. -/
    private lemma rtypew_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      {rs2 rs1 rd : regidx} {op : ropw} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, op)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      air.cols.instruction.opcode row 0 = Transpiler.opcode_of_ropw op ∧
      air.cols.opcode_selector.imm_c row 0 = 0 ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      regidx.Regidx (air.cols.instruction.op_b_0 row 0).val = rs1 ∧
      regidx.Regidx (air.cols.instruction.op_c_0 row 0).val = rs2
    := by
      simp only [Transpiler.V3.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      have h_op_b : air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_op_c : air.cols.instruction.op_c_0 row 0 = Transpiler.reg_to_KB rs2 :=
        decoded_field h_data ProgramBusEntry.c_0
      exact ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode, decoded_field h_data ProgramBusEntry.imm_c,
        by rw [h_op_a]; exact regidx_reg_to_KB rd, by rw [h_op_b]; exact regidx_reg_to_KB rs1,
        by rw [h_op_c]; exact regidx_reg_to_KB rs2 ⟩

    /-- Equivalence for ADDW (opcode 40, `ropw.ADDW`), the 32-bit add: for every `ADDW` instruction
        and address `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the
        row's Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_ADDW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, .ADDW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.ADDW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := rtypew_decoded air row h_decode
      exact equivalence_ADDW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SUBW (opcode 41, `ropw.SUBW`), the 32-bit subtract: for every `SUBW`
        instruction and address `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity
        1) is the row's Program message, Sail's step on that instruction equals the row's effect.
        The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_SUBW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, .SUBW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SUBW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, rfl, rfl, rfl ⟩ := rtypew_decoded air row h_decode
      exact equivalence_SUBW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions @h_opc @h_bus_hypotheses

    /-- Equivalence for SLLW (opcode 42, `ropw.SLLW`), the 32-bit shift left logical: for every
        `SLLW` instruction and address `addr` whose decoding (`Transpiler.V3.transpile_op`, at
        multiplicity 1) is the row's Program message, Sail's step on that instruction equals the
        row's effect. The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit
        pc pieces. -/
    theorem equivalence_SLLW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, .SLLW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := rtypew_decoded air row h_decode
      exact equivalence_SLLW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRLW (opcode 43, `ropw.SRLW`), the 32-bit shift right logical: for every
        `SRLW` instruction and address `addr` whose decoding (`Transpiler.V3.transpile_op`, at
        multiplicity 1) is the row's Program message, Sail's step on that instruction equals the
        row's effect. The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit
        pc pieces. -/
    theorem equivalence_SRLW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, .SRLW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SRLW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := rtypew_decoded air row h_decode
      exact equivalence_SRLW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRAW (opcode 44, `ropw.SRAW`), the 32-bit shift right arithmetic: for every
        `SRAW` instruction and address `addr` whose decoding (`Transpiler.V3.transpile_op`, at
        multiplicity 1) is the row's Program message, Sail's step on that instruction equals the
        row's effect. The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit
        pc pieces. -/
    theorem equivalence_SRAW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, .SRAW)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SRAW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := rtypew_decoded air row h_decode
      exact equivalence_SRAW_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- The `RTYPEW` theorems' decoding hypothesis holds on every real row of an `RTYPEW` opcode
        whose column form's hypotheses hold: the opcode of `op`, and `imm_c = 0` unless `op` is
        `SUBW` (an immediate form shares every other opcode). There the Program table's promise
        (in `bus_row_wf_asm`) gives an `RTYPEW` instruction of `op` and a 4-aligned address below
        `Transpiler.V3.code_address_bound` whose decoding is the row's Program message. On a row
        of opcode 41 (`SUBW`) the promise itself gives `imm_c = 0` (`imm_c_eq_zero_of_opcode`). -/
    theorem rtypew_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : ropw)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_ropw op)
      (h_imm_c : op ≠ .SUBW → air.cols.opcode_selector.imm_c row 0 = 0)
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.RTYPEW (rs2, rs1, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      have h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0 := by
        by_cases h_sub : op = .SUBW
        · subst h_sub
          exact imm_c_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode]; rfl)
        · exact h_imm_c h_sub
      have h_c : (ProgramBusEntry.deserialise (program_bus_entry air row)).imm_c = 0 := by
        rw [deserialise_program_bus_entry]; exact h_imm_c
      have h_op : ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, op) := by
        cases op <;>
        simp only [Transpiler.opcode_of_ropw, ProgramBusEntry.decoded_from, h_c, zero_ne_one,
          false_and, or_false, true_and] at h_from <;>
        exact h_from
      obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_op
      exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end RTYPEW

end Equivalence
