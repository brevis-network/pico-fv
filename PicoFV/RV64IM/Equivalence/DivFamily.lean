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
    -- `imm_c = 0` (`ALURowFacts.imm_c_eq_zero`) and every column-form theorem
    -- (`equivalence_<OP>_row`) takes the opcode alone; the checked theorems
    -- take the instruction and its decoding instead (end of the section).
    -- Sail's last field is `is_unsigned`: `false` for the signed
    -- opcodes, `true` for the unsigned ones (`ProgramBusEntry.decoded_from`).
    -- The row reads both operands from registers and sets no class selector;
    -- `eq_operation_list_effect_state_of_reg_reg` does everything but the
    -- opcode's arm of `ALUBus.Spec`, which states the quotient or remainder,
    -- division by zero and signed overflow included (the 32-bit opcodes divide
    -- the low 32 bits of each operand). So no theorem assumes anything about
    -- the divisor. Every column-form theorem closes through
    -- `alu_reg_reg_close` (`Common.lean`).
    -- ========================================================================

    /-- `equivalence_DIV` in column form: for a row of opcode 34, Sail's step on the DIV instruction
        whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_DIV_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 34)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIV_equiv OpcodeSpec.RV64.spec_DIV_hypotheses []

    /-- `equivalence_DIVU` in column form: for a row of opcode 35, Sail's step on the DIVU
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_DIVU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 35)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIVU_equiv OpcodeSpec.RV64.spec_DIVU_hypotheses []

    /-- `equivalence_REM` in column form: for a row of opcode 36, Sail's step on the REM instruction
        whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_REM_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 36)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REM_equiv OpcodeSpec.RV64.spec_REM_hypotheses []

    /-- `equivalence_REMU` in column form: for a row of opcode 37, Sail's step on the REMU
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_REMU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 37)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REMU_equiv OpcodeSpec.RV64.spec_REMU_hypotheses []

    /-- `equivalence_DIVW` in column form: for a row of opcode 49, Sail's step on the DIVW
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_DIVW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 49)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIVW_equiv OpcodeSpec.RV64.spec_DIVW_hypotheses []

    /-- `equivalence_DIVUW` in column form: for a row of opcode 50, Sail's step on the DIVUW
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_DIVUW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 50)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_DIVUW_equiv OpcodeSpec.RV64.spec_DIVUW_hypotheses []

    /-- `equivalence_REMW` in column form: for a row of opcode 51, Sail's step on the REMW
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_REMW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 51)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REMW_equiv OpcodeSpec.RV64.spec_REMW_hypotheses []

    /-- `equivalence_REMUW` in column form: for a row of opcode 52, Sail's step on the REMUW
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_REMUW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 52)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_REMUW_equiv OpcodeSpec.RV64.spec_REMUW_hypotheses []

    -- ========================================================================
    -- The checked divide and remainder theorems, in decoded form: each takes the
    -- instruction and an address whose decoding (`Transpiler.V3.transpile_op`,
    -- at multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What a decoding of a divide or remainder says about the row, given the decoder's row for the
        instruction's clause (`h_clause`, which `rfl` proves for each opcode of the class): it is
        real, its opcode is the clause's, and its `op_a`, `op_b` and `op_c` columns name `rd`, `rs1`
        and `rs2`. -/
    private lemma div_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      {instr : instruction} {rs2 rs1 rd : regidx} {opc : FKB} {addr : ℕ} {props props' : Prop}
      (h_decode : Transpiler.V3.transpile_op instr 1 addr = some (program_bus_entry air row, props))
      (h_clause : Transpiler.V3.transpile_op instr 1 addr =
        some ((1, #v[Transpiler.V3.pc_lo addr, Transpiler.V3.pc_hi addr, opc, opc,
          Transpiler.reg_to_KB rd, Transpiler.reg_to_KB rs1, 0, 0, Transpiler.reg_to_KB rs2, 0, 0,
          if rd == regidx.Regidx 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          Transpiler.V3.pc_carry addr]), props'))
    :
      air.cols.is_real row 0 = 1 ∧ air.cols.instruction.opcode row 0 = opc ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      regidx.Regidx (air.cols.instruction.op_b_0 row 0).val = rs1 ∧
      regidx.Regidx (air.cols.instruction.op_c_0 row 0).val = rs2
    := by
      rw [h_clause, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      have h_op_b : air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_op_c : air.cols.instruction.op_c_0 row 0 = Transpiler.reg_to_KB rs2 :=
        decoded_field h_data ProgramBusEntry.c_0
      exact ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode, by rw [h_op_a]; exact regidx_reg_to_KB rd,
        by rw [h_op_b]; exact regidx_reg_to_KB rs1, by rw [h_op_c]; exact regidx_reg_to_KB rs2 ⟩

    /-- Equivalence for DIV (opcode 34, `instruction.DIV` with `is_unsigned := false`), the signed
        64-bit quotient: for every `DIV` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_DIV
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.DIV (rs2, rs1, rd, false)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.DIV (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 34) h_decode rfl
      exact equivalence_DIV_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for DIVU (opcode 35, `instruction.DIV` with `is_unsigned := true`), the unsigned
        64-bit quotient: for every `DIVU` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_DIVU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.DIV (rs2, rs1, rd, true)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.DIV (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 35) h_decode rfl
      exact equivalence_DIVU_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for REM (opcode 36, `instruction.REM` with `is_unsigned := false`), the signed
        64-bit remainder: for every `REM` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_REM
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.REM (rs2, rs1, rd, false)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.REM (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 36) h_decode rfl
      exact equivalence_REM_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for REMU (opcode 37, `instruction.REM` with `is_unsigned := true`), the unsigned
        64-bit remainder: for every `REMU` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_REMU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.REM (rs2, rs1, rd, true)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.REM (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 37) h_decode rfl
      exact equivalence_REMU_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for DIVW (opcode 49, `instruction.DIVW` with `is_unsigned := false`), the signed
        32-bit quotient, sign-extended: for every `DIVW` instruction and address `addr` whose
        decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message,
        Sail's step on that instruction equals the row's effect. The decoding fixes `addr` only
        modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_DIVW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.DIVW (rs2, rs1, rd, false)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.DIVW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 49) h_decode rfl
      exact equivalence_DIVW_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for DIVUW (opcode 50, `instruction.DIVW` with `is_unsigned := true`), the
        unsigned 32-bit quotient, sign-extended: for every `DIVUW` instruction and address `addr`
        whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding fixes `addr`
        only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_DIVUW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.DIVW (rs2, rs1, rd, true)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.DIVW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 50) h_decode rfl
      exact equivalence_DIVUW_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for REMW (opcode 51, `instruction.REMW` with `is_unsigned := false`), the signed
        32-bit remainder, sign-extended: for every `REMW` instruction and address `addr` whose
        decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message,
        Sail's step on that instruction equals the row's effect. The decoding fixes `addr` only
        modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_REMW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.REMW (rs2, rs1, rd, false)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.REMW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 51) h_decode rfl
      exact equivalence_REMW_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for REMUW (opcode 52, `instruction.REMW` with `is_unsigned := true`), the
        unsigned 32-bit remainder, sign-extended: for every `REMUW` instruction and address `addr`
        whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding fixes `addr`
        only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_REMUW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.REMW (rs2, rs1, rd, true)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.REMW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        div_decoded air row (opc := 52) h_decode rfl
      exact equivalence_REMUW_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- The `DIV` and `DIVU` theorems' decoding hypothesis holds on every real row of opcode 34 or
        35: there the Program table's promise (in `bus_row_wf_asm`) gives a `DIV` of the opcode's
        signedness (`is_unsigned`) and a 4-aligned address below `Transpiler.V3.code_address_bound`
        whose decoding is the row's Program message. -/
    theorem div_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {u : Bool} {opc : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = opc)
      (h_u : (u = false ∧ opc = 34) ∨ (u = true ∧ opc = 35))
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.DIV (rs2, rs1, rd, u)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      rcases h_u with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ <;>
      · obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_from
        exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

    /-- The `REM` and `REMU` theorems' decoding hypothesis holds on every real row of opcode 36 or
        37: there the Program table's promise (in `bus_row_wf_asm`) gives a `REM` of the opcode's
        signedness (`is_unsigned`) and a 4-aligned address below `Transpiler.V3.code_address_bound`
        whose decoding is the row's Program message. -/
    theorem rem_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {u : Bool} {opc : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = opc)
      (h_u : (u = false ∧ opc = 36) ∨ (u = true ∧ opc = 37))
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.REM (rs2, rs1, rd, u)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      rcases h_u with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ <;>
      · obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_from
        exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

    /-- The `DIVW` and `DIVUW` theorems' decoding hypothesis holds on every real row of opcode 49 or
        50: there the Program table's promise (in `bus_row_wf_asm`) gives a `DIVW` of the opcode's
        signedness (`is_unsigned`) and a 4-aligned address below `Transpiler.V3.code_address_bound`
        whose decoding is the row's Program message. -/
    theorem divw_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {u : Bool} {opc : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = opc)
      (h_u : (u = false ∧ opc = 49) ∨ (u = true ∧ opc = 50))
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.DIVW (rs2, rs1, rd, u)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      rcases h_u with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ <;>
      · obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_from
        exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

    /-- The `REMW` and `REMUW` theorems' decoding hypothesis holds on every real row of opcode 51 or
        52: there the Program table's promise (in `bus_row_wf_asm`) gives a `REMW` of the opcode's
        signedness (`is_unsigned`) and a 4-aligned address below `Transpiler.V3.code_address_bound`
        whose decoding is the row's Program message. -/
    theorem remw_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {u : Bool} {opc : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = opc)
      (h_u : (u = false ∧ opc = 51) ∨ (u = true ∧ opc = 52))
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.REMW (rs2, rs1, rd, u)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      rcases h_u with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ <;>
      · obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_from
        exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end DIV_FAMILY

end Equivalence
