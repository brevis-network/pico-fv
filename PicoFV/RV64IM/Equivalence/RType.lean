import PicoFV.RV64IM.Equivalence.Common

-- About 2.4 times the most any proof here uses (about 408 000), so a proof that stops
-- terminating fails at its theorem instead of at the CI job's time-out.
set_option maxHeartbeats 1_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions
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
    -- column forms (`equivalence_<OP>_row`) take `imm_c = 0`. No immediate form
    -- shares 1, so the decoder already gives SUB `imm_c = 0`
    -- (`imm_c_eq_zero_of_opcode`) and its column form takes the opcode alone.
    -- The checked theorems take the decoded instruction instead, whose decoding
    -- fixes the opcode and `imm_c = 0` for all ten (`rtype_decoded`).
    -- The row reads both operands from registers
    -- (`imm_b = 0`, which `imm_c = 0` fixes, and `imm_c = 0`) and sets no class
    -- selector. Every column form closes with `alu_reg_reg_close` (`Common.lean`),
    -- which ends on the opcode's arm of `ALUBus.Spec`, passed to `simp` whole.
    -- The arms of XOR, OR and AND also state the operands' range. The arms of
    -- SLT and SLTU (8 and 9) state the
    -- result with no premise; the "not a branch comparison" condition
    -- (`is_cmp = 0`) sits in the less-than chip's own specification
    -- (`spec_SLT`, `spec_SLTU` in `Spec/LtChip.lean`), not on this side.
    -- ========================================================================

    /-- `equivalence_ADD` in column form: for a row of opcode 0 with `imm_c = 0`, Sail's step on
        the `ADD` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_ADD_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_ADD_equiv OpcodeSpec.RV64.spec_ADD_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_SUB` in column form: for a row of opcode 1, Sail's step on
        the `SUB` whose registers are read off the row's columns equals the row's effect.
        No immediate form shares opcode 1, so the decoder gives `imm_c = 0`
        (`imm_c_eq_zero_of_opcode`) and the theorem takes the opcode alone. -/
    theorem equivalence_SUB_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_SUB_equiv OpcodeSpec.RV64.spec_SUB_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_XOR` in column form: for a row of opcode 2 with `imm_c = 0`, Sail's step on
        the `XOR` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_XOR_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 2 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.XOR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_XOR_equiv OpcodeSpec.RV64.spec_XOR_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_OR` in column form: for a row of opcode 3 with `imm_c = 0`, Sail's step on
        the `OR` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_OR_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 3 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.OR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_OR_equiv OpcodeSpec.RV64.spec_OR_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_AND` in column form: for a row of opcode 4 with `imm_c = 0`, Sail's step on
        the `AND` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_AND_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 4 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.AND)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_AND_equiv OpcodeSpec.RV64.spec_AND_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_SLL` in column form: for a row of opcode 5 with `imm_c = 0`, Sail's step on
        the `SLL` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SLL_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 5 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLL_equiv OpcodeSpec.RV64.spec_SLL_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_SRL` in column form: for a row of opcode 6 with `imm_c = 0`, Sail's step on
        the `SRL` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SRL_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 6 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SRL_equiv OpcodeSpec.RV64.spec_SRL_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_SRA` in column form: for a row of opcode 7 with `imm_c = 0`, Sail's step on
        the `SRA` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SRA_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 7 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRA)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SRA_equiv OpcodeSpec.RV64.spec_SRA_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_SLT` in column form: for a row of opcode 8 with `imm_c = 0`, Sail's step on
        the `SLT` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SLT_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 8 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLT_equiv OpcodeSpec.RV64.spec_SLT_hypotheses
        [execute_RTYPE_pure]

    /-- `equivalence_SLTU` in column form: for a row of opcode 9 with `imm_c = 0`, Sail's step on
        the `SLTU` whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_SLTU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 9 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode.1 h_opcode.2
        OpcodeSpec.RV64.execute_SLTU_equiv OpcodeSpec.RV64.spec_SLTU_hypotheses
        [execute_RTYPE_pure]

    -- ========================================================================
    -- The checked RTYPE theorems, in decoded form: each takes the instruction
    -- and an address whose decoding (`Transpiler.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- Equivalence for ADD (opcode 0, `rop.ADD`), the 64-bit add: for every `ADD` instruction and
        address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding fixes
        `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_ADD
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .ADD)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_ADD_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SUB (opcode 1, `rop.SUB`), the 64-bit subtract: for every `SUB` instruction
        and address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the
        row's Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_SUB
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .SUB)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_SUB_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions @h_opc @h_bus_hypotheses

    /-- Equivalence for XOR (opcode 2, `rop.XOR`), the bitwise exclusive or: for every `XOR`
        instruction and address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity
        1) is the row's Program message, Sail's step on that instruction equals the row's effect.
        The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_XOR
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .XOR)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.XOR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_XOR_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for OR (opcode 3, `rop.OR`), the bitwise or: for every `OR` instruction and
        address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding fixes
        `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_OR
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .OR)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.OR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_OR_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for AND (opcode 4, `rop.AND`), the bitwise and: for every `AND` instruction and
        address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding fixes
        `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_AND
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .AND)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.AND)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_AND_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SLL (opcode 5, `rop.SLL`), the shift left logical by the low 6 bits of
        `rs2`: for every `SLL` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .SLL)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_SLL_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRL (opcode 6, `rop.SRL`), the shift right logical by the low 6 bits of
        `rs2`: for every `SRL` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SRL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .SRL)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_SRL_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRA (opcode 7, `rop.SRA`), the shift right arithmetic by the low 6 bits of
        `rs2`: for every `SRA` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SRA
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .SRA)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRA)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_SRA_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SLT (opcode 8, `rop.SLT`), the signed set-less-than: for every `SLT`
        instruction and address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity
        1) is the row's Program message, Sail's step on that instruction equals the row's effect.
        The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLT
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .SLT)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_SLT_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SLTU (opcode 9, `rop.SLTU`), the unsigned set-less-than: for every `SLTU`
        instruction and address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity
        1) is the row's Program message, Sail's step on that instruction equals the row's effect.
        The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLTU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, .SLTU)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ := reg_reg_decoded air row h_decode rfl
      exact equivalence_SLTU_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- The `RTYPE` theorems' decoding hypothesis holds on every real row of an `RTYPE` opcode
        whose column form's hypotheses hold: the opcode of `op`, and `imm_c = 0` unless `op` is
        `SUB` (an immediate form shares every other opcode). There the Program table's promise
        (in `bus_row_wf_asm`) gives an `RTYPE` instruction of `op` and a 4-aligned address below
        `Transpiler.code_address_bound` whose decoding is the row's Program message. On a row
        of opcode 1 (`SUB`) the promise itself gives `imm_c = 0` (`imm_c_eq_zero_of_opcode`). -/
    theorem rtype_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : rop)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_rop op)
      (h_imm_c : op ≠ .SUB → air.cols.opcode_selector.imm_c row 0 = 0)
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.code_address_bound ∧
        Transpiler.transpile_op (.RTYPE (rs2, rs1, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      have h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0 := by
        by_cases h_sub : op = .SUB
        · subst h_sub
          exact imm_c_eq_zero_of_opcode air row h_is_real h_wf (by rw [h_opcode]; rfl)
        · exact h_imm_c h_sub
      have h_c : (ProgramBusEntry.deserialise (program_bus_entry air row)).imm_c = 0 := by
        rw [deserialise_program_bus_entry]; exact h_imm_c
      have h_op : ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, op) := by
        cases op <;>
        simp only [Transpiler.opcode_of_rop, ProgramBusEntry.decoded_from, h_c, zero_ne_one,
          false_and, and_false, or_false, true_and] at h_from <;>
        first | exact h_from | exact h_from.2
      obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_op
      exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end RTYPE

end Equivalence
