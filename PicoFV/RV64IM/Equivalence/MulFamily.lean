import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section MUL_FAMILY

    -- ========================================================================
    -- MUL_FAMILY — the multiply class, five opcodes:
    --   MUL = 30, MULH = 31, MULHU = 32, MULHSU = 33, MULW = 48.
    -- No immediate form shares any of them, so the decoder gives each
    -- `imm_c = 0` (`ALURowFacts.imm_c_eq_zero`) and every column-form theorem
    -- (`equivalence_<OP>_row`) takes the opcode alone; the checked theorems
    -- take the instruction and its decoding instead (end of the section).
    -- `MUL` decodes with any signedness (`ProgramBusEntry.decoded_from` at 30),
    -- since the low 64 bits of the product do not depend on it, so its theorems
    -- hold for every `srs1` and `srs2`. The row reads both operands from
    -- registers and sets no class selector;
    -- `eq_operation_list_effect_state_of_reg_reg` does everything but the
    -- opcode's arm of `ALUBus.Spec`, which states the operands' range and
    -- the product (`MULW` multiplies the low 32 bits of each operand). Every
    -- column-form theorem closes through `alu_reg_reg_close` (`Common.lean`).
    -- ========================================================================

    /-- `equivalence_MUL` in column form: for a row of opcode 30, Sail's step on the MUL instruction
        whose registers are read off the row's columns equals the row's effect, for every `srs1` and
        `srs2`. -/
    theorem equivalence_MUL_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 30)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MUL_equiv OpcodeSpec.RV64.spec_MUL_hypotheses []

    /-- `equivalence_MULH` in column form: for a row of opcode 31, Sail's step on the MULH
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_MULH_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 31)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULH_equiv OpcodeSpec.RV64.spec_MULH_hypotheses []

    /-- `equivalence_MULHU` in column form: for a row of opcode 32, Sail's step on the MULHU
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_MULHU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 32)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULHU_equiv OpcodeSpec.RV64.spec_MULHU_hypotheses []

    /-- `equivalence_MULHSU` in column form: for a row of opcode 33, Sail's step on the MULHSU
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_MULHSU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 33)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
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
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULHSU_equiv OpcodeSpec.RV64.spec_MULHSU_hypotheses []

    /-- `equivalence_MULW` in column form: for a row of opcode 48, Sail's step on the MULW
        instruction whose registers are read off the row's columns equals the row's effect. -/
    theorem equivalence_MULW_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 48)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MULW (rs2, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      alu_reg_reg_close h_opcode (h_alu.imm_c_eq_zero rfl)
        OpcodeSpec.RV64.execute_MULW_equiv OpcodeSpec.RV64.spec_MULW_hypotheses []

    -- ========================================================================
    -- The checked multiply theorems, in decoded form: each takes the
    -- instruction and an address whose decoding (`Transpiler.transpile_op`,
    -- at multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What a decoding of a multiply (`MUL` or `MULW`) says about the row, given the decoder's row
        for the instruction's clause (`h_clause`, which `rfl` proves for each opcode of the class):
        it is real, its opcode is the clause's, and its `op_a`, `op_b` and `op_c` columns name `rd`,
        `rs1` and `rs2`. -/
    private lemma mul_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      {instr : instruction} {rs2 rs1 rd : regidx} {opc : FKB} {addr : ℕ} {props props' : Prop}
      (h_decode : Transpiler.transpile_op instr 1 addr = some (program_bus_entry air row, props))
      (h_clause : Transpiler.transpile_op instr 1 addr =
        some ((1, #v[Transpiler.pc_lo addr, Transpiler.pc_hi addr, opc, opc,
          Transpiler.reg_to_KB rd, Transpiler.reg_to_KB rs1, 0, 0, Transpiler.reg_to_KB rs2, 0, 0,
          if rd == regidx.Regidx 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          Transpiler.pc_carry addr]), props'))
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

    /-- Equivalence for MUL (opcode 30, `instruction.MUL` with `result_part := .Low`), the low 64
        bits of the product: for every `MUL` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoder accepts any signedness for opcode
        30, and the low half does not depend on it, so the theorem holds for every `srs1` and
        `srs2`. The decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc
        pieces. -/
    theorem equivalence_MUL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {srs1 srs2 : Signedness} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.MUL (rs2, rs1, rd,
          { result_part := .Low, signed_rs1 := srs1, signed_rs2 := srs2 })) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.Low,
            signed_rs1   := srs1,
            signed_rs2   := srs2 })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        mul_decoded air row (opc := 30) h_decode rfl
      exact equivalence_MUL_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses srs1 srs2

    /-- Equivalence for MULH (opcode 31, `instruction.MUL` with `result_part := .High`,
        `signed_rs1 := .Signed`, `signed_rs2 := .Signed`), the high 64 bits of the signed product:
        for every `MULH` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_MULH
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed })) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Signed })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        mul_decoded air row (opc := 31) h_decode rfl
      exact equivalence_MULH_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for MULHU (opcode 32, `instruction.MUL` with `result_part := .High`,
        `signed_rs1 := .Unsigned`, `signed_rs2 := .Unsigned`), the high 64 bits of the unsigned
        product: for every `MULHU` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_MULHU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Unsigned,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        mul_decoded air row (opc := 32) h_decode rfl
      exact equivalence_MULHU_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for MULHSU (opcode 33, `instruction.MUL` with `result_part := .High`,
        `signed_rs1 := .Signed`, `signed_rs2 := .Unsigned`), the high 64 bits of the
        signed-by-unsigned product: for every `MULHSU` instruction and address `addr` whose decoding
        (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_MULHSU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        mul_decoded air row (opc := 33) h_decode rfl
      exact equivalence_MULHSU_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- Equivalence for MULW (opcode 48, `instruction.MULW`), the 32-bit multiply (the low 32 bits
        of the product of the operands' low 32 bits, sign-extended): for every `MULW` instruction and
        address `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding fixes
        `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_MULW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {rs2 rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.MULW (rs2, rs1, rd)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.MULW (rs2, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        mul_decoded air row (opc := 48) h_decode rfl
      exact equivalence_MULW_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses

    /-- The `MUL`, `MULH`, `MULHU` and `MULHSU` theorems' decoding hypothesis holds on every real
        row of opcode 30 to 33: there the Program table's promise (in `bus_row_wf_asm`) gives a
        `MUL` of the opcode's `mul_op` and a 4-aligned address below
        `Transpiler.code_address_bound` whose decoding is the row's Program message. For opcode
        30 that holds for every `mul_op` with `result_part := .Low`, whatever its signedness. -/
    theorem mul_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : mul_op) {opc : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = opc)
      (h_op : (op.result_part = .Low ∧ opc = 30) ∨
              (op = { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } ∧
                opc = 31) ∨
              (op = { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } ∧
                opc = 32) ∨
              (op = { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } ∧
                opc = 33))
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.code_address_bound ∧
        Transpiler.transpile_op (.MUL (rs2, rs1, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      rcases h_op with ⟨ h_low, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩
      · -- The decoding of a low-half `MUL` does not read its signedness, so `h_dec`, at the
        -- signedness the promise gives, is the decoding at `op`'s by unfolding.
        obtain ⟨ rp, sl, sr ⟩ := op
        obtain rfl : rp = .Low := h_low
        obtain ⟨ rs2, rs1, rd, _, _, rfl ⟩ := h_from
        exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩
      all_goals
        obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_from
        exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

    /-- The `MULW` theorem's decoding hypothesis holds on every real row of opcode 48: there the
        Program table's promise (in `bus_row_wf_asm`) gives a `MULW` and a 4-aligned address below
        `Transpiler.code_address_bound` whose decoding is the row's Program message. -/
    theorem mulw_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 48)
    :
      ∃ (rs2 rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.code_address_bound ∧
        Transpiler.transpile_op (.MULW (rs2, rs1, rd)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      obtain ⟨ rs2, rs1, rd, rfl ⟩ := h_from
      exact ⟨ rs2, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end MUL_FAMILY

end Equivalence
