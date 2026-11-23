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

  section ITYPE

    -- ========================================================================
    -- ITYPE — the 64-bit register-immediate ALU class, six opcodes:
    --   ADDI = 0, XORI = 2, ORI = 3, ANDI = 4, SLTI = 8, SLTIU = 9.
    -- They share their opcodes with ADD, XOR, OR, AND, SLT and SLTU, which
    -- `imm_c = 0` tells apart (`ProgramBusEntry.decoded_from`), so each
    -- column-form theorem (`equivalence_<OP>_row`) takes `imm_c = 1`. The
    -- decoder fixes `imm_b = 0` for opcodes 2, 3, 4, 8 and 9
    -- (`ALURowFacts.imm_b_eq_zero`). Opcode 0 is also `LUI` and `AUIPC` with
    -- `imm_b = 1` and `imm_c = 1`, so ADDI's column form keeps `imm_b = 0` as
    -- a hypothesis. Each column form reads its 12-bit `imm` from the row's
    -- `op_c_0`, as it reads `rd` and `rs1`; the ALU chip works on the `op_c`
    -- value the row sends, whose low 12 bits are those of `op_c_0`
    -- (`op_c_value_setWidth_eq_op_c_0`) and whose 64-bit form is their sign
    -- extension (`op_c_value_eq_signExtend_imm12`). All six close through
    -- `itype_by_alu_spec` below, which takes the `imm_b = 0` proof as an
    -- argument.
    --
    -- The checked theorems, `equivalence_<OP>`, take the instruction instead
    -- and the hypothesis that the decoder turns it into the row's Program
    -- message, which fixes `is_real`, the opcode, both immediate flags, the
    -- two register columns and `op_c_0` (`itype_decoded`).
    -- ========================================================================

    set_option hygiene false in
    /-- The proof of every column-form theorem in this section. `imm_b` and `imm_c` prove the row's
        `imm_b = 0` and `imm_c = 1`; `imm_b` may use the row's `ALURowFacts`, which the tactic
        builds first as `h_alu`. `exec_equiv` and `spec_hyps` are the opcode's Sail lemmas
        `execute_<OP>_equiv` and `spec_<OP>_hypotheses`; `pat` takes the opcode's arm of
        `ALUBus.Spec` apart and names its result equation `h_spec_eq`.

        `eq_operation_list_effect_state_of_reg_imm` reads the pc and `rs1`, and leaves
        the opcode's arm of `ALUBus.Spec`. `imm` is the low 12 bits of the instruction's
        `op_c_0`. `op_c_value_eq_signExtend_imm12` gives the 64-bit value Sail adds, combines or
        compares as the sign extension of the low 12 bits of the `op_c` value the row sends;
        `op_c_value_setWidth_eq_op_c_0` rewrites those bits in it (`h_imm`) into `imm`'s.
        Hygiene is off so the tactic
        can name the theorem's hypotheses (`h_opcode`, `h_all_wf`, ...), which every column form
        here declares under the same names. -/
    local macro "itype_by_alu_spec " imm_b:term ", " imm_c:term ", " exec_equiv:ident ", "
        spec_hyps:ident ", " pat:rcasesPat : tactic => `(tactic| (
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      have h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0 := $imm_b
      have h_imm := op_c_value_eq_signExtend_imm12 air row h_is_real (h_all_wf row h_row)
        (h_all_constraints row h_row) h_opcode.1 (by simp) h_imm_b $imm_c
      rw [op_c_value_setWidth_eq_op_c_0 air row (n := 12) (by norm_num) $imm_c
        (h_all_constraints row h_row)] at h_imm
      intro rd rs1 imm
      refine eq_operation_list_effect_state_of_reg_imm h_alu h_imm_b $imm_c h_bus_hypotheses _
        (fun h_pc h_rs1 => $exec_equiv (by rw [$spec_hyps:ident]; exact ⟨ h_pc, h_rs1 ⟩))
        (fun h_spec => ?_)
      simp [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain $pat:rcasesPat := h_spec
      rw [show BitVec.signExtend 64 imm = U64w.toBV (op_c_value air row) from h_imm.symm]
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]))

    /-- `equivalence_ADDI` in column form (opcode 0, `iop.ADDI`). `imm` is the low 12 bits of
        `op_c_0`, read off the row as `rd` and `rs1` are; `op_c_value_setWidth_eq_op_c_0` ties it to
        the `op_c` value the row sends, whose 64-bit form is its sign extension
        (`op_c_value_eq_signExtend_imm12`). Opcode 0 with `imm_c = 1` is also `LUI` or `AUIPC` when
        `imm_b = 1` (`ProgramBusEntry.decoded_from` at 0), so the theorem takes `imm_b = 0`. -/
    theorem equivalence_ADDI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ADDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      itype_by_alu_spec h_opcode.2.1, h_opcode.2.2,
        OpcodeSpec.RV64.execute_ADDI_equiv, OpcodeSpec.RV64.spec_ADDI_hypotheses,
        ⟨ -, h_spec_eq ⟩

    /-- `equivalence_XORI` in column form (opcode 2, `iop.XORI`). `imm` is the low 12 bits of
        `op_c_0`, read off the row as `rd` and `rs1` are; `op_c_value_setWidth_eq_op_c_0` ties it to
        the `op_c` value the row sends, whose 64-bit form is its sign extension
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 2 a register `op_b`, so the
        theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). -/
    theorem equivalence_XORI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 2 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.XORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      itype_by_alu_spec (h_alu.imm_b_eq_zero rfl), h_opcode.2,
        OpcodeSpec.RV64.execute_XORI_equiv, OpcodeSpec.RV64.spec_XORI_hypotheses,
        ⟨ -, -, h_spec_eq ⟩

    /-- `equivalence_ORI` in column form (opcode 3, `iop.ORI`). `imm` is the low 12 bits of
        `op_c_0`, read off the row as `rd` and `rs1` are; `op_c_value_setWidth_eq_op_c_0` ties it to
        the `op_c` value the row sends, whose 64-bit form is its sign extension
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 3 a register `op_b`, so the
        theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). -/
    theorem equivalence_ORI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 3 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      itype_by_alu_spec (h_alu.imm_b_eq_zero rfl), h_opcode.2,
        OpcodeSpec.RV64.execute_ORI_equiv, OpcodeSpec.RV64.spec_ORI_hypotheses,
        ⟨ -, -, h_spec_eq ⟩

    /-- `equivalence_ANDI` in column form (opcode 4, `iop.ANDI`). `imm` is the low 12 bits of
        `op_c_0`, read off the row as `rd` and `rs1` are; `op_c_value_setWidth_eq_op_c_0` ties it to
        the `op_c` value the row sends, whose 64-bit form is its sign extension
        (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 4 a register `op_b`, so the
        theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). -/
    theorem equivalence_ANDI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 4 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ANDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      itype_by_alu_spec (h_alu.imm_b_eq_zero rfl), h_opcode.2,
        OpcodeSpec.RV64.execute_ANDI_equiv, OpcodeSpec.RV64.spec_ANDI_hypotheses,
        ⟨ -, -, h_spec_eq ⟩

    /-- `equivalence_SLTI` in column form (opcode 8, `iop.SLTI`), the signed set-less-than against
        an immediate. `imm` is the low 12 bits of `op_c_0`, read off the row as `rd` and `rs1` are;
        `op_c_value_setWidth_eq_op_c_0` ties it to the `op_c` value the row sends, whose 64-bit form
        is its sign extension (`op_c_value_eq_signExtend_imm12`). The decoder gives opcode 8 a
        register `op_b`, so the theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). The
        ALU message at opcode 8 is the CPU's own `SLT` request; the branch comparisons use opcodes
        264 and 265. -/
    theorem equivalence_SLTI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 8 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      itype_by_alu_spec (h_alu.imm_b_eq_zero rfl), h_opcode.2,
        OpcodeSpec.RV64.execute_SLTI_equiv, OpcodeSpec.RV64.spec_SLTI_hypotheses,
        ⟨ -, h_spec_eq ⟩

    /-- `equivalence_SLTIU` in column form (opcode 9, `iop.SLTIU`), the unsigned set-less-than
        against an immediate. `imm` is the low 12 bits of `op_c_0`, read off the row as `rd` and
        `rs1` are; `op_c_value_setWidth_eq_op_c_0` ties it to the `op_c` value the row sends, whose
        64-bit form is its sign extension (`op_c_value_eq_signExtend_imm12`). The comparison is
        unsigned against that sign-extended value. The decoder gives opcode 9 a register `op_b`, so
        the theorem does not take `imm_b = 0` (`imm_b_eq_zero_of_opcode`). The ALU message at opcode
        9 is the CPU's own `SLTU` request; the branch comparisons use opcodes 264 and 265. -/
    theorem equivalence_SLTIU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 9 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := ((air.cols.instruction.op_c_0 row 0).val : BitVec 12)
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTIU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      itype_by_alu_spec (h_alu.imm_b_eq_zero rfl), h_opcode.2,
        OpcodeSpec.RV64.execute_SLTIU_equiv, OpcodeSpec.RV64.spec_SLTIU_hypotheses,
        ⟨ -, h_spec_eq ⟩

    -- ========================================================================
    -- The checked ITYPE theorems, in decoded form: each takes the instruction
    -- and an address whose decoding (`Transpiler.V3.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form. The proofs pass hypotheses as `@h`, which Lean elaborates
    -- without unfolding their types.
    -- ========================================================================

    /-- What an I-type instruction's decoding says about the row: it is real, its opcode is the
        operation's (`Transpiler.opcode_of_iop`), `imm_b = 0` and `imm_c = 1`, its `op_a` and
        `op_b_0` columns name `rd` and `rs1`, and the low 12 bits of `op_c_0` are `imm`. The
        decoder writes the low 16 bits of `imm`'s sign extension into `op_c_0`
        (`Transpiler.V3.imm_operand imm true`). -/
    private lemma itype_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      {imm : BitVec 12} {rs1 rd : regidx} {op : iop} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, op)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      air.cols.instruction.opcode row 0 = Transpiler.opcode_of_iop op ∧
      air.cols.opcode_selector.imm_b row 0 = 0 ∧
      air.cols.opcode_selector.imm_c row 0 = 1 ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      regidx.Regidx (air.cols.instruction.op_b_0 row 0).val = rs1 ∧
      ((air.cols.instruction.op_c_0 row 0).val : BitVec 12) = imm
    := by
      simp only [Transpiler.V3.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      have h_op_b : air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_c0 : air.cols.instruction.op_c_0 row 0 = (Transpiler.V3.imm_operand imm true)[0] :=
        decoded_field h_data ProgramBusEntry.c_0
      refine ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode, decoded_field h_data ProgramBusEntry.imm_b,
        decoded_field h_data ProgramBusEntry.imm_c,
        by rw [h_op_a]; exact regidx_reg_to_KB rd, by rw [h_op_b]; exact regidx_reg_to_KB rs1, ?_ ⟩
      obtain ⟨ h0, -, - ⟩ := Transpiler.V3.imm_operand_sext imm (by norm_num) (by norm_num)
      have h_low := congrArg BitVec.toNat (setWidth_signExtend_self imm (by norm_num))
      rw [BitVec.toNat_setWidth] at h_low
      rw [h_c0]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, h0]
      omega

    /-- Equivalence for ADDI (opcode 0, `iop.ADDI`): for every `ADDI` instruction and address `addr`
        whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding fixes `addr`
        only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_ADDI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, iop.ADDI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ADDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_b, h_imm_c, rfl, rfl, rfl ⟩ :=
        itype_decoded air row h_decode
      exact equivalence_ADDI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_b, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for XORI (opcode 2, `iop.XORI`): for every `XORI` instruction and address `addr`
        whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding fixes `addr`
        only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_XORI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, iop.XORI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.XORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        itype_decoded air row h_decode
      exact equivalence_XORI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for ORI (opcode 3, `iop.ORI`): for every `ORI` instruction and address `addr`
        whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding fixes `addr`
        only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_ORI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, iop.ORI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        itype_decoded air row h_decode
      exact equivalence_ORI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for ANDI (opcode 4, `iop.ANDI`): for every `ANDI` instruction and address `addr`
        whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding fixes `addr`
        only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_ANDI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, iop.ANDI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ANDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        itype_decoded air row h_decode
      exact equivalence_ANDI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SLTI (opcode 8, `iop.SLTI`), the signed set-less-than against an immediate:
        for every `SLTI` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLTI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, iop.SLTI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        itype_decoded air row h_decode
      exact equivalence_SLTI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SLTIU (opcode 9, `iop.SLTIU`), the unsigned set-less-than against an
        immediate: for every `SLTIU` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLTIU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, iop.SLTIU)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTIU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, -, h_imm_c, rfl, rfl, rfl ⟩ :=
        itype_decoded air row h_decode
      exact equivalence_SLTIU_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- The I-type theorems' decoding hypothesis holds on every real row of an I-type opcode with
        `imm_c = 1`, and `imm_b = 0` for `ADDI`'s opcode 0, which `LUI` and `AUIPC` share with
        `imm_b = 1`: there the Program table's promise (in `bus_row_wf_asm`) gives an I-type
        instruction of the operation and a 4-aligned address below
        `Transpiler.V3.code_address_bound` whose decoding is the row's Program message. -/
    theorem itype_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : iop)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_iop op)
      (h_imm_b : op = .ADDI → air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 12) (rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.ITYPE (imm, rs1, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode, deserialise_program_bus_entry] at h_from
      cases op <;>
      simp [ProgramBusEntry.decoded_from, Transpiler.opcode_of_iop, h_imm_b, h_imm_c]
        at h_from <;>
      · obtain ⟨ imm, rs1, rd, rfl ⟩ := h_from
        exact ⟨ imm, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end ITYPE

end Equivalence
