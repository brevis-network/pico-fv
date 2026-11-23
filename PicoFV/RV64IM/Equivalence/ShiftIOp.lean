import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section SHIFTIOP

    -- ========================================================================
    -- SHIFTIOP — the 64-bit shift-immediate class, three opcodes:
    --   SLLI = 5, SRLI = 6, SRAI = 7.
    -- They share their opcodes with SLL, SRL and SRA, which `imm_c = 0`
    -- tells apart (`ProgramBusEntry.decoded_from`), so each column-form
    -- theorem (`equivalence_<OP>_row`) takes `imm_c = 1`; the decoder fixes
    -- `imm_b = 0` for all three. The row reads `rs1` and sends the
    -- instruction's immediate as `op_c`. Each column form reads its 6-bit
    -- `imm` from the row's `op_c_0`, as it reads `rd` and `rs1`; the ALU chip
    -- shifts by the low 6 bits of the `op_c` value the row sends.
    -- `eq_operation_list_effect_state_of_shift_imm` links the two and does
    -- everything but the opcode's arm of `ALUBus.Spec`, which each proof gives
    -- last.
    --
    -- The checked theorems, `equivalence_<OP>`, take the instruction instead
    -- and the hypothesis that the decoder turns it into the row's Program
    -- message, which fixes `is_real`, the opcode, `imm_c`, the two register
    -- columns and `op_c_0` (`shiftiop_decoded`).
    -- ========================================================================

    /-- `equivalence_SLLI` in column form (opcode 5, `sop.SLLI`), the 64-bit shift left logical by
        an immediate. `imm` is the low 6 bits of `op_c_0`, read off the row as `rd` and `rs1` are.
        -/
    theorem equivalence_SLLI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 5 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SLLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_shift_imm (n := 6) (by norm_num) h_alu
        (h_alu.imm_b_eq_zero rfl) h_opcode.2 h_bus_hypotheses
        (fun v amount => v <<< amount.toNat)
        (fun _ _ h_reads => OpcodeSpec.RV64.execute_SLLI_equiv
          (by rw [OpcodeSpec.RV64.spec_SLLI_hypotheses]; exact h_reads))
        (fun h_spec => ?_)
      -- The ALU chip's arm for opcode 5.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- `equivalence_SRLI` in column form (opcode 6, `sop.SRLI`), the 64-bit shift right logical by
        an immediate. `imm` is the low 6 bits of `op_c_0`, read off the row as `rd` and `rs1` are.
        -/
    theorem equivalence_SRLI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 6 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_shift_imm (n := 6) (by norm_num) h_alu
        (h_alu.imm_b_eq_zero rfl) h_opcode.2 h_bus_hypotheses
        (fun v amount => v >>> amount.toNat)
        (fun _ _ h_reads => OpcodeSpec.RV64.execute_SRLI_equiv
          (by rw [OpcodeSpec.RV64.spec_SRLI_hypotheses]; exact h_reads))
        (fun h_spec => ?_)
      -- The ALU chip's arm for opcode 6.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    /-- `equivalence_SRAI` in column form (opcode 7, `sop.SRAI`), the 64-bit shift right arithmetic
        by an immediate. `imm` is the low 6 bits of `op_c_0`, read off the row as `rd` and `rs1`
        are. -/
    theorem equivalence_SRAI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 7 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRAI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 imm
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
      refine eq_operation_list_effect_state_of_shift_imm (n := 6) (by norm_num) h_alu
        (h_alu.imm_b_eq_zero rfl) h_opcode.2 h_bus_hypotheses
        (fun v amount => v.sshiftRight amount.toNat)
        (fun _ _ h_reads => OpcodeSpec.RV64.execute_SRAI_equiv
          (by rw [OpcodeSpec.RV64.spec_SRAI_hypotheses]; exact h_reads))
        (fun h_spec => ?_)
      -- The ALU chip's arm for opcode 7.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      obtain ⟨ -, h_spec_eq ⟩ := h_spec
      simp [op_a_value, op_b_value, op_c_value, h_spec_eq, execute_RTYPE_pure]

    -- ========================================================================
    -- The checked SHIFTIOP theorems, in decoded form: each takes the instruction
    -- and an address whose decoding (`Transpiler.V3.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What the decoding of a 64-bit shift by an immediate says about the row: it is real, its
        opcode is the operation's (`Transpiler.opcode_of_sop`), `imm_c = 1`, its `op_a` and `op_b_0`
        columns name `rd` and `rs1`, and the low 6 bits of `op_c_0` are `imm`. The decoder
        zero-extends the shift amount into `op_c_0` (`Transpiler.V3.imm_operand imm false`). -/
    private lemma shiftiop_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      {imm : BitVec 6} {rs1 rd : regidx} {op : sop} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.SHIFTIOP (imm, rs1, rd, op)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      air.cols.instruction.opcode row 0 = Transpiler.opcode_of_sop op ∧
      air.cols.opcode_selector.imm_c row 0 = 1 ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      regidx.Regidx (air.cols.instruction.op_b_0 row 0).val = rs1 ∧
      ((air.cols.instruction.op_c_0 row 0).val : BitVec 6) = imm
    := by
      simp only [Transpiler.V3.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      have h_op_b : air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_c0 : air.cols.instruction.op_c_0 row 0 = (Transpiler.V3.imm_operand imm false)[0] :=
        decoded_field h_data ProgramBusEntry.c_0
      refine ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode, decoded_field h_data ProgramBusEntry.imm_c,
        by rw [h_op_a]; exact regidx_reg_to_KB rd, by rw [h_op_b]; exact regidx_reg_to_KB rs1, ?_ ⟩
      rw [h_c0]
      apply BitVec.eq_of_toNat_eq
      have := imm.isLt
      simp [Transpiler.V3.imm_operand, Transpiler.imm_to_KB, BitVec.extend, U64w.fromNat]
      omega

    /-- Equivalence for SLLI (opcode 5, `sop.SLLI`), the 64-bit shift left logical by an immediate:
        for every `SLLI` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SLLI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 6} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.SHIFTIOP (imm, rs1, rd, sop.SLLI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SLLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ :=
        shiftiop_decoded air row h_decode
      exact equivalence_SLLI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRLI (opcode 6, `sop.SRLI`), the 64-bit shift right logical by an immediate:
        for every `SRLI` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SRLI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 6} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.SHIFTIOP (imm, rs1, rd, sop.SRLI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ :=
        shiftiop_decoded air row h_decode
      exact equivalence_SRLI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- Equivalence for SRAI (opcode 7, `sop.SRAI`), the 64-bit shift right arithmetic by an
        immediate: for every `SRAI` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's Program message, Sail's step
        on that instruction equals the row's effect. The decoding fixes `addr` only modulo `2 ^ 32`,
        through the row's two 16-bit pc pieces. -/
    theorem equivalence_SRAI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 6} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.SHIFTIOP (imm, rs1, rd, sop.SRAI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRAI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opc, h_imm_c, rfl, rfl, rfl ⟩ :=
        shiftiop_decoded air row h_decode
      exact equivalence_SRAI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions ⟨ h_opc, h_imm_c ⟩ @h_bus_hypotheses

    /-- The `SHIFTIOP` theorems' decoding hypothesis holds on every real row of a `SHIFTIOP` opcode
        with `imm_c = 1`, which tells the shift from `SLL`, `SRL` and `SRA`: there the Program
        table's promise (in `bus_row_wf_asm`) gives a 64-bit shift by an immediate of the operation
        and a 4-aligned address below `Transpiler.V3.code_address_bound` whose decoding is the row's
        Program message. -/
    theorem shiftiop_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : sop)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_sop op)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 6) (rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.SHIFTIOP (imm, rs1, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode, deserialise_program_bus_entry] at h_from
      cases op <;>
      simp [ProgramBusEntry.decoded_from, Transpiler.opcode_of_sop, h_imm_c] at h_from <;>
      · obtain ⟨ imm, rs1, rd, rfl ⟩ := h_from
        exact ⟨ imm, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end SHIFTIOP

end Equivalence
