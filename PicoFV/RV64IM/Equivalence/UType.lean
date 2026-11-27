import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section UTYPE

    -- ========================================================================
    -- UTYPE — `LUI` and `AUIPC`. Both are opcode 0 with both immediate flags
    -- set, and Pico has no `is_auipc` selector and no opcode 27, so the
    -- opcode and the flags no longer tell them apart: a `LUI` row and an
    -- `AUIPC` row have the same shape, and the decoder's clause for opcode 0
    -- (`ProgramBusEntry.decoded_from`) is a disjunction of the two.
    --
    -- What tells them apart is where the row carries the 32-bit immediate
    -- `imm ++ 0#12` (Pico v3.2.0, `disassembler/rrs.rs:342-366`):
    --
    --   * `LUI`   — `op_b` is zero and `op_c` is the immediate;
    --   * `AUIPC` — `op_b` is the immediate and `op_c` is the row's pc.
    --
    -- Either way the row is an ALU row of opcode 0, so the ALU chip's promise
    -- makes `op_a` the sum `op_b + op_c`: the immediate for `LUI`, and
    -- `pc + immediate` for `AUIPC`. Each column-form theorem
    -- (`equivalence_LUI_row`, `equivalence_AUIPC_row`) therefore takes the
    -- shape its instruction has, and `utype_row_cases` shows the two shapes
    -- cover every such row. The decoded theorems take the instruction instead,
    -- and its decoding gives the shape (`utype_decoded`);
    -- `utype_decode_satisfiable` shows every such row decodes from a `LUI` or
    -- an `AUIPC`. Both operands are immediates, so the row reads no
    -- source register: its operations are `JAL`'s (the pc read, the read of
    -- `rd`'s old value and the write of `rd`, and the next pc).
    --
    -- The shapes are not exclusive: a row whose `op_b` is zero and whose
    -- `op_c` is the row's pc has both, as `AUIPC 0` and as the `LUI` of the
    -- pc's upper bits (which needs the pc to be a multiple of `2 ^ 12`, but
    -- is not implied by it). Both theorems then hold of the row, because
    -- both instructions write the pc.
    -- ========================================================================

    /-- The operations a `LUI` or `AUIPC` row's messages stand for, in order: the pc read, the
        read of `rd`'s old value and the write of the result, and the next pc. Both operands
        are immediates, so neither sends a message. -/
    private lemma CPU_bus_operations_eq_of_utype
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
    :
      CPU_bus_operations air row =
        [ .ReadPC (U64w.toBV (pc air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_prev_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC (U64w.toBV (next_pc air row)) ]
    := by
      obtain ⟨ h_op, h_imm_b, h_imm_c ⟩ := h_opcode
      -- Opcode 0 sets no class selector, so the row sends no Memory message.
      have h_s_mem := (alu_class_selectors_zero air row h_is_real h_wf (by rw [h_op]; rfl)).2.1
      obtain ⟨ h_reg_rd, -, - ⟩ := register_indices_lt air row h_is_real h_wf
      rw [CPU_bus_operations, RV64IM_Interactions.bus_operations,
          deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
          deserialise_raw_bus_row_Memory]
      simp [MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_op, h_imm_b, h_imm_c, h_s_mem, h_reg_rd, BitVec.ofNatLT_eq_ofNat,
            toBV_pc_eq_ofNat air row h_is_real h_wf, op_a_prev_value, op_a_value]

    /-- The proof shared by `LUI` and `AUIPC`, in one call. `exec` is the Sail step: given the
        pc read, `h_exec` rewrites it into "read the pc, write `pc + 4`, write `v` to `rd`".
        `h_v` says `v` is `op_b + op_c`, which the ALU chip's promise for opcode 0 makes the
        row's `op_a` value. Then `exec` is the state the row's messages leave. -/
    private lemma eq_operation_list_effect_state_of_utype
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      {exec : EStateM.Result (Sail.Error exception)
        (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult}
      {air : Valid_CpuChip FKB ExtF} {row : ℕ}
      (h : ALURowFacts air row 0)
      (h_imm : air.cols.opcode_selector.imm_b row 0 = 1 ∧
               air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (v : BitVec 64)
      (h_exec :
        Sail.readReg Register.PC state = .ok (U64w.toBV (pc air row)) state →
        exec = (operation_list_effect
          [ .ReadPC (U64w.toBV (pc air row)),
            .WritePC (U64w.toBV (pc air row) + 4#64),
            .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val) v ] state).state)
      (h_v : U64w.toBV (op_b_value air row) + U64w.toBV (op_c_value air row) = v)
    :
      exec = (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_ops := CPU_bus_operations_eq_of_utype air row h.is_real (h.all_wf row h.row_le)
        ⟨ h.opcode_eq, h_imm ⟩
      rw [h_ops, operation_list_effect_hypotheses_readPC] at h_bus_hypotheses
      rw [h_exec h_bus_hypotheses.1, h_ops]
      rw [operation_list_effect_state_readPC, operation_list_effect_state_swap_writePC_writeReg,
          operation_list_effect_state_readPC, operation_list_effect_state_readReg,
          h.toBV_next_pc_eq]
      refine operation_list_effect_state_writeReg_eq_op_a_value h v (fun h_spec => ?_) _
      -- `ALUBus.Spec 0`: the `op_a` value is `op_b + op_c`.
      simp only [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      exact h_v.symm.trans h_spec.2.symm

    /-- Every row of opcode 0 with both immediate flags set has one of the two U-type shapes:
        `op_b` zero with the immediate in `op_c` (`LUI`), or the immediate in `op_b` with the
        row's pc in `op_c` (`AUIPC`). This is the decoder's clause for opcode 0 read through
        the constraints that tie the operand values to the instruction's columns, and it is
        what makes the column forms `equivalence_LUI_row` and `equivalence_AUIPC_row` together
        cover the opcode; for the decoded theorems, `utype_decode_satisfiable` does. -/
    theorem utype_row_cases
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
    :
      (∃ imm : BitVec 20,
        U64w.toBV (op_b_value air row) = 0#64 ∧
        U64w.toBV (op_c_value air row) = BitVec.signExtend 64 (imm ++ 0#12)) ∨
      (∃ imm : BitVec 20,
        U64w.toBV (op_b_value air row) = BitVec.signExtend 64 (imm ++ 0#12) ∧
        U64w.toBV (op_c_value air row) = U64w.toBV (pc air row))
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_op, h_imm_b, h_imm_c ⟩ := h_opcode
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ :=
        program_bus_operand_properties air row h_is_real h_wf
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      have h_pc := ProgramBusEntry.inversion_pc h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded h_pc
      simp [ProgramBusEntry.decoded_from, h_op, h_imm_b, h_imm_c] at h_decoded h_pc
      have h_b := imm_b_eq_1_constraints air row h_imm_b h_constraints
      have h_c := imm_c_eq_1_constraints air row h_imm_c h_constraints
      obtain ⟨ imm, _rd, h_shape ⟩ := h_decoded
      rcases h_shape with ⟨ -, eq_b0, eq_b1, eq_bs, eq_c0, eq_c1, eq_cs ⟩ |
                          ⟨ -, eq_b0, eq_b1, eq_bs, eq_c0, eq_c1, eq_cs ⟩
      · refine Or.inl ⟨ imm, ?_, ?_ ⟩
        · simp [op_b_value, h_b.1, h_b.2.1, h_b.2.2.1, h_b.2.2.2, eq_b0, eq_b1, eq_bs, U64w.toBV]
        · simp only [op_c_value, h_c.1, h_c.2.1, h_c.2.2.1, h_c.2.2.2, eq_c0, eq_c1, eq_cs]
          exact Transpiler.imm_operand_toBV_sgn (imm ++ 0#12) (by norm_num) (by norm_num)
      · refine Or.inr ⟨ imm, ?_, ?_ ⟩
        · simp only [op_b_value, h_b.1, h_b.2.1, h_b.2.2.1, h_b.2.2.2, eq_b0, eq_b1, eq_bs]
          exact Transpiler.imm_operand_toBV_sgn (imm ++ 0#12) (by norm_num) (by norm_num)
        · simp [op_c_value, pc, h_c.1, h_c.2.1, h_c.2.2.1, h_c.2.2.2, eq_c0, eq_c1, eq_cs,
                h_pc.1, h_pc.2.1]

    /-- `equivalence_LUI` in column form: for a row of opcode 0 with `imm_b = 1` and
        `imm_c = 1` and the `LUI` shape, Sail's step on `instruction.UTYPE (imm, rd, .LUI)`,
        with `rd` read off the row's `op_a` column, equals the row's effect. The row's `op_b` is
        zero and its `op_c` the immediate `signExtend 64 (imm ++ 0#12)`, so the ALU chip's
        promise for opcode 0 (`op_a = op_b + op_c`) makes the result the immediate, and the next
        pc is `pc + 4`.

        Opcode 0 with both flags is `LUI` or `AUIPC` (`ProgramBusEntry.decoded_from`), so the
        theorem takes the `LUI` shape; `utype_row_cases` shows every such row has it or
        `AUIPC`'s. The immediate is a parameter the shape pins: `signExtend 64 (imm ++ 0#12)`
        determines `imm`. -/
    theorem equivalence_LUI_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (imm : BitVec 20)
      (h_op_b : U64w.toBV (op_b_value air row) = 0#64)
      (h_op_c : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 (imm ++ 0#12))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd
      exact eq_operation_list_effect_state_of_utype
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
        h_opcode.2 h_bus_hypotheses _
        (fun h_pc => OpcodeSpec.RV64.execute_LUI_equiv
          (by rw [OpcodeSpec.RV64.spec_LUI_hypotheses]; exact h_pc))
        (by rw [h_op_b, h_op_c]; simp)

    /-- `equivalence_AUIPC` in column form: for a row of opcode 0 with `imm_b = 1` and
        `imm_c = 1` and the `AUIPC` shape, Sail's step on `instruction.UTYPE (imm, rd, .AUIPC)`,
        with `rd` read off the row's `op_a` column, equals the row's effect. The row's `op_b` is
        the immediate `signExtend 64 (imm ++ 0#12)` and its `op_c` the row's pc, so the ALU
        chip's promise for opcode 0 (`op_a = op_b + op_c`) makes the result `pc + immediate`,
        and the next pc is `pc + 4`.

        Opcode 0 with both flags is `LUI` or `AUIPC` (`ProgramBusEntry.decoded_from`), so the
        theorem takes the `AUIPC` shape; `utype_row_cases` shows every such row has it or
        `LUI`'s. -/
    theorem equivalence_AUIPC_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (imm : BitVec 20)
      (h_op_b : U64w.toBV (op_b_value air row) = BitVec.signExtend 64 (imm ++ 0#12))
      (h_op_c : U64w.toBV (op_c_value air row) = U64w.toBV (pc air row))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd
      exact eq_operation_list_effect_state_of_utype
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, h_opcode.1, rfl ⟩
        h_opcode.2 h_bus_hypotheses _
        (fun h_pc => OpcodeSpec.RV64.execute_AUIPC_equiv
          (by rw [OpcodeSpec.RV64.spec_AUIPC_hypotheses]; exact h_pc))
        (by rw [h_op_b, h_op_c, BitVec.add_comm])

    -- ========================================================================
    -- The checked U-type theorems, in decoded form: each takes the instruction
    -- and an address whose decoding (`Transpiler.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form. The decoding fixes the operand shape, so neither takes it.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What a `LUI`'s or an `AUIPC`'s decoding says about the row: it is real, its opcode is 0
        with both immediate flags set, its `op_a` column names `rd`, and its operands have the
        instruction's shape: for `LUI` the `op_b` value is zero and the `op_c` value the
        immediate `signExtend 64 (imm ++ 0#12)`, for `AUIPC` the `op_b` value is that immediate
        and the `op_c` value the row's pc (constraints 0 to 7, through `imm_b_eq_1_constraints`
        and `imm_c_eq_1_constraints`). -/
    private lemma utype_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_constraints : CpuChip.Extraction.allHold air row)
      {imm : BitVec 20} {rd : regidx} {op : uop} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.UTYPE (imm, rd, op)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      (air.cols.instruction.opcode row 0 = 0 ∧
        air.cols.opcode_selector.imm_b row 0 = 1 ∧
        air.cols.opcode_selector.imm_c row 0 = 1) ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      (op = .LUI →
        U64w.toBV (op_b_value air row) = 0#64 ∧
        U64w.toBV (op_c_value air row) = BitVec.signExtend 64 (imm ++ 0#12)) ∧
      (op = .AUIPC →
        U64w.toBV (op_b_value air row) = BitVec.signExtend 64 (imm ++ 0#12) ∧
        U64w.toBV (op_c_value air row) = U64w.toBV (pc air row))
    := by
      simp only [Transpiler.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_imm_b : air.cols.opcode_selector.imm_b row 0 = 1 :=
        decoded_field h_data ProgramBusEntry.imm_b
      have h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1 :=
        decoded_field h_data ProgramBusEntry.imm_c
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      obtain ⟨ e0, e1, e2, e3 ⟩ := imm_b_eq_1_constraints air row h_imm_b h_constraints
      refine ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        ⟨ decoded_field h_data ProgramBusEntry.opcode, h_imm_b, h_imm_c ⟩,
        by rw [h_op_a]; exact regidx_reg_to_KB rd, ?_, ?_ ⟩
      · rintro rfl
        have h_b0 : air.cols.instruction.op_b_0 row 0 = 0 :=
          decoded_field h_data ProgramBusEntry.b_0
        have h_b1 : air.cols.instruction.op_b_1 row 0 = 0 :=
          decoded_field h_data ProgramBusEntry.b_1
        have h_bs : air.cols.instruction.op_b_sign row 0 = 0 :=
          decoded_field h_data ProgramBusEntry.b_sign
        refine ⟨ by simp [op_b_value, e0, e1, e2, e3, h_b0, h_b1, h_bs, U64w.toBV], ?_ ⟩
        exact op_c_value_eq_signExtend_of_imm_operand air row (imm ++ 0#12) (by norm_num)
          (by norm_num) h_imm_c h_constraints
          (decoded_field h_data ProgramBusEntry.c_0) (decoded_field h_data ProgramBusEntry.c_1)
          (decoded_field h_data ProgramBusEntry.c_sign)
      · rintro rfl
        obtain ⟨ f0, f1, f2, f3 ⟩ := imm_c_eq_1_constraints air row h_imm_c h_constraints
        have h_b0 : air.cols.instruction.op_b_0 row 0 =
            (Transpiler.imm_operand (imm ++ 0#12) true)[0] :=
          decoded_field h_data ProgramBusEntry.b_0
        have h_b1 : air.cols.instruction.op_b_1 row 0 =
            (Transpiler.imm_operand (imm ++ 0#12) true)[1] :=
          decoded_field h_data ProgramBusEntry.b_1
        have h_bs : air.cols.instruction.op_b_sign row 0 =
            (Transpiler.imm_operand (imm ++ 0#12) true)[2] :=
          decoded_field h_data ProgramBusEntry.b_sign
        have h_c0 : air.cols.instruction.op_c_0 row 0 = Transpiler.pc_lo addr :=
          decoded_field h_data ProgramBusEntry.c_0
        have h_c1 : air.cols.instruction.op_c_1 row 0 = Transpiler.pc_hi addr :=
          decoded_field h_data ProgramBusEntry.c_1
        have h_cs : air.cols.instruction.op_c_sign row 0 = 0 :=
          decoded_field h_data ProgramBusEntry.c_sign
        have h_pc0 : air.cols.pc_0 row 0 = Transpiler.pc_lo addr :=
          decoded_field h_data ProgramBusEntry.pc_0
        have h_pc1 : air.cols.pc_1 row 0 = Transpiler.pc_hi addr :=
          decoded_field h_data ProgramBusEntry.pc_1
        refine ⟨ ?_, by simp [op_c_value, pc, f0, f1, f2, f3, h_c0, h_c1, h_cs, h_pc0, h_pc1] ⟩
        simp only [op_b_value, e0, e1, e2, e3, h_b0, h_b1, h_bs]
        exact Transpiler.imm_operand_toBV_sgn (imm ++ 0#12) (by norm_num) (by norm_num)

    /-- Equivalence for LUI (opcode 0 with `imm_b = 1` and `imm_c = 1`,
        `instruction.UTYPE (imm, rd, .LUI)`): for every `LUI` instruction and address `addr`
        whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's Program
        message, Sail's step on that instruction equals the row's effect. The decoding puts the
        row in the `LUI` shape, so the theorem takes no operand hypothesis. The decoding fixes
        `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_LUI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 20} {rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.UTYPE (imm, rd, .LUI)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, h_shape, - ⟩ :=
        utype_decoded air row (h_all_constraints row h_row) h_decode
      obtain ⟨ h_op_b, h_op_c ⟩ := h_shape rfl
      exact equivalence_LUI_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions @h_opcode imm @h_op_b @h_op_c @h_bus_hypotheses

    /-- Equivalence for AUIPC (opcode 0 with `imm_b = 1` and `imm_c = 1`,
        `instruction.UTYPE (imm, rd, .AUIPC)`): for every `AUIPC` instruction and address
        `addr` whose decoding (`Transpiler.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        puts the row in the `AUIPC` shape, so the theorem takes no operand hypothesis. The
        decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_AUIPC
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 20} {rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.transpile_op (.UTYPE (imm, rd, .AUIPC)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, -, h_shape ⟩ :=
        utype_decoded air row (h_all_constraints row h_row) h_decode
      obtain ⟨ h_op_b, h_op_c ⟩ := h_shape rfl
      exact equivalence_AUIPC_row air row @h_row @h_is_real @h_all_wf @h_all_constraints
        @pico_assumptions @h_opcode imm @h_op_b @h_op_c @h_bus_hypotheses

    /-- The U-type theorems' decoding hypothesis holds, for `LUI` or for `AUIPC`, on every real
        row of opcode 0 with `imm_b = 1`: there the Program table's promise (in
        `bus_row_wf_asm`) gives a `LUI` or an `AUIPC` and a 4-aligned address below
        `Transpiler.code_address_bound` whose decoding is the row's Program message. The flag
        is what tells the two from `ADD` and `ADDI`, which share opcode 0 with `imm_b = 0`.
        Which of the two it is the opcode and the flags do not say
        (`ProgramBusEntry.decoded_from`); the operand shapes tell them apart except where they
        overlap, and there both hold (`utype_row_cases`). -/
    theorem utype_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 0)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 1)
    :
      ∃ (imm : BitVec 20) (rd : regidx) (op : uop) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.code_address_bound ∧
        Transpiler.transpile_op (.UTYPE (imm, rd, op)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      rcases h_from with ⟨ h_b, - ⟩ | ⟨ h_b, - ⟩ |
        ⟨ -, -, imm, rd, ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ ⟩
      · have h_b' : air.cols.opcode_selector.imm_b row 0 = 0 := h_b
        rw [h_imm_b] at h_b'
        exact absurd h_b' (by decide)
      · have h_b' : air.cols.opcode_selector.imm_b row 0 = 0 := h_b
        rw [h_imm_b] at h_b'
        exact absurd h_b' (by decide)
      · exact ⟨ imm, rd, .LUI, addr, props, h_al, h_lt, h_dec ⟩
      · exact ⟨ imm, rd, .AUIPC, addr, props, h_al, h_lt, h_dec ⟩

  end UTYPE

end Equivalence
