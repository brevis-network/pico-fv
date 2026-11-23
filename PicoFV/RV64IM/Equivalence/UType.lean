import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
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
    -- `pc + immediate` for `AUIPC`. Each theorem therefore takes the shape
    -- its instruction has, and `utype_row_cases` shows the two shapes cover
    -- every such row. Both operands are immediates, so the row reads no
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
      rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
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
        what makes `equivalence_LUI` and `equivalence_AUIPC` together cover the opcode. -/
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
          exact Transpiler.V3.imm_operand_toBV_sgn (imm ++ 0#12) (by norm_num) (by norm_num)
      · refine Or.inr ⟨ imm, ?_, ?_ ⟩
        · simp only [op_b_value, h_b.1, h_b.2.1, h_b.2.2.1, h_b.2.2.2, eq_b0, eq_b1, eq_bs]
          exact Transpiler.V3.imm_operand_toBV_sgn (imm ++ 0#12) (by norm_num) (by norm_num)
        · simp [op_c_value, pc, h_c.1, h_c.2.1, h_c.2.2.1, h_c.2.2.2, eq_c0, eq_c1, eq_cs,
                h_pc.1, h_pc.2.1]

    /-- Equivalence for LUI (opcode 0 with `imm_b = 1` and `imm_c = 1`,
        `instruction.UTYPE (imm, rd, .LUI)`). The row's `op_b` is zero and its `op_c` the
        immediate `signExtend 64 (imm ++ 0#12)`, so the ALU chip's promise for opcode 0
        (`op_a = op_b + op_c`) makes the result the immediate, and the next pc is `pc + 4`.

        Opcode 0 with both flags is `LUI` or `AUIPC` (`ProgramBusEntry.decoded_from`), so the
        theorem takes the `LUI` shape; `utype_row_cases` shows every such row has it or
        `AUIPC`'s. The immediate is a parameter the shape pins: `signExtend 64 (imm ++ 0#12)`
        determines `imm`.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_LUI
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
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (imm : BitVec 20)
      (h_op_b : U64w.toBV (op_b_value air row) = 0#64)
      (h_op_c : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 (imm ++ 0#12))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
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

    /-- Equivalence for AUIPC (opcode 0 with `imm_b = 1` and `imm_c = 1`,
        `instruction.UTYPE (imm, rd, .AUIPC)`). The row's `op_b` is the immediate
        `signExtend 64 (imm ++ 0#12)` and its `op_c` the row's pc, so the ALU chip's promise
        for opcode 0 (`op_a = op_b + op_c`) makes the result `pc + immediate`, and the next pc
        is `pc + 4`.

        Opcode 0 with both flags is `LUI` or `AUIPC` (`ProgramBusEntry.decoded_from`), so the
        theorem takes the `AUIPC` shape; `utype_row_cases` shows every such row has it or
        `LUI`'s.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_AUIPC
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
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (imm : BitVec 20)
      (h_op_b : U64w.toBV (op_b_value air row) = BitVec.signExtend 64 (imm ++ 0#12))
      (h_op_c : U64w.toBV (op_c_value air row) = U64w.toBV (pc air row))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
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

  end UTYPE

end Equivalence
