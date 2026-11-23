import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section JUMPS

    -- ========================================================================
    -- JUMPS — the two jump opcodes: JAL = 24, JALR = 25.
    -- Neither opcode is shared (`ProgramBusEntry.decoded_from`), so the
    -- decoder fixes both immediate flags and the row's jump selector, and no
    -- statement takes them. JAL carries its 21-bit offset in `op_b`
    -- (`imm_b = 1`), JALR its 12-bit offset in `op_c` (`imm_c = 1`).
    --
    -- Both rows write the return address `pc + 4` into `op_a` unless the
    -- destination is `x0` (`jump_return_address`), and both set the next pc:
    -- JAL to `pc + offset` (`jal_next_pc`), JALR to `rs1 + offset` with bit 0
    -- cleared (`jalr_target`). Sail's success condition differs: for JAL it is
    -- that the target is 4-aligned, which `next_pc_mod_four_eq_zero` carries;
    -- for JALR it is that bit 1 of the unmasked sum `rs1 + offset` is zero,
    -- which is the second half of `jalr_target`.
    --
    -- The column-form theorems (`equivalence_JAL_row`, `equivalence_JALR_row`)
    -- read the registers and the offset off the row; the checked theorems, in
    -- decoded form, follow them.
    -- ========================================================================

    /-- A JAL row's flags and selectors, as opcode 24 fixes them (`selector_exclusivity`):
        both operands are immediates, `is_jal` is set, and the row is neither a JALR nor a
        memory row. -/
    private lemma jal_row_selectors
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 24)
    :
      air.cols.opcode_selector.imm_b row 0 = 1 ∧
      air.cols.opcode_selector.imm_c row 0 = 1 ∧
      air.cols.opcode_selector.is_jal row 0 = 1 ∧
      air.cols.opcode_selector.is_jalr row 0 = 0 ∧
      air.cols.opcode_selector.is_memory row 0 = 0
    := by
      obtain ⟨ h_sel, h_b, h_c ⟩ :=
        selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
      rw [h_opcode] at h_sel h_b h_c
      simp [class_selectors_of_opcode, imm_b_of_opcode, imm_c_of_opcode] at h_sel h_b h_c
      exact ⟨ h_b, h_c, h_sel.2.2.2.2.2.2.2.2.2.2, h_sel.2.2.2.2.2.2.2.2.2.1, h_sel.2.1 ⟩

    /-- A JALR row's flags and selectors, as opcode 25 fixes them (`selector_exclusivity`):
        `op_b` is the register `rs1` and `op_c` the immediate, `is_jalr` is set, and the row is
        neither a JAL nor a memory row. -/
    private lemma jalr_row_selectors
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 25)
    :
      air.cols.opcode_selector.imm_b row 0 = 0 ∧
      air.cols.opcode_selector.imm_c row 0 = 1 ∧
      air.cols.opcode_selector.is_jal row 0 = 0 ∧
      air.cols.opcode_selector.is_jalr row 0 = 1 ∧
      air.cols.opcode_selector.is_memory row 0 = 0
    := by
      obtain ⟨ h_sel, h_b, h_c ⟩ :=
        selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
      rw [h_opcode] at h_sel h_b h_c
      simp [class_selectors_of_opcode, imm_b_of_opcode, imm_c_of_opcode] at h_sel h_b h_c
      exact ⟨ h_b, h_c, h_sel.2.2.2.2.2.2.2.2.2.2, h_sel.2.2.2.2.2.2.2.2.2.1, h_sel.2.1 ⟩

    /-- JAL's offset: the Program message says the row's `op_b` columns encode a 21-bit
        immediate `imm'`, and `op_b` is then its 64-bit sign extension (constraints 0 to 3,
        through `imm_b_eq_1_constraints`). -/
    private lemma jal_offset
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 24)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 1)
    :
      ∃ imm' : BitVec 21,
        air.cols.instruction.op_b_0 row 0 = (Transpiler.V3.imm_operand imm' true)[0] ∧
        air.cols.instruction.op_b_1 row 0 = (Transpiler.V3.imm_operand imm' true)[1] ∧
        air.cols.instruction.op_b_sign row 0 = (Transpiler.V3.imm_operand imm' true)[2] ∧
        U64w.toBV (op_b_value air row) = BitVec.signExtend 64 imm'
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      simp [ProgramBusEntry.decoded_from, h_opcode] at h_decoded
      obtain ⟨ imm', rd', h_eq_instr ⟩ := h_decoded
      subst h_eq_instr
      simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, - ⟩ := h_eq
      subst h_eq_data
      rw [deserialise_program_bus_entry] at h_eq_entry
      simp [ProgramBusEntry.deserialise] at h_eq_entry
      have eq_b0 : air.cols.instruction.op_b_0 row 0 =
          (Transpiler.V3.imm_operand imm' true)[0] := by simp [h_eq_entry]
      have eq_b1 : air.cols.instruction.op_b_1 row 0 =
          (Transpiler.V3.imm_operand imm' true)[1] := by simp [h_eq_entry]
      have eq_bs : air.cols.instruction.op_b_sign row 0 =
          (Transpiler.V3.imm_operand imm' true)[2] := by simp [h_eq_entry]
      refine ⟨ imm', eq_b0, eq_b1, eq_bs, ?_ ⟩
      have h_imm_b_eqs := imm_b_eq_1_constraints air row h_imm_b h_constraints
      simp only [op_b_value, h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1,
                 h_imm_b_eqs.2.2.2, eq_b0, eq_b1, eq_bs]
      exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)

    /-- JALR's offset: the Program message says the row's `op_c` columns encode a 12-bit
        immediate `imm'`, and `op_c` is then its 64-bit sign extension (constraints 4 to 7,
        through `imm_c_eq_1_constraints`). -/
    private lemma jalr_offset
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 25)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ imm' : BitVec 12, U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm'
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      simp [ProgramBusEntry.decoded_from, h_opcode] at h_decoded
      obtain ⟨ imm', rs1', rd', h_eq_instr ⟩ := h_decoded
      subst h_eq_instr
      simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, - ⟩ := h_eq
      subst h_eq_data
      rw [deserialise_program_bus_entry] at h_eq_entry
      simp [ProgramBusEntry.deserialise] at h_eq_entry
      have eq_c0 : air.cols.instruction.op_c_0 row 0 =
          (Transpiler.V3.imm_operand imm' true)[0] := by simp [h_eq_entry]
      have eq_c1 : air.cols.instruction.op_c_1 row 0 =
          (Transpiler.V3.imm_operand imm' true)[1] := by simp [h_eq_entry]
      have eq_cs : air.cols.instruction.op_c_sign row 0 =
          (Transpiler.V3.imm_operand imm' true)[2] := by simp [h_eq_entry]
      refine ⟨ imm', ?_ ⟩
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_imm_c h_constraints
      simp only [op_c_value, h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1,
                 h_imm_c_eqs.2.2.2, eq_c0, eq_c1, eq_cs]
      exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)

    /-- The operations a JAL row's messages stand for, in order: the pc read, the read of
        `rd`'s old value and the write of the return address, and the next pc. Both operands
        are immediates, so neither sends a message. -/
    private lemma CPU_bus_operations_eq_of_jal
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 24)
    :
      CPU_bus_operations air row =
        [ .ReadPC (U64w.toBV (pc air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_prev_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC (U64w.toBV (next_pc air row)) ]
    := by
      obtain ⟨ h_imm_b, h_imm_c, -, -, h_s_mem ⟩ :=
        jal_row_selectors air row h_is_real h_wf h_opcode
      obtain ⟨ h_reg_rd, -, - ⟩ := register_indices_lt air row h_is_real h_wf
      rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
          deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
          deserialise_raw_bus_row_Memory]
      simp [MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, h_imm_b, h_imm_c, h_s_mem, h_reg_rd, BitVec.ofNatLT_eq_ofNat,
            toBV_pc_eq_ofNat air row h_is_real h_wf, op_a_prev_value, op_a_value]

    /-- The operations a JALR row's messages stand for, in order: the pc read, a read and
        write back of `rs1`, the read of `rd`'s old value and the write of the return address,
        and the next pc. `op_c` is the immediate, so it sends no message: the shared
        `CPU_bus_operations_eq_of_imm_c_eq_one`. -/
    private lemma CPU_bus_operations_eq_of_jalr
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 25)
    :
      CPU_bus_operations air row =
        [ .ReadPC (U64w.toBV (pc air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_prev_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC (U64w.toBV (next_pc air row)) ]
    := by
      obtain ⟨ h_imm_b, h_imm_c, -, -, - ⟩ :=
        jalr_row_selectors air row h_is_real h_wf h_opcode
      exact CPU_bus_operations_eq_of_imm_c_eq_one air row h_is_real h_wf h_imm_b h_imm_c
        (by simp [mem_width_of_opcode, h_opcode])

    /-- On a jump row whose destination is not `x0`, the chip's `op_a` value is the return
        address `pc + 4` (`jump_return_address`); `op_a_is_x0` is 0 there (`op_a_is_x0_eq`). -/
    private lemma jump_op_a_value
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_jump : air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0 = 1)
      (h_rd0 : ¬ (air.cols.instruction.op_a row 0).val = 0)
    :
      U64w.toBV (op_a_value air row) = U64w.toBV (pc air row) + 4#64
    := by
      have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
        rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
        simp [Fin.ext_iff, h_rd0]
      exact jump_return_address air row h_is_real h_wf h_constraints h_jump h_a_is_x0

    /-- `equivalence_JAL` in column form: for a row of opcode 24, Sail's step on the `JAL` whose
        destination and offset are read off the row's columns equals the row's effect. The next
        pc is `pc + offset`, the sign-extended 21-bit immediate the decoder put in `op_b`
        (`jal_next_pc`, constraint 24), and the return address is `pc + 4`
        (`jump_return_address`) on a row whose destination is not `x0`.

        Opcode 24 is `JAL` alone (`ProgramBusEntry.decoded_from`), so the decoder fixes both
        immediate flags and the `is_jal` selector; the statement takes none of the three. -/
    theorem equivalence_JAL_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 24)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let imm : BitVec 21 := (U64w.toBV (op_b_value air row)).setWidth 21
      execute_instruction (instruction.JAL (imm, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, -, h_s_jal, h_s_jalr, - ⟩ :=
        jal_row_selectors air row h_is_real h_wf h_opcode
      obtain ⟨ imm', eq_b0, eq_b1, eq_bs, h_op_b_bv ⟩ :=
        jal_offset air row h_is_real h_wf h_constraints h_opcode h_imm_b
      -- A 21-bit offset stays inside `2 ^ 20` of zero, which is what makes constraint 24's
      -- single field equation an exact 64-bit addition.
      have h_bounds := imm_operand_offset_bounds (w := 21) (by norm_num) (by norm_num) imm'
      have h_jal := jal_next_pc air row h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_s_jal
        (by rw [eq_b0, eq_b1, eq_bs]; exact h_bounds.1)
        (by rw [eq_b0, eq_b1, eq_bs]; exact h_bounds.2)
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + BitVec.signExtend 64 imm' := by
        rw [← h_op_b_bv]
        exact h_jal.2
      -- The target is 4-aligned, which is Sail's success condition for JAL.
      have h_npc_mod4 := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      have h_success : (U64w.toBV (pc air row) + BitVec.signExtend 64 imm') % 4 = 0 := by
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_npc_mod4.2]
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_jal air row h_is_real h_wf h_opcode] at h_bus_hypotheses ⊢
      extract_lets rd imm
      rw [show imm = imm' by
            simp only [imm, h_op_b_bv]; exact setWidth_signExtend_self imm' (by norm_num)]
      rw [OpcodeSpec.RV64.execute_JAL_equiv
            (pc_val := U64w.toBV (pc air row))
            (misa := misa)
            (h_success := by
              clear * - h_success
              rw [BitVec.mod_4_zero_equiv_64] at h_success
              grind)]
      · simp [OpcodeSpec.RV64.spec_JAL, rd]
        rw [operation_list_effect_state_swap_writePC_writeReg, ← h_next]
        by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
        · -- The destination is `x0`: neither side's write changes the state.
          rw [operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0]),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0])]
        · rw [jump_op_a_value air row h_is_real h_wf h_constraints
                (by rw [h_s_jal, h_s_jalr]; norm_num) h_rd0]
      · rw [OpcodeSpec.RV64.spec_JAL_hypotheses]
        simp at h_bus_hypotheses
        exact h_bus_hypotheses.1
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto

    /-- `equivalence_JALR` in column form: for a row of opcode 25, Sail's step on the `JALR`
        whose registers and offset are read off the row's columns equals the row's effect. The
        target is `rs1 + imm` with bit 0 cleared, which is what `jalr_target` reads off
        constraints 26 to 30, and the return address is `pc + 4` (`jump_return_address`) on a
        row whose destination is not `x0`.

        Opcode 25 is `JALR` alone (`ProgramBusEntry.decoded_from`), so the decoder fixes both
        immediate flags and the `is_jalr` selector; the statement takes none of the three. -/
    theorem equivalence_JALR_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 25)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.JALR (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ -, h_imm_c, h_s_jal, h_s_jalr, - ⟩ :=
        jalr_row_selectors air row h_is_real h_wf h_opcode
      obtain ⟨ imm', h_op_c_bv ⟩ :=
        jalr_offset air row h_is_real h_wf h_constraints h_opcode h_imm_c
      -- The target: `op_b + op_c` with bit 0 cleared, and bit 1 of the sum zero.
      have h_jalr := jalr_target air row h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_s_jalr
      have h_sum_eq : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c_bv]; rfl
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_jalr air row h_is_real h_wf h_opcode] at h_bus_hypotheses ⊢
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c_bv]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, - ⟩ := h_bus_hypotheses
      rw [OpcodeSpec.RV64.execute_JALR_equiv
            (pc_val := U64w.toBV (pc air row))
            (rs1_val := U64w.toBV (op_b_value air row))
            (misa := misa) (mseccfg := mseccfg)]
      · simp [OpcodeSpec.RV64.spec_JALR, rd, rs1]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg]
        rw [h_sum_eq, ← h_jalr.1, operation_list_effect_state_swap_writePC_writeReg]
        by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
        · -- The destination is `x0`: neither side's write changes the state.
          rw [operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0]),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0])]
        · rw [jump_op_a_value air row h_is_real h_wf h_constraints
                (by rw [h_s_jal, h_s_jalr]; norm_num) h_rd0]
      · rw [OpcodeSpec.RV64.spec_JALR_hypotheses]
        exact ⟨ h_pc_read, by simpa [rs1] using h_read_b ⟩
      -- Sail's success condition: bit 1 of the unmasked sum is zero (`jalr_target`).
      case h_success =>
        rw [h_sum_eq, ← BitVec.mod_4_lt_two_equiv_64]
        exact h_jalr.2
      -- The `misa` and `mseccfg` reads, from `RISC_V_assumptions`.
      all_goals
        clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto

    -- ========================================================================
    -- The checked jump theorems, in decoded form: each takes the jump and an
    -- address whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1)
    -- is the row's Program message, and is proved from its column form.
    --
    -- The proofs pass hypotheses as `@h`: on the store and load sections that
    -- elaborated about 2.3 times faster than passing them bare. It does not
    -- avoid every unfolding: checking `@h_bus_hypotheses` against its expected
    -- type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What a `JAL`'s decoding says about the row: it is real, its opcode is 24, its `op_a`
        column names `rd`, and the low 21 bits of its `op_b` value are the offset (constraints
        0 to 3, through `imm_b_eq_1_constraints`). -/
    private lemma jal_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_constraints : CpuChip.Extraction.allHold air row)
      {imm : BitVec 21} {rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.JAL (imm, rd)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      air.cols.instruction.opcode row 0 = 24 ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      (U64w.toBV (op_b_value air row)).setWidth 21 = imm
    := by
      simp only [Transpiler.V3.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      obtain ⟨ e0, e1, e2, e3 ⟩ := imm_b_eq_1_constraints air row
        (decoded_field h_data ProgramBusEntry.imm_b) h_constraints
      have h_b0 : air.cols.instruction.op_b_0 row 0 = (Transpiler.V3.imm_operand imm true)[0] :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_b1 : air.cols.instruction.op_b_1 row 0 = (Transpiler.V3.imm_operand imm true)[1] :=
        decoded_field h_data ProgramBusEntry.b_1
      have h_bs : air.cols.instruction.op_b_sign row 0 =
          (Transpiler.V3.imm_operand imm true)[2] :=
        decoded_field h_data ProgramBusEntry.b_sign
      have h_op_b : U64w.toBV (op_b_value air row) = BitVec.signExtend 64 imm := by
        simp only [op_b_value, e0, e1, e2, e3, h_b0, h_b1, h_bs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm (by norm_num) (by norm_num)
      exact ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode,
        by rw [h_op_a]; exact regidx_reg_to_KB rd,
        by rw [h_op_b]; exact setWidth_signExtend_self imm (by norm_num) ⟩

    /-- What a `JALR`'s decoding says about the row: it is real, its opcode is 25, its `op_a`
        and `op_b` columns name `rd` and `rs1`, and the low 12 bits of its `op_c` value are the
        offset. -/
    private lemma jalr_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_constraints : CpuChip.Extraction.allHold air row)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.JALR (imm, rs1, rd)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      air.cols.instruction.opcode row 0 = 25 ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rd ∧
      regidx.Regidx (air.cols.instruction.op_b_0 row 0).val = rs1 ∧
      (U64w.toBV (op_c_value air row)).setWidth 12 = imm
    := by
      simp only [Transpiler.V3.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rd :=
        decoded_field h_data ProgramBusEntry.op_a
      have h_op_b : air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_op_c := op_c_value_eq_signExtend_of_imm_operand air row imm (by norm_num)
        (by norm_num) (decoded_field h_data ProgramBusEntry.imm_c) h_constraints
        (decoded_field h_data ProgramBusEntry.c_0) (decoded_field h_data ProgramBusEntry.c_1)
        (decoded_field h_data ProgramBusEntry.c_sign)
      exact ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode,
        by rw [h_op_a]; exact regidx_reg_to_KB rd, by rw [h_op_b]; exact regidx_reg_to_KB rs1,
        by rw [h_op_c]; exact setWidth_signExtend_self imm (by norm_num) ⟩

    /-- Equivalence for JAL (opcode 24, `instruction.JAL`): for every `JAL` instruction and
        address `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the
        row's Program message, Sail's step on that instruction equals the row's effect. The
        decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_JAL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 21} {rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.JAL (imm, rd)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.JAL (imm, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl ⟩ :=
        jal_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_JAL_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- Equivalence for JALR (opcode 25, `instruction.JALR`): for every `JALR` instruction and
        address `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the
        row's Program message, Sail's step on that instruction equals the row's effect. The
        decoding fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_JALR
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs1 rd : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.JALR (imm, rs1, rd)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.JALR (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        jalr_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_JALR_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- `equivalence_JAL`'s decoding hypothesis holds on every real row of opcode 24: there the
        Program table's promise (in `bus_row_wf_asm`) gives a `JAL` and a 4-aligned address
        below `Transpiler.V3.code_address_bound` whose decoding is the row's Program message. -/
    theorem jal_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 24)
    :
      ∃ (imm : BitVec 21) (rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.JAL (imm, rd)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      obtain ⟨ imm, rd, rfl ⟩ := h_from
      exact ⟨ imm, rd, addr, props, h_al, h_lt, h_dec ⟩

    /-- `equivalence_JALR`'s decoding hypothesis holds on every real row of opcode 25: there the
        Program table's promise (in `bus_row_wf_asm`) gives a `JALR` and a 4-aligned address
        below `Transpiler.V3.code_address_bound` whose decoding is the row's Program message. -/
    theorem jalr_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 25)
    :
      ∃ (imm : BitVec 12) (rs1 rd : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.JALR (imm, rs1, rd)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      obtain ⟨ imm, rs1, rd, rfl ⟩ := h_from
      exact ⟨ imm, rs1, rd, addr, props, h_al, h_lt, h_dec ⟩

  end JUMPS

end Equivalence
