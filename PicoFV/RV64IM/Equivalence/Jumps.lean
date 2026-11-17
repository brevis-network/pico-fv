import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 4_000_000
set_option maxRecDepth 1_000_000

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
    -- decoder fixes both immediate flags and the row's jump selector, and
    -- neither statement takes them: the 2.x statements took `imm_b`, `imm_c`
    -- and `is_jal` / `is_jalr`, and dropping a hypothesis makes the theorem
    -- stronger. JAL carries its 21-bit offset in `op_b` (`imm_b = 1`), JALR
    -- its 12-bit offset in `op_c` (`imm_c = 1`).
    --
    -- Both rows write the return address `pc + 4` into `op_a` unless the
    -- destination is `x0` (`jump_return_address`), and both set the next pc:
    -- JAL to `pc + offset` (`jal_next_pc`), JALR to `rs1 + offset` with bit 0
    -- cleared (`jalr_target`). Sail's success condition for both is that the
    -- target is 4-aligned, which `next_pc_facts` carries.
    -- ========================================================================

    /-- Cutting a sign extension back to the immediate's own width returns the immediate.
        Both theorems read their `imm` back from the chip's operand columns, where the
        decoder put it sign-extended, so both need it. The 2.x proofs reached for a
        compiled-code bitvector decision procedure here; this is the same fact by
        `getLsbD`, so the file needs none. -/
    private lemma setWidth_signExtend_self {w : ℕ} (imm : BitVec w) (hw : w ≤ 64) :
      (BitVec.signExtend 64 imm).setWidth w = imm
    := by
      ext i hi
      simp [BitVec.getElem_setWidth]
      rw [BitVec.getLsbD_signExtend]
      simp [hi]
      omega

    /-- Equivalence for JAL (opcode 24, `instruction.JAL`). The next pc is `pc + offset`, the
        sign-extended 21-bit immediate the decoder put in `op_b` (`jal_next_pc`, constraint 24),
        and the return address is `pc + 4` (`jump_return_address`) on a row whose destination
        is not `x0`.

        Opcode 24 is `JAL` alone (`ProgramBusEntry.decoded_from`), so the decoder fixes both
        immediate flags and the `is_jal` selector; the statement takes none of the three.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_JAL
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
      have h_wf : bus_row_wf_asm (bus_row air row) := h_all_wf row h_row
      have h_constraints : CpuChip.Extraction.allHold air row := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      -- The Program message, and the instruction it was decoded from.
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, h_al, h_lt, h_eq, h_eq_entry, h_props ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      simp [ProgramBusEntry.decoded_from, h_opcode] at h_decoded
      obtain ⟨ imm', rd', h_eq_instr ⟩ := h_decoded
      subst h_eq_instr
      simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst h_eq_data
      rw [deserialise_program_bus_entry] at h_eq_entry
      simp [ProgramBusEntry.deserialise] at h_eq_entry
      obtain ⟨ -, h_pc0, h_pc1, -, eq_a, eq_b0, eq_b1, eq_bs, eq_c0, eq_c1, eq_cs, eq_a_is_x0,
               eq_imm_b, eq_imm_c, h_s_ecall, h_s_mem, h_s_store, h_s_beq, h_s_bne, h_s_blt,
               h_s_bge, h_s_bltu, h_s_bgeu, h_s_jalr, h_s_jal, h_pc_carry ⟩ := h_eq_entry
      obtain ⟨ h_reg_rd, -, - ⟩ := register_indices_lt air row h_is_real h_wf
      -- `op_b` is the sign-extended 21-bit offset.
      have h_imm_b_eqs := imm_b_eq_1_constraints air row eq_imm_b h_constraints
      have h_op_b_bv : U64w.toBV (op_b_value air row) = BitVec.signExtend 64 imm' := by
        simp only [op_b_value, h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1,
                   h_imm_b_eqs.2.2.2, eq_b0, eq_b1, eq_bs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)
      have h_imm_eq : (U64w.toBV (op_b_value air row)).setWidth 21 = imm' := by
        rw [h_op_b_bv, setWidth_signExtend_self imm' (by norm_num)]
      -- A 21-bit offset stays inside `2 ^ 20` of zero, which is what makes constraint 24's
      -- single field equation an exact 64-bit addition.
      have h_bounds := CpuChip.Interpretations.imm_operand_offset_bounds
        (w := 21) (by norm_num) (by norm_num) imm'
      have h_jal := jal_next_pc air row h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_s_jal
        (by rw [eq_b0, eq_b1, eq_bs]; exact h_bounds.1)
        (by rw [eq_b0, eq_b1, eq_bs]; exact h_bounds.2)
      -- The target is 4-aligned, which is Sail's success condition.
      have h_npc_mod4 := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      have h_eq : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + BitVec.signExtend 64 imm' := by
        rw [← h_op_b_bv]
        exact h_jal.2
      have h_success : (U64w.toBV (pc air row) + BitVec.signExtend 64 imm') % 4 = 0 := by
        rw [← h_eq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_npc_mod4.2]
      -- The row's messages, as operations on the Sail state.
      have h_bus := h_bus_hypotheses
      simp [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, deserialise_bus_row,
            raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, eq_imm_b, eq_imm_c, h_s_mem,
            h_reg_rd] at h_bus
      obtain ⟨ h_pc_read, h_read_a, h_rest ⟩ := h_bus
      extract_lets rd imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [OpcodeSpec.RV64.execute_JAL_equiv
            (pc_val := U64w.toBV (pc air row))
            (misa := misa)
            (h_success := by
              clear * - h_success
              rw [BitVec.mod_4_zero_equiv_64] at h_success
              grind)]
      · simp [OpcodeSpec.RV64.spec_JAL, CPU_bus_operations,
                RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, eq_imm_b, eq_imm_c, h_s_mem,
                h_reg_rd, rd, BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_swap_writePC_writeReg, ← h_eq]
        by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
        · -- The destination is `x0`: neither side's write changes the state.
          rw [operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0]),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0])]
        · have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
            rw [eq_a_is_x0]
            have h_ne : ¬ (rd' == regidx.Regidx 0#5) = true := by
              intro h
              simp at h
              subst h
              exact h_rd0 (by rw [eq_a]; rfl)
            simp [h_ne]
          have h_ret := jump_return_address air row h_is_real h_wf h_constraints
            (by rw [h_s_jal, h_s_jalr]; norm_num) h_a_is_x0
          rw [← h_ret]
      · rw [OpcodeSpec.RV64.spec_JAL_hypotheses]
        rw [h_pc_read]
        congr 1
        simp [pc, ← BitVec.toNat_inj, U64w.toNat]
        omega
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto

    /-- Equivalence for JALR (opcode 25, `instruction.JALR`). The target is `rs1 + imm` with
        bit 0 cleared, which is what `jalr_target` reads off constraints 26 to 30, and the
        return address is `pc + 4` (`jump_return_address`) on a row whose destination is not
        `x0`.

        Opcode 25 is `JALR` alone (`ProgramBusEntry.decoded_from`), so the decoder fixes both
        immediate flags and the `is_jalr` selector; the statement takes none of the three.

        The bus assumptions are part of every instruction theorem's statement; the ones this
        proof does not read are named with a leading underscore. -/
    theorem equivalence_JALR
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
      have h_wf : bus_row_wf_asm (bus_row air row) := h_all_wf row h_row
      have h_constraints : CpuChip.Extraction.allHold air row := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      -- The Program message, and the instruction it was decoded from.
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, h_al, h_lt, h_eq, h_eq_entry, h_props ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      simp [ProgramBusEntry.decoded_from, h_opcode] at h_decoded
      obtain ⟨ imm', rs1', rd', h_eq_instr ⟩ := h_decoded
      subst h_eq_instr
      simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst h_eq_data
      rw [deserialise_program_bus_entry] at h_eq_entry
      simp [ProgramBusEntry.deserialise] at h_eq_entry
      obtain ⟨ -, h_pc0, h_pc1, -, eq_a, eq_b0, eq_b1, eq_bs, eq_c0, eq_c1, eq_cs, eq_a_is_x0,
               eq_imm_b, eq_imm_c, h_s_ecall, h_s_mem, h_s_store, h_s_beq, h_s_bne, h_s_blt,
               h_s_bge, h_s_bltu, h_s_bgeu, h_s_jalr, h_s_jal, h_pc_carry ⟩ := h_eq_entry
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 eq_imm_b
      -- `op_c` is the sign-extended 12-bit offset.
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        simp only [op_c_value, h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1,
                   h_imm_c_eqs.2.2.2, eq_c0, eq_c1, eq_cs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        rw [h_op_c_bv, setWidth_signExtend_self imm' (by norm_num)]
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
      have h_bus := h_bus_hypotheses
      simp [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, deserialise_bus_row,
            raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, eq_imm_b, eq_imm_c, h_s_mem,
            h_reg_rd, h_reg_rs1] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      extract_lets rd rs1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [OpcodeSpec.RV64.execute_JALR_equiv
            (pc_val := U64w.toBV (pc air row))
            (rs1_val := U64w.toBV (op_b_value air row))
            (misa := misa) (mseccfg := mseccfg)]
      · simp [OpcodeSpec.RV64.spec_JALR, CPU_bus_operations,
              RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
              MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, eq_imm_b, eq_imm_c, h_s_mem,
              h_reg_rd, h_reg_rs1, rd, rs1, BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_writeReg_same
              (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
            operation_list_effect_state_readReg]
        rw [h_sum_eq, ← h_jalr.1, operation_list_effect_state_swap_writePC_writeReg]
        by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
        · -- The destination is `x0`: neither side's write changes the state.
          rw [operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0]),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0])]
        · have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
            rw [eq_a_is_x0]
            have h_ne : ¬ (rd' == regidx.Regidx 0#5) = true := by
              intro h
              simp at h
              subst h
              exact h_rd0 (by rw [eq_a]; rfl)
            simp [h_ne]
          have h_ret := jump_return_address air row h_is_real h_wf h_constraints
            (by rw [h_s_jal, h_s_jalr]; norm_num) h_a_is_x0
          rw [← h_ret]
      · rw [OpcodeSpec.RV64.spec_JALR_hypotheses]
        refine ⟨ ?_, ?_ ⟩
        · rw [h_pc_read]
          congr 1
          simp [pc, ← BitVec.toNat_inj, U64w.toNat]
          omega
        · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · rw [h_sum_eq, ← BitVec.mod_4_lt_two_equiv_64]
        exact h_jalr.2


  end JUMPS

end Equivalence
