import PicoFV.RV64IM.Equivalence.TrialV3

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSectionVars false

/-! # Trial load and store against the Pico v3.1.1 memory contract (prototype, not for merging)

    Two instruction theorems, LW and SD, over the 58-column CPU chip and the draft 3.x memory
    contract (`RV64IM_Interactions.V3.MemoryBus.Spec` in `RVSail/BusesV3.lean`). They check that
    what the memory chip promises is enough for the CPU's side of a load and of a store. -/

namespace Equivalence.TrialV3

  open Plonky3
  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open Interaction

  section Decoder

    /-- A row with opcode 12 is LW. -/
    lemma lw_inversion
        (h_tr : Transpiler.V3.transpile_op instr 1 pc = .some (data, props))
        (h_op : data.2[2] = 12) :
        ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 4) := by
      cases instr <;> simp [Transpiler.V3.transpile_op] at h_tr <;>
        (try split at h_tr) <;> (try simp at h_tr) <;>
        (try (obtain ⟨ h_tr, _ ⟩ := h_tr; subst h_tr; simp at h_op))
      all_goals (try (rename_i x _ _; obtain ⟨ a, b, c, op ⟩ := x; cases op <;>
        simp [Transpiler.opcode_of_rop, Transpiler.opcode_of_ropw, Transpiler.opcode_of_iop,
              Transpiler.opcode_of_sop, Transpiler.opcode_of_sopw, Transpiler.opcode_of_bop] at h_op ⊢))
      all_goals (split at h_op <;> simp at h_op ⊢)
      rename_i x _ _ _ _ _ h1 h2
      exact ⟨ x.1, x.2.1, x.2.2.1, by rw [← h1, ← h2] ⟩

    /-- A row with opcode 47 is SD. -/
    lemma sd_inversion
        (h_tr : Transpiler.V3.transpile_op instr 1 pc = .some (data, props))
        (h_op : data.2[2] = 47) :
        ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 8) := by
      cases instr <;> simp [Transpiler.V3.transpile_op] at h_tr <;>
        (try split at h_tr) <;> (try simp at h_tr) <;>
        (try (obtain ⟨ h_tr, _ ⟩ := h_tr; subst h_tr; simp at h_op))
      all_goals (try (rename_i x _ _; obtain ⟨ a, b, c, op ⟩ := x; cases op <;>
        simp [Transpiler.opcode_of_rop, Transpiler.opcode_of_ropw, Transpiler.opcode_of_iop,
              Transpiler.opcode_of_sop, Transpiler.opcode_of_sopw, Transpiler.opcode_of_bop] at h_op ⊢))
      all_goals (split at h_op <;> simp at h_op ⊢)
      rename_i x _ _ _ _ h1
      exact ⟨ x.1, x.2.1, x.2.2.1, by rw [← h1] ⟩

  end Decoder

  section Trials

    variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}

    /-- LW: the row's operations change the Sail state as one step of `LW rd, imm(rs1)` does,
        for a real destination register and for `x0`. -/
    theorem equivalence_LW [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_row : row ≤ air.last_row)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
        (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
        (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
        (h_opcode : air.cols.instruction.opcode row 0 = 12)
        (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
        (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg) :
        let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
        let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
        let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
        execute_instruction (instruction.LOAD (imm, rs1, rd, false, 4)) state =
          (operation_list_effect (CPU_bus_operations air row) state).state := by
      have h_wf := h_all_wf row h_row
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, h_props ⟩ := program_wf air row h_is_real h_wf
      simp [program_bus_entry, ProgramBusEntry.deserialise] at h_eq
      obtain ⟨ _, e_pc0, e_pc1, e_op, _, e_a, e_b0, e_b1, e_bs, e_c0, e_c1, e_cs, e_ax0,
               e_ib, e_ic, e_ecall, e_mem, e_st, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu,
               e_jalr, e_jal, e_carry ⟩ := h_eq
      obtain ⟨ imm', rs1, rd, rfl ⟩ := lw_inversion h_tr (by rw [← e_op, h_opcode])
      obtain ⟨ rd_bv ⟩ := rd
      simp [Transpiler.V3.transpile_op] at h_tr
      obtain ⟨ rfl, _ ⟩ := h_tr
      simp at e_a e_b0 e_b1 e_bs e_c0 e_c1 e_cs e_ax0 e_ib e_ic e_ecall e_mem e_st e_beq e_bne e_blt e_bge e_bltu e_bgeu e_jalr e_jal
      clear e_op
      have h_imm := imm_operand_sext imm' (by norm_num) (by norm_num)
      have h_rd : (air.cols.instruction.op_a_0 row 0).val < 32 := by simp [e_a, Transpiler.reg_to_KB]
      have h_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32 := by simp [e_b0, Transpiler.reg_to_KB]
      have h_a0v : (air.cols.instruction.op_a_0 row 0).val = rd_bv.toNat := by
        simp [e_a, Transpiler.reg_to_KB, regidx_to_fin]
      have hc := row_constraints air row (h_all_constraints row h_row)
      simp only [row_constraint_list, List.forall_cons, List.Forall] at hc
      obtain ⟨ _, _, _, _, c4, c5, c6, c7, c8, c9, c10, c11, _, _, _, _, _, _, _, _,
               _, _, _, _, _, _, _, _, _, _, _, c31, _, _, _, _, _, c37, _ ⟩ := hc
      simp [constraint_4, constraint_5, constraint_6, constraint_7, e_ic, sub_eq_zero] at c4 c5 c6 c7
      simp [constraint_31, e_ecall] at c31
      simp [constraint_37, h_is_real, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jal, e_jalr, c31, sub_eq_zero] at c37
      have h_pc := pc_facts air row h_is_real h_wf
      have h_npc := next_pc_facts air row h_row h_is_real h_all_wf h_all_constraints pico_assumptions
      -- next_pc = pc + 4 as numbers: both sides are below the field size.
      have h_next : next_pc_val air row = pc_val air row + 4 := by
        have h := congrArg Fin.val c37
        simp only [Fin.val_add, Fin.val_mul] at h
        simp only [next_pc_val, pc_val] at h_npc h_pc ⊢
        norm_num at h
        omega
      -- The immediate and its 64-bit value.
      obtain ⟨ h_o0, h_o1, h_os ⟩ := h_imm
      have h_imm_lt : imm'.toNat < 4096 := imm'.isLt
      have h_sx : (BitVec.signExtend 64 imm').toNat = imm'.toNat + if imm'.msb then 2^64 - 2^12 else 0 := by
        simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]
      have h_msb : imm'.msb = decide (2^11 ≤ imm'.toNat) := BitVec.msb_eq_decide imm'
      have h_cv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        apply BitVec.eq_of_toNat_eq
        simp only [U64w.toBV_toNat, U64w.toNat, op_c_value, c4, c5, c6, c7, e_c0, e_c1, e_cs]
        rcases h_os with ⟨ hs, hlt ⟩ | ⟨ hs, hge, hlt ⟩ <;> simp [hs] <;> omega
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        rw [h_cv]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, h_sx]
        split <;> omega
      -- The memory chip's promise for this row's hand-off.
      have h_mem_wf := h_wf
      simp only [bus_row_wf_asm, bus_row, RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_mem_wf
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_opcode, MemoryBus.Spec] at h_mem_wf
      obtain ⟨ _, _, _, _, _, _, _, _, _, h_addr_ge, h_addr_lt, h_addr_al, h_ext ⟩ := h_mem_wf
      have h_addr_bridge :
          U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV (op_b_value air row) + U64w.toBV (op_c_value air row) := by
        rw [h_cv]
      have h_range :
          (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat < 2 ^ 48 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add, op_b_value, op_c_value]
        clear * - h_addr_lt; omega
      have h_align :
          (4 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add, op_b_value, op_c_value]
        exact_mod_cast h_addr_al
      -- The row's register and memory operations.
      simp only [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                 RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_bus_hypotheses
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1,
            mem_width_of_opcode, h_opcode, List.filterMap_cons] at h_bus_hypotheses
      clear c4 c5 c6 c7
      have h_addr : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat =
          (U64w.toNat (op_b_value air row) + U64w.toNat (op_c_value air row)) % 18446744073709551616 := by
        rw [← h_cv, BitVec.toNat_add]; simp
      have h_npc_bv : BitVec.ofNat 64 (next_pc_val air row) = BitVec.ofNat 64 (pc_val air row) + 4#64 := by
        rw [h_next, BitVec.ofNat_add]
      have h_x0_cases : air.cols.instruction.op_a_is_x0 row 0 = 1 ∨ air.cols.instruction.op_a_is_x0 row 0 = 0 := by
        rw [e_ax0]; split <;> simp
      rcases h_x0_cases with h_x0 | h_x0
      · -- The destination is x0: nothing is promised about the value, and nothing is written.
        simp [h_x0] at h_bus_hypotheses
        rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
        simp at h_bus_hypotheses
        obtain ⟨ h_rpc, h_reg1, h_reg0, h_mem ⟩ := h_bus_hypotheses
        have h_a0 : (air.cols.instruction.op_a_0 row 0).val = 0 := by
          rw [e_ax0] at h_x0
          simp at h_x0
          simp [e_a, h_x0, Transpiler.reg_to_KB, regidx_to_fin]
        simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin, h_a0] at h_mem
        simp only [BitVec.ofNatLT_eq_ofNat] at h_rpc h_reg1 h_reg0
        intro rd' rs1' immv
        have h_immv : immv = imm' := h_imm_eq
        rw [h_immv]
        have h_rd0 : rd' = regidx.Regidx 0#5 := by simp [rd', h_a0]
        have h_hyp : (operation_list_effect (OpcodeSpec.RV64.spec_LW rs1' rd' imm'
            (BitVec.ofNat 64 (pc_val air row)) (U64w.toBV (op_b_value air row)) 0#8 0#8 0#8 0#8) state).hypotheses := by
          rw [OpcodeSpec.RV64.spec_LW_hypotheses, h_rd0]
          simp only [beq_self_eq_true, if_true]
          rw [h_addr]
          refine ⟨ ?_, ?_, ?_ ⟩
          · simpa [pc_val] using h_rpc
          · simpa [op_b_value, rs1'] using h_reg1
          · simpa [op_b_value, op_c_value] using h_mem
        have key := OpcodeSpec.RV64.execute_LW_equiv h_hyp h_assumptions h_range h_align
        rw [key]
        simp only [OpcodeSpec.RV64.spec_LW, CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                   RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row]
        simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1,
              mem_width_of_opcode, h_opcode, h_x0, h_rd0]
        simp only [BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_writeReg_same h_reg1]
        simp only [operation_list_effect_state_readReg]
        rw [h_npc_bv]
        simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin, h_a0]
      · -- The destination is a real register: it receives the sign-extended 32-bit value read.
        simp [h_x0] at h_bus_hypotheses
        rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
        simp at h_bus_hypotheses
        obtain ⟨ h_rpc, h_reg1, h_reg0, h_mem ⟩ := h_bus_hypotheses
        have h_a0nz : (air.cols.instruction.op_a_0 row 0).val ≠ 0 := by
          rw [e_ax0] at h_x0
          simp at h_x0
          rw [h_a0v]
          intro h; apply h_x0; apply BitVec.eq_of_toNat_eq; simpa using h
        obtain ⟨ n, hn ⟩ : ∃ n, rd_bv.toNat = n + 1 := Nat.exists_eq_succ_of_ne_zero (by rw [← h_a0v]; exact h_a0nz)
        simp [operation_list_effect, operation_effect] at h_mem
        simp [write_xreg, e_a, Transpiler.reg_to_KB, regidx_to_fin, Sail.writeReg, PreSail.writeReg, hn] at h_mem
        simp only [BitVec.ofNatLT_eq_ofNat] at h_rpc h_reg1 h_reg0
        intro rd' rs1' immv
        have h_immv : immv = imm' := h_imm_eq
        rw [h_immv]
        have h_rd_ne : ¬ (rd' == regidx.Regidx 0#5) = true := by
          have : (BitVec.ofNat 5 (air.cols.instruction.op_a_0 row 0).val).toNat ≠ 0 := by
            rw [BitVec.toNat_ofNat]; omega
          simpa [rd', ← BitVec.toNat_inj] using this
        let v32 : BitVec 32 := BitVec.ofNat 16 (air.cols.op_a_access.access.value_1 row 0).val ++
                               BitVec.ofNat 16 (air.cols.op_a_access.access.value_0 row 0).val
        have h_hyp : (operation_list_effect (OpcodeSpec.RV64.spec_LW rs1' rd' imm'
            (BitVec.ofNat 64 (pc_val air row)) (U64w.toBV (op_b_value air row))
            (BitVec.extractLsb 7 0 v32) (BitVec.extractLsb 15 8 v32)
            (BitVec.extractLsb 23 16 v32) (BitVec.extractLsb 31 24 v32)) state).hypotheses := by
          rw [OpcodeSpec.RV64.spec_LW_hypotheses, if_neg h_rd_ne, h_addr]
          refine ⟨ ?_, ?_, ?_ ⟩
          · simpa [pc_val] using h_rpc
          · simpa [op_b_value, rs1'] using h_reg1
          · simpa [op_b_value, op_c_value, v32] using h_mem
        have key := OpcodeSpec.RV64.execute_LW_equiv h_hyp h_assumptions h_range h_align
        rw [key]
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.signExtend 64 v32 := by
          simp only [op_a_value]
          rw [h_ext h_x0]
          simp [v32, U32w.toBV]
        have h_append_eq :
            v32 = BitVec.extractLsb 31 24 v32 ++ BitVec.extractLsb 23 16 v32 ++
                  BitVec.extractLsb 15 8 v32 ++ BitVec.extractLsb 7 0 v32 := by
          clear *-; simp [BitVec.extractLsb, v32]
          (repeat rw [BitVec.extractLsb'_append_eq_ite]); simp
          set x₁ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)
          set x₂ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
          rw [BitVec.extractLsb'_append_extractLsb', BitVec.append_assoc, BitVec.extractLsb'_append_extractLsb']
          simp
        simp only [OpcodeSpec.RV64.spec_LW, CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                   RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row]
        simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1,
              mem_width_of_opcode, h_opcode, h_x0, h_rd_ne]
        simp only [BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_writeReg_same h_reg1]
        simp only [operation_list_effect_state_readReg]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        rw [← h_append_eq, ← h_a_ext, h_npc_bv]
        rfl

    /-- SD: the row's operations change the Sail state as one step of `SD rs2, imm(rs1)` does. -/
    theorem equivalence_SD [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_row : row ≤ air.last_row)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
        (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
        (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
        (h_opcode : air.cols.instruction.opcode row 0 = 47)
        (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
        (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg) :
        let rs2 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
        let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
        let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
        execute_instruction (instruction.STORE (imm, rs2, rs1, 8)) state =
          (operation_list_effect (CPU_bus_operations air row) state).state := by
      have h_wf := h_all_wf row h_row
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, h_props ⟩ := program_wf air row h_is_real h_wf
      simp [program_bus_entry, ProgramBusEntry.deserialise] at h_eq
      obtain ⟨ _, e_pc0, e_pc1, e_op, _, e_a, e_b0, e_b1, e_bs, e_c0, e_c1, e_cs, e_ax0,
               e_ib, e_ic, e_ecall, e_mem, e_st, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu,
               e_jalr, e_jal, e_carry ⟩ := h_eq
      obtain ⟨ imm', rs2, rs1, rfl ⟩ := sd_inversion h_tr (by rw [← e_op, h_opcode])
      simp [Transpiler.V3.transpile_op] at h_tr
      obtain ⟨ rfl, _ ⟩ := h_tr
      simp at e_a e_b0 e_b1 e_bs e_c0 e_c1 e_cs e_ax0 e_ib e_ic e_ecall e_mem e_st e_beq e_bne e_blt e_bge e_bltu e_bgeu e_jalr e_jal
      clear e_op
      have h_imm := imm_operand_sext imm' (by norm_num) (by norm_num)
      have h_rs2 : (air.cols.instruction.op_a_0 row 0).val < 32 := by simp [e_a, Transpiler.reg_to_KB]
      have h_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32 := by simp [e_b0, Transpiler.reg_to_KB]
      have hc := row_constraints air row (h_all_constraints row h_row)
      simp only [row_constraint_list, List.forall_cons, List.Forall] at hc
      obtain ⟨ _, _, _, _, c4, c5, c6, c7, _, _, _, _, _, c13, c14, c15, c16, _, _, _,
               _, _, _, _, _, _, _, _, _, _, _, c31, _, _, _, _, _, c37, _ ⟩ := hc
      simp [constraint_4, constraint_5, constraint_6, constraint_7, e_ic, sub_eq_zero] at c4 c5 c6 c7
      simp [constraint_13, constraint_14, constraint_15, constraint_16, e_st, e_beq, e_bne, e_blt, e_bge,
            e_bltu, e_bgeu, sub_eq_zero] at c13 c14 c15 c16
      simp [constraint_31, e_ecall] at c31
      simp [constraint_37, h_is_real, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jal, e_jalr, c31, sub_eq_zero] at c37
      have h_pc := pc_facts air row h_is_real h_wf
      have h_npc := next_pc_facts air row h_row h_is_real h_all_wf h_all_constraints pico_assumptions
      -- next_pc = pc + 4 as numbers: both sides are below the field size.
      have h_next : next_pc_val air row = pc_val air row + 4 := by
        have h := congrArg Fin.val c37
        simp only [Fin.val_add, Fin.val_mul] at h
        simp only [next_pc_val, pc_val] at h_npc h_pc ⊢
        norm_num at h
        omega
      -- The immediate and its 64-bit value.
      obtain ⟨ h_o0, h_o1, h_os ⟩ := h_imm
      have h_imm_lt : imm'.toNat < 4096 := imm'.isLt
      have h_sx : (BitVec.signExtend 64 imm').toNat = imm'.toNat + if imm'.msb then 2^64 - 2^12 else 0 := by
        simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]
      have h_msb : imm'.msb = decide (2^11 ≤ imm'.toNat) := BitVec.msb_eq_decide imm'
      have h_cv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        apply BitVec.eq_of_toNat_eq
        simp only [U64w.toBV_toNat, U64w.toNat, op_c_value, c4, c5, c6, c7, e_c0, e_c1, e_cs]
        rcases h_os with ⟨ hs, hlt ⟩ | ⟨ hs, hge, hlt ⟩ <;> simp [hs] <;> omega
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        rw [h_cv]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, h_sx]
        split <;> omega
      -- The memory chip's promise for this row's hand-off.
      have h_mem_wf := h_wf
      simp only [bus_row_wf_asm, bus_row, RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_mem_wf
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_opcode, MemoryBus.Spec] at h_mem_wf
      obtain ⟨ _, _, _, _, _, _, _, _, h_addr_ge, h_addr_lt, h_addr_al ⟩ := h_mem_wf
      have h_addr_bridge :
          U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV (op_b_value air row) + U64w.toBV (op_c_value air row) := by
        rw [h_cv]
      have h_range :
          (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat < 2 ^ 48 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add, op_b_value, op_c_value]
        clear * - h_addr_lt; omega
      have h_align :
          (8 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add, op_b_value, op_c_value]
        exact_mod_cast h_addr_al
      have h_addr : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat =
          (U64w.toNat (op_b_value air row) + U64w.toNat (op_c_value air row)) % 18446744073709551616 := by
        rw [← h_cv, BitVec.toNat_add]; simp
      have h_npc_bv : BitVec.ofNat 64 (next_pc_val air row) = BitVec.ofNat 64 (pc_val air row) + 4#64 := by
        rw [h_next, BitVec.ofNat_add]
      -- The row's register and memory operations.
      simp only [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                 RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_bus_hypotheses
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rs2, h_rs1,
            mem_width_of_opcode, h_opcode] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_rpc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
      simp only [BitVec.ofNatLT_eq_ofNat] at h_rpc h_reg1 h_reg0
      -- A store leaves register `a` as it was: the value sent is the value read (constraints 13 to 16).
      have h_reg0' :
          read_xreg (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 (air.cols.instruction.op_a_0 row 0).val))) state =
            EStateM.Result.ok
              (U64w.toBV
                #v[BitVec.ofNat 16 (air.cols.op_a_access.access.value_0 row 0).val,
                   BitVec.ofNat 16 (air.cols.op_a_access.access.value_1 row 0).val,
                   BitVec.ofNat 16 (air.cols.op_a_access.access.value_2 row 0).val,
                   BitVec.ofNat 16 (air.cols.op_a_access.access.value_3 row 0).val]) state := by
        rw [c13, c14, c15, c16]; exact h_reg0
      intro rs2' rs1' immv
      have h_immv : immv = imm' := h_imm_eq
      rw [h_immv]
      have h_hyp : (operation_list_effect (OpcodeSpec.RV64.spec_SD rs1' rs2' imm'
          (BitVec.ofNat 64 (pc_val air row)) (U64w.toBV (op_b_value air row))
          (U64w.toBV (op_a_value air row))) state).hypotheses := by
        rw [OpcodeSpec.RV64.spec_SD_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · simpa [pc_val] using h_rpc
        · simpa [op_b_value, rs1'] using h_reg1
        · exact h_reg0'
      have key := OpcodeSpec.RV64.execute_SD_equiv h_hyp h_assumptions h_range h_align
      rw [key]
      simp only [OpcodeSpec.RV64.spec_SD, CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                 RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row]
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rs2, h_rs1,
            mem_width_of_opcode, h_opcode]
      simp only [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_writeReg_same h_reg1]
      simp only [operation_list_effect_state_readReg]
      rw [operation_list_effect_state_writeReg_same h_reg0']
      rw [h_npc_bv]
      have h_c_nat := congrArg BitVec.toNat h_cv
      simp only [op_c_value, U64w.toBV_toNat] at h_c_nat
      simp [op_a_value, op_b_value, h_c_nat, operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

  end Trials

end Equivalence.TrialV3
