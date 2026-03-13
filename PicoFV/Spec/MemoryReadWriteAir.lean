import PicoFV.Constraints.MemoryReadWriteAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace AddSubAir.Spec

  open RV32IM_Interactions
  open MemoryReadWriteAir.ConstraintsAndBuses
  open MemoryReadWriteAir.Interactions

  set_option maxHeartbeats 1_000_000_000

  lemma spec_LB
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 10)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
    obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
             h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
             h_off_aligned_addr,
             h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
             h_off_b_b3_decomp,
             u1, u2, u3, h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3, h_constraints ⟩ := h_constraints
    clear u0 u1 u2 u3
    simp [bus_row, *] at asm_state
    obtain ⟨ ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := asm_state
    simp [h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3] at h_constraints
    clear h_eq_mav0 h_eq_mav1 h_eq_mav2 h_eq_mav3
    obtain ⟨ h_eq_uval0, h_eq_uval1, h_eq_uval2, h_eq_uval3,
              h_b_msb_d0, h_b_msb_d1, h_b_msb_d2, h_b_msb_d3, h_b_msb_d4, h_b_msb_d5, h_b_msb_d6, h_b_msb_d7, h_msb_decomp,
              h_op_a_0, h_eq_neg, h_eq_pos,
              h_eq_pos0, h_eq_pos1, h_eq_pos2, h_eq_pos3,
              h_constraints ⟩ := h_constraints
    clear h_constraints
    obtain ⟨ ub_uval0, h_d7_eq_msb_uval0 ⟩ :
      air.cols.unsigned_mem_val_0 row 0 < 256 ∧
      (air.cols.unsigned_mem_val_0 row 0 < 128 ↔ air.cols.msb_decomp_7 row 0 = 0)
    := by
      clear *- h_b_msb_d0 h_b_msb_d1 h_b_msb_d2 h_b_msb_d3
                h_b_msb_d4 h_b_msb_d5 h_b_msb_d6 h_b_msb_d7 h_msb_decomp
      split_ands
      . grind
      . constructor <;> grind
    split_ands
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
        simp [h_eq_neg] at asm_neg_val
        simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        clear *- ub_uval0 h_eq_uval1 h_eq_uval2 h_eq_uval3
        omega
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
        simp [h_eq_neg, ALUBus.Spec] at asm_neg_val
        clear *- asm_neg_val; omega
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
        simp [h_eq_neg] at asm_neg_val
        simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        simp [← BitVec.toInt_inj, BitVec.extend]; unfold U32.toInt
        simp [U32.negative, U32.toNat, BitVec.toInt_signExtend_of_le]
        simp [BitVec.toInt]
        rw [if_neg (by omega), if_pos (by omega)]
        omega
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
        clear h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [h_eq_neg, ALUBus.Spec] at asm_neg_val
        obtain ⟨ ub_av, ub_umv, asm_neg_val⟩ := asm_neg_val
        simp [h_eq_uval1, h_eq_uval2, h_eq_uval3] at asm_neg_val
        have h_sign_extend : forall x, U32.toBV #v[x, 0#8, 0#8, 0#8] - U32.toBV #v[0#8, 1#8, 0#8, 0#8] = U32.toBV #v[x, 255, 255, 255]
        := by
          clear *-; intro x
          simp [U32.toBV, -List.getElem_cons_succ]
          repeat rw [List.getElem_cons_succ]
          repeat rw [List.getElem_cons_zero]
          simp
          bv_check "MemoryReadWriteAir.lean-sign_extend_sub_single.lrat"
        rw [h_sign_extend] at asm_neg_val
        apply U32.toBV_inj at asm_neg_val
        simp at asm_neg_val; simp [asm_neg_val]
        simp [U32.toBV, -List.getElem_cons_succ]
        repeat rw [List.getElem_cons_succ]
        repeat rw [List.getElem_cons_zero]
        simp [BitVec.extend, BitVec.signExtend_eq_append_extractLsb']
        rw [if_pos]
        . grind
        . simp [BitVec.msb_eq_decide]
          omega

  lemma spec_LBU
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 13)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
    obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
             h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
             h_off_aligned_addr,
             h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
             h_off_b_b3_decomp,
             u1, u2, u3, h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3, h_constraints ⟩ := h_constraints
    clear u0 u1 u2 u3
    simp [bus_row, *] at asm_state
    obtain ⟨ ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := asm_state
    simp [h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3] at h_constraints
    clear h_eq_mav0 h_eq_mav1 h_eq_mav2 h_eq_mav3
    obtain ⟨ h_eq_uval0, h_eq_uval1, h_eq_uval2, h_eq_uval3,
              h_b_msb_d0, h_b_msb_d1, h_b_msb_d2, h_b_msb_d3, h_b_msb_d4, h_b_msb_d5, h_b_msb_d6, h_b_msb_d7,
              h_op_a_0, h_eq_neg, h_eq_pos,
              h_eq_pos0, h_eq_pos1, h_eq_pos2, h_eq_pos3,
              h_constraints ⟩ := h_constraints
    clear h_constraints
    obtain ub_uval0 : air.cols.unsigned_mem_val_0 row 0 < 256
    := by
      clear *- h_eq_uval0 h_off_b_o1 h_off_b_o2 h_off_b_o3
               h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
               ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
      grind
    split_ands
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      clear *- ub_uval0 h_eq_uval1 h_eq_uval2 h_eq_uval3
      omega
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      simp [← BitVec.toNat_inj, U32.toNat, BitVec.extend]
      omega

  lemma spec_LH
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 11)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
    obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
             h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
             h_off_aligned_addr,
             h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
             h_off_b_b3_decomp,
             u1, u2, u3, h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3, h_constraints ⟩ := h_constraints
    clear u0 u1 u2 u3
    simp [bus_row, *] at asm_state
    obtain ⟨ ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := asm_state
    simp [h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3] at h_constraints
    clear h_eq_mav0 h_eq_mav1 h_eq_mav2 h_eq_mav3
    obtain ⟨ h_offset_characterisation, h_eq_uval0, h_eq_uval1, h_eq_uval2, h_eq_uval3,
             h_b_msb_d0, h_b_msb_d1, h_b_msb_d2, h_b_msb_d3, h_b_msb_d4, h_b_msb_d5, h_b_msb_d6, h_b_msb_d7, h_msb_decomp,
             h_op_a_0, h_eq_neg, h_eq_pos,
             h_eq_pos0, h_eq_pos1, h_eq_pos2, h_eq_pos3,
             h_constraints ⟩ := h_constraints
    clear h_constraints
    obtain ⟨ ub_uval0, ub_uval1, h_d7_eq_msb_uval1 ⟩ :
      air.cols.unsigned_mem_val_0 row 0 < 256 ∧ air.cols.unsigned_mem_val_1 row 0 < 256 ∧
      (air.cols.unsigned_mem_val_1 row 0 < 128 ↔ air.cols.msb_decomp_7 row 0 = 0)
    := by
      clear *- h_b_msb_d0 h_b_msb_d1 h_b_msb_d2 h_b_msb_d3
               h_b_msb_d4 h_b_msb_d5 h_b_msb_d6 h_b_msb_d7 h_msb_decomp
               h_off_b_o1 h_off_b_o2 h_off_b_o3
               h_eq_uval0 h_off_b_o1 h_off_b_o2 h_off_b_o3
               h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
               ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
      split_ands
      . clear h_b_msb_d0 h_b_msb_d1 h_b_msb_d2 h_b_msb_d3
              h_b_msb_d4 h_b_msb_d5 h_b_msb_d6 h_b_msb_d7 h_msb_decomp
        grind
      . clear h_eq_uval0 h_off_b_o1 h_off_b_o2 h_off_b_o3
              h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
              ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
        grind
      . clear h_eq_uval0 h_off_b_o1 h_off_b_o2 h_off_b_o3
              h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
              ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
        constructor <;> grind
    split_ands
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval1 h_eq_neg h_eq_pos
        simp [h_eq_neg] at asm_neg_val
        simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        clear *- ub_uval0 ub_uval1 h_eq_uval2 h_eq_uval3
        omega
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval1 h_eq_neg h_eq_pos
        simp [h_eq_neg, ALUBus.Spec] at asm_neg_val
        clear *- asm_neg_val; omega
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
      . simp [h_b_msb_d7] at h_eq_neg h_eq_pos
        simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [h_eq_uval2, h_eq_uval3] at h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        simp [← BitVec.toInt_inj, BitVec.extend]; unfold U32.toInt
        simp [U32.negative, U32.toNat, BitVec.toInt_signExtend_of_le]
        simp [BitVec.toInt]
        rw [if_neg (by omega), BitVec.toNat_append]
        simp
        repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
        rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
        simp [Nat.shiftLeft_eq_mul_pow]
        rw [if_pos (by omega)]
        omega
      . clear h_eq_pos h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [h_b_msb_d7] at h_eq_neg h_d7_eq_msb_uval1
        simp [ALUBus.Spec, *] at asm_neg_val
        obtain ⟨ ub_av, asm_neg_val⟩ := asm_neg_val
        have h_sign_extend : forall x y, U32.toBV #v[x, y, 0#8, 0#8] - U32.toBV #v[0#8, 0#8, 1#8, 0#8] = U32.toBV #v[x, y, 255, 255]
        := by
          clear *-; intro x y
          simp [U32.toBV, -List.getElem_cons_succ]
          repeat rw [List.getElem_cons_succ]
          repeat rw [List.getElem_cons_zero]
          simp
          bv_check "MemoryReadWriteAir.lean-sign_extend_sub_double.lrat"
        rw [h_sign_extend] at asm_neg_val
        apply U32.toBV_inj at asm_neg_val
        simp at asm_neg_val; simp [asm_neg_val]
        simp [U32.toBV, -List.getElem_cons_succ]
        repeat rw [List.getElem_cons_succ]
        repeat rw [List.getElem_cons_zero]
        simp [BitVec.extend, BitVec.signExtend_eq_append_extractLsb']
        rw [if_pos]
        . rw [BitVec.append_assoc]; simp
          rw [BitVec.append_eq_append_eql]; simp
          grind
        . rw [BitVec.msb_append]; simp [BitVec.msb_eq_decide]
          omega

  lemma spec_LHU
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 14)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
    obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
             h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
             h_off_aligned_addr,
             h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
             h_off_b_b3_decomp,
             u1, u2, u3, h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3, h_constraints ⟩ := h_constraints
    clear u0 u1 u2 u3
    simp [bus_row, *] at asm_state
    obtain ⟨ ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := asm_state
    simp [h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3] at h_constraints
    clear h_eq_mav0 h_eq_mav1 h_eq_mav2 h_eq_mav3
    obtain ⟨ h_offset_characterisation,
             h_eq_uval0, h_eq_uval1, h_eq_uval2, h_eq_uval3,
             h_b_msb_d0, h_b_msb_d1, h_b_msb_d2, h_b_msb_d3, h_b_msb_d4, h_b_msb_d5, h_b_msb_d6, h_b_msb_d7,
             h_op_a_0, h_eq_neg, h_eq_pos,
             h_eq_pos0, h_eq_pos1, h_eq_pos2, h_eq_pos3,
             h_constraints ⟩ := h_constraints
    clear h_constraints
    obtain ⟨ ub_uval0, ub_uval1 ⟩ : air.cols.unsigned_mem_val_0 row 0 < 256 ∧ air.cols.unsigned_mem_val_1 row 0 < 256
    := by
      clear *- h_eq_uval0 h_eq_uval1 h_off_b_o1 h_off_b_o2 h_off_b_o3
               h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
               ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
      grind
    split_ands
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      clear *- ub_uval0 ub_uval1 h_eq_uval2 h_eq_uval3
      omega
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      simp [← BitVec.toNat_inj, U32.toNat, BitVec.extend]
      rw [BitVec.toNat_append]; simp
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
      rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
      simp [Nat.shiftLeft_eq_mul_pow]
      omega

  lemma spec_LW
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 12)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
    obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
             h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
             h_off_aligned_addr,
             h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
             h_off_b_b3_decomp,
             u1, u2, u3, h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3, h_constraints ⟩ := h_constraints
    clear u0 u1 u2 u3
    simp [bus_row, *] at asm_state
    obtain ⟨ ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := asm_state
    simp [h_eq_mav0, h_eq_mav1, h_eq_mav2, h_eq_mav3] at h_constraints
    clear h_eq_mav0 h_eq_mav1 h_eq_mav2 h_eq_mav3
    obtain ⟨ h_offset_characterisation,
             h_eq_uval0, h_eq_uval1, h_eq_uval2, h_eq_uval3,
             h_b_msb_d0, h_b_msb_d1, h_b_msb_d2, h_b_msb_d3, h_b_msb_d4, h_b_msb_d5, h_b_msb_d6, h_b_msb_d7,
             h_op_a_0, h_eq_neg, h_eq_pos,
             h_eq_pos0, h_eq_pos1, h_eq_pos2, h_eq_pos3,
             h_constraints ⟩ := h_constraints
    clear h_constraints
    split_ands
    . intro h_not_x0; clear h_op_a_0
      simp [h_not_x0] at h_eq_neg h_eq_pos
      simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      omega
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega

  lemma spec_SB
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 15)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    simp [← BitVec.toNat_inj] at asm_addr
    clear *- ub_addr asm_addr
    omega

  lemma spec_SH
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 16)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    simp [← BitVec.toNat_inj] at asm_addr
    clear *- ub_addr asm_addr
    omega

  lemma spec_SW
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 16)
    (h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
             air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
             air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec
      (air.cols.instruction.opcode row 0)
      (air.cols.instruction.op_a_access.access.value_0 row 0)
      (air.cols.instruction.op_a_access.access.value_1 row 0)
      (air.cols.instruction.op_a_access.access.value_2 row 0)
      (air.cols.instruction.op_a_access.access.value_3 row 0)
      (air.cols.instruction.op_b_access.value_0 row 0)
      (air.cols.instruction.op_b_access.value_1 row 0)
      (air.cols.instruction.op_b_access.value_2 row 0)
      (air.cols.instruction.op_b_access.value_3 row 0)
      (air.cols.instruction.op_c_access.value_0 row 0)
      (air.cols.instruction.op_c_access.value_1 row 0)
      (air.cols.instruction.op_c_access.value_2 row 0)
      (air.cols.instruction.op_c_access.value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
      (air.cols.instruction.is_lb row 0)
      (air.cols.instruction.is_lbu row 0)
      (air.cols.instruction.is_lh row 0)
      (air.cols.instruction.is_lhu row 0)
      (air.cols.instruction.is_lw row 0)
      (air.cols.instruction.is_sb row 0)
      (air.cols.instruction.is_sh row 0)
      (air.cols.instruction.is_sw row 0)
  := by
    simp [bus_row_ext_asm, bus_row, h_opcode, h_mul] at h_ext
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
             eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := h_ext
    clear h_mul
    -- Process goal
    simp [MemoryBus.Spec, *]
    -- Process assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_mem
    -- ALU assumptions
    simp [bus_row, *] at asm_alu
    obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
    simp [ALUBus.Spec, *] at asm_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
    -- Unfurl constraints
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      eq_lw, eq_sb, eq_sh, eq_sw,
    ] at h_constraints
    replace h_constraints := h_constraints.2
    -- Proof
    obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
             h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7,
             h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
             h_awrc_all, h_awrc_def,
             h_constraints ⟩ := h_constraints
    have ub_addr : U32.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    simp [← BitVec.toNat_inj] at asm_addr
    clear *- ub_addr asm_addr
    omega

#exit

      -- have h_eq_addr_offset : air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0 = air.cols.addr_offset row 0
      -- := by
      --   clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
      --           h_off_aligned_addr h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
      --   grind
      -- rw [h_eq_addr_offset] at h_off_b_b3_decomp
      -- have ub_addr_offset : air.cols.addr_offset row 0 < 4
      -- := by
      --   clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_eq_addr_offset
      --   grind
      -- have h_offset_diff_nonneg : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
      -- := by
      --   clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
      --           ub_addr_offset
      --   grind
      -- clear h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3 h_eq_addr_offset
      -- have h_div_four_aw0 : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
      -- := by
      --   clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
      --           h_off_b_b3_decomp ub_addr_offset h_offset_diff_nonneg
      --   grind
      -- clear h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
      -- have h_eq_mod_aw0 : (air.cols.addr_offset row 0).val = (air.cols.addr_word_0 row 0).val % 4
      -- := by
      --   clear *- h_offset_diff_nonneg ub_aw0 ub_addr_offset h_div_four_aw0
      --   omega
      -- have h_div_four : 4 ∣ (air.cols.addr_aligned row 0).val
      -- := by
      --   clear *- ub_aw0 ub_aw1 ub_aw2 ub_aw3 ub_addr
      --           h_off_aligned_addr h_eq_mod_aw0 ub_addr_offset
      --   simp [U32.toNat] at ub_addr
      --   repeat rw [Nat.mod_eq_of_lt (by omega)] at ub_addr
      --   grind
      -- clear h_div_four_aw0 ub_addr_offset

end AddSubAir.Spec
