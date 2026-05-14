import PicoFV.RV32IM.Constraints.MemoryReadWriteAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace MemoryReadWriteAir.Spec

  open RV32IM_Interactions
  open MemoryReadWriteAir.ConstraintsAndBuses
  open MemoryReadWriteAir.Interactions

  set_option maxHeartbeats 1_000_000_000

  -- ===================================
  -- LB (Load Byte, signed) -- opcode 10
  -- ===================================

  lemma spec_LB
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 10)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
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
    clear h_constraints h_op_a_0
    obtain ⟨ ub_uval0, h_d7_eq_msb_uval0 ⟩ :
      air.cols.unsigned_mem_val_0 row 0 < 256 ∧
      (air.cols.unsigned_mem_val_0 row 0 < 128 ↔ air.cols.msb_decomp_7 row 0 = 0)
    := by
      clear *- h_b_msb_d0 h_b_msb_d1 h_b_msb_d2 h_b_msb_d3
                h_b_msb_d4 h_b_msb_d5 h_b_msb_d6 h_b_msb_d7 h_msb_decomp
      split_ands
      . grind
      . constructor <;> grind
    constructor
    . obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
        simp [h_eq_neg] at asm_neg_val
        simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        clear *- ub_uval0 h_eq_uval1 h_eq_uval2 h_eq_uval3
        omega
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
        simp [h_eq_neg, ALUBus.Spec] at asm_neg_val
        clear *- asm_neg_val; omega
    . constructor
      . simp [← BitVec.toNat_inj] at asm_addr
        clear *- ub_addr asm_addr
        omega
      . obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
        . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
          simp [h_eq_neg] at asm_neg_val
          simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
          simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
          simp [← BitVec.toInt_inj, BitVec.extend]; unfold U32b.toInt
          simp [U32b.negative, U32b.toNat, BitVec.toInt_signExtend_of_le]
          simp [BitVec.toInt]
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval0 h_eq_neg h_eq_pos
          clear h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
          simp [h_eq_neg, ALUBus.Spec] at asm_neg_val
          obtain ⟨ ub_av, ub_umv, asm_neg_val⟩ := asm_neg_val
          simp [h_eq_uval1, h_eq_uval2, h_eq_uval3] at asm_neg_val
          have h_sign_extend : forall x, U32b.toBV #v[x, 0#8, 0#8, 0#8] - U32b.toBV #v[0#8, 1#8, 0#8, 0#8] = U32b.toBV #v[x, 255, 255, 255]
          := by
            clear *-; intro x
            simp [U32b.toBV, -List.getElem_cons_succ]
            repeat rw [List.getElem_cons_succ]
            repeat rw [List.getElem_cons_zero]
            simp
            bv_check "MemoryReadWriteAir.lean-sign_extend_sub_single.lrat"
          rw [h_sign_extend] at asm_neg_val
          apply U32b.toBV_inj at asm_neg_val
          simp at asm_neg_val; simp [asm_neg_val]
          simp [U32b.toBV, -List.getElem_cons_succ]
          repeat rw [List.getElem_cons_succ]
          repeat rw [List.getElem_cons_zero]
          simp [BitVec.extend, BitVec.signExtend_eq_append_extractLsb']
          rw [if_pos]
          . grind
          . simp [BitVec.msb_eq_decide]
            omega

  -- ======================================
  -- LBU (Load Byte, unsigned) -- opcode 13
  -- ======================================

  lemma spec_LBU
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 13)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
    := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
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
    clear h_constraints h_op_a_0
    obtain ub_uval0 : air.cols.unsigned_mem_val_0 row 0 < 256
    := by
      clear *- h_eq_uval0 h_off_b_o1 h_off_b_o2 h_off_b_o3
               h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
               ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
      grind
    constructor
    . simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      clear *- ub_uval0 h_eq_uval1 h_eq_uval2 h_eq_uval3
      omega
    . constructor
      . simp [← BitVec.toNat_inj] at asm_addr
        clear *- ub_addr asm_addr
        omega
      . simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        simp [← BitVec.toNat_inj, U32b.toNat, BitVec.extend]
        omega

  -- ========================================
  -- LH (Load Half-word, signed) -- opcode 11
  -- ========================================

  lemma spec_LH
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 11)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
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
    clear h_constraints h_op_a_0
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
    constructor
    . obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval1 h_eq_neg h_eq_pos
        simp [h_eq_neg] at asm_neg_val
        simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
        simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
        clear *- ub_uval0 ub_uval1 h_eq_uval2 h_eq_uval3
        omega
      . simp [h_b_msb_d7] at h_msb_decomp h_d7_eq_msb_uval1 h_eq_neg h_eq_pos
        simp [h_eq_neg, ALUBus.Spec] at asm_neg_val
        clear *- asm_neg_val; omega
    . constructor
      . simp [← BitVec.toNat_inj] at asm_addr
        clear *- ub_addr asm_addr
        omega
      . constructor
        . simp [← BitVec.toNat_inj] at asm_addr
          rw [← asm_addr]; clear asm_addr
          suffices h_align : 2 ∣ (air.cols.addr_word_0 row 0).val
          . simp [U32b.toNat]; clear *- ub_aw0 ub_aw1 ub_aw2 ub_aw3 h_align; omega
          . have h_eq_addr_offset : air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0 = air.cols.addr_offset row 0
            := by
              clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                      h_off_aligned_addr h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
              grind
            rw [h_eq_addr_offset] at h_off_b_b3_decomp
            have ub_addr_offset : air.cols.addr_offset row 0 < 4
            := by
              clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_eq_addr_offset
              grind
            have h_offset_diff_nonneg : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
            := by
              clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
                      ub_addr_offset
              grind
            have h_div_four_aw0 : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
            := by
              clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                      h_off_b_b3_decomp ub_addr_offset h_offset_diff_nonneg
              grind
            have h_eq_mod_aw0 : (air.cols.addr_offset row 0).val = (air.cols.addr_word_0 row 0).val % 4
            := by
              clear *- h_offset_diff_nonneg ub_aw0 ub_addr_offset h_div_four_aw0
              omega
            clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3
                    h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                    ub_addr_offset h_offset_diff_nonneg h_div_four_aw0
                    h_off_aligned_addr h_offset_characterisation
            obtain h_off_b_o1 | h_off_b_o1 := h_off_b_o1
            . obtain h_off_b_o3 | h_off_b_o3 := h_off_b_o3
              . simp_all; grind
              . exfalso; grind
            . exfalso; grind
        . obtain h_b_msb_d7 | h_b_msb_d7 := h_b_msb_d7
          . simp [h_b_msb_d7] at h_eq_neg h_eq_pos
            simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
            simp [h_eq_uval2, h_eq_uval3] at h_eq_pos1 h_eq_pos2 h_eq_pos3
            simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
            simp [← BitVec.toInt_inj, BitVec.extend]; unfold U32b.toInt
            simp [U32b.negative, U32b.toNat, BitVec.toInt_signExtend_of_le]
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
            have h_sign_extend : forall x y, U32b.toBV #v[x, y, 0#8, 0#8] - U32b.toBV #v[0#8, 0#8, 1#8, 0#8] = U32b.toBV #v[x, y, 255, 255]
            := by
              clear *-; intro x y
              simp [U32b.toBV, -List.getElem_cons_succ]
              repeat rw [List.getElem_cons_succ]
              repeat rw [List.getElem_cons_zero]
              simp
              bv_check "MemoryReadWriteAir.lean-sign_extend_sub_double.lrat"
            rw [h_sign_extend] at asm_neg_val
            apply U32b.toBV_inj at asm_neg_val
            simp at asm_neg_val; simp [asm_neg_val]
            simp [U32b.toBV, -List.getElem_cons_succ]
            repeat rw [List.getElem_cons_succ]
            repeat rw [List.getElem_cons_zero]
            simp [BitVec.extend, BitVec.signExtend_eq_append_extractLsb']
            rw [if_pos]
            . rw [BitVec.append_assoc]; simp
              rw [BitVec.append_eq_append_eql]; simp
              grind
            . rw [BitVec.msb_append]; simp [BitVec.msb_eq_decide]
              omega

  -- ===========================================
  -- LHU (Load Half-word, unsigned) -- opcode 14
  -- ===========================================

  lemma spec_LHU
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 14)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
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
    clear h_constraints h_op_a_0
    obtain ⟨ ub_uval0, ub_uval1 ⟩ : air.cols.unsigned_mem_val_0 row 0 < 256 ∧ air.cols.unsigned_mem_val_1 row 0 < 256
    := by
      clear *- h_eq_uval0 h_eq_uval1 h_off_b_o1 h_off_b_o2 h_off_b_o3
               h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
               ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3
      grind
    constructor
    . simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      clear *- ub_uval0 ub_uval1 h_eq_uval2 h_eq_uval3
      omega
    . constructor
      . simp [← BitVec.toNat_inj] at asm_addr
        clear *- ub_addr asm_addr
        omega
      . constructor
        . simp [← BitVec.toNat_inj] at asm_addr
          rw [← asm_addr]; clear asm_addr
          suffices h_align : 2 ∣ (air.cols.addr_word_0 row 0).val
          . simp [U32b.toNat]; clear *- ub_aw0 ub_aw1 ub_aw2 ub_aw3 h_align; omega
          . have h_eq_addr_offset : air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0 = air.cols.addr_offset row 0
            := by
              clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                      h_off_aligned_addr h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
              grind
            rw [h_eq_addr_offset] at h_off_b_b3_decomp
            have ub_addr_offset : air.cols.addr_offset row 0 < 4
            := by
              clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_eq_addr_offset
              grind
            have h_offset_diff_nonneg : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
            := by
              clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
                      ub_addr_offset
              grind
            have h_div_four_aw0 : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
            := by
              clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                      h_off_b_b3_decomp ub_addr_offset h_offset_diff_nonneg
              grind
            have h_eq_mod_aw0 : (air.cols.addr_offset row 0).val = (air.cols.addr_word_0 row 0).val % 4
            := by
              clear *- h_offset_diff_nonneg ub_aw0 ub_addr_offset h_div_four_aw0
              omega
            clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3
                    h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                    ub_addr_offset h_offset_diff_nonneg h_div_four_aw0
                    h_off_aligned_addr h_offset_characterisation
            obtain h_off_b_o1 | h_off_b_o1 := h_off_b_o1
            . obtain h_off_b_o3 | h_off_b_o3 := h_off_b_o3
              . simp_all; grind
              . exfalso; grind
            . exfalso; grind
        . simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
          simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
          simp [← BitVec.toNat_inj, U32b.toNat, BitVec.extend]
          rw [BitVec.toNat_append]; simp
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
          rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
          simp [Nat.shiftLeft_eq_mul_pow]
          omega

  -- ===========================
  -- LW (Load Word) -- opcode 12
  -- ===========================

  lemma spec_LW
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 12)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
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
    clear h_constraints h_op_a_0
    constructor
    . simp [h_eq_pos] at h_eq_pos0 h_eq_pos1 h_eq_pos2 h_eq_pos3
      simp [← h_eq_pos0, ← h_eq_pos1, ← h_eq_pos2, ← h_eq_pos3]
      omega
    . constructor
      . simp [← BitVec.toNat_inj] at asm_addr
        clear *- ub_addr asm_addr
        omega
      . simp [← BitVec.toNat_inj] at asm_addr
        rw [← asm_addr]; clear asm_addr
        suffices h_align : 4 ∣ (air.cols.addr_word_0 row 0).val
        . simp [U32b.toNat]; clear *- ub_aw0 ub_aw1 ub_aw2 ub_aw3 h_align; omega
        . have h_eq_addr_offset : air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0 = air.cols.addr_offset row 0
          := by
            clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                    h_off_aligned_addr h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
            grind
          rw [h_eq_addr_offset] at h_off_b_b3_decomp
          have ub_addr_offset : air.cols.addr_offset row 0 < 4
          := by
            clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_eq_addr_offset
            grind
          have h_offset_diff_nonneg : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
          := by
            clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
                    ub_addr_offset
            grind
          have h_div_four_aw0 : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
          := by
            clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                    h_off_b_b3_decomp ub_addr_offset h_offset_diff_nonneg
            grind
          have h_eq_mod_aw0 : (air.cols.addr_offset row 0).val = (air.cols.addr_word_0 row 0).val % 4
          := by
            clear *- h_offset_diff_nonneg ub_aw0 ub_addr_offset h_div_four_aw0
            omega
          clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3
                  h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                  ub_addr_offset h_offset_diff_nonneg h_div_four_aw0
                  h_off_aligned_addr h_offset_characterisation
          obtain h_off_b_o1 | h_off_b_o1 := h_off_b_o1
          . obtain h_off_b_o2 | h_off_b_o2 := h_off_b_o2
            . obtain h_off_b_o3 | h_off_b_o3 := h_off_b_o3
              . simp_all
              . exfalso; grind
            . exfalso; grind
          . exfalso; grind

  -- ============================
  -- SB (Store Byte) -- opcode 15
  -- ============================

  lemma spec_SB
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 15)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    simp [← BitVec.toNat_inj] at asm_addr
    clear *- ub_addr asm_addr
    omega

  -- =================================
  -- SH (Store Half-word) -- opcode 16
  -- =================================

  lemma spec_SH
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 16)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    split_ands
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega
    . clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
      obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
               h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
               h_off_aligned_addr,
               h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
               h_off_b_b3_decomp,
               h_constraints ⟩ := h_constraints
      have h_offset_characterisation : air.cols.offset_is_one row 0 + air.cols.offset_is_three row 0 = 0 := by aesop
      clear h_constraints
      simp [← BitVec.toNat_inj] at asm_addr
      rw [← asm_addr]; clear asm_addr
      suffices h_align : 2 ∣ (air.cols.addr_word_0 row 0).val
      . simp [U32b.toNat]; clear *- ub_aw0 ub_aw1 ub_aw2 ub_aw3 h_align; omega
      . have h_eq_addr_offset : air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0 = air.cols.addr_offset row 0
        := by
          clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                   h_off_aligned_addr h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
          grind
        rw [h_eq_addr_offset] at h_off_b_b3_decomp
        have ub_addr_offset : air.cols.addr_offset row 0 < 4
        := by
          clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_eq_addr_offset
          grind
        have h_offset_diff_nonneg : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
        := by
          clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
                  ub_addr_offset
          grind
        have h_div_four_aw0 : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
        := by
          clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                  h_off_b_b3_decomp ub_addr_offset h_offset_diff_nonneg
          grind
        have h_eq_mod_aw0 : (air.cols.addr_offset row 0).val = (air.cols.addr_word_0 row 0).val % 4
        := by
          clear *- h_offset_diff_nonneg ub_aw0 ub_addr_offset h_div_four_aw0
          omega
        clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3
                 h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                 ub_addr_offset h_offset_diff_nonneg h_div_four_aw0
                 h_off_aligned_addr h_offset_characterisation
        obtain h_off_b_o1 | h_off_b_o1 := h_off_b_o1
        . obtain h_off_b_o3 | h_off_b_o3 := h_off_b_o3
          . simp_all; grind
          . exfalso; grind
        . exfalso; grind

  -- ============================
  -- SW (Store Word) -- opcode 17
  -- ============================

  lemma spec_SW
    [Field ExtF]
    (air : Valid_MemoryReadWriteAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row ))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
    (h_opcode : air.cols.instruction.opcode row 0 = 17)
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
  := by
    have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                 air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                 air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
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
    have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
    := by
      clear h_constraints
      simp [U32b.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    split_ands
    . simp [← BitVec.toNat_inj] at asm_addr
      clear *- ub_addr asm_addr
      omega
    . clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
          h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7
          h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
          h_awrc_all h_awrc_def
      obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
               h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
               h_off_aligned_addr,
               h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
               h_off_b_b3_decomp,
               h_constraints ⟩ := h_constraints
      have h_offset_characterisation : 1 - air.cols.offset_is_one row 0 - air.cols.offset_is_two row 0 - air.cols.offset_is_three row 0 = 1 := by clear *- h_constraints; grind
      clear h_constraints
      simp [← BitVec.toNat_inj] at asm_addr
      rw [← asm_addr]; clear asm_addr
      suffices h_align : 4 ∣ (air.cols.addr_word_0 row 0).val
      . simp [U32b.toNat]; clear *- ub_aw0 ub_aw1 ub_aw2 ub_aw3 h_align; omega
      . have h_eq_addr_offset : air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0 = air.cols.addr_offset row 0
        := by
          clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                   h_off_aligned_addr h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
          grind
        rw [h_eq_addr_offset] at h_off_b_b3_decomp
        have ub_addr_offset : air.cols.addr_offset row 0 < 4
        := by
          clear *- h_off_eq_o0 h_off_b_o1 h_off_b_o2 h_off_b_o3 h_eq_addr_offset
          grind
        have h_offset_diff_nonneg : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
        := by
          clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35 h_off_b_b3_decomp
                  ub_addr_offset
          grind
        have h_div_four_aw0 : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
        := by
          clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                  h_off_b_b3_decomp ub_addr_offset h_offset_diff_nonneg
          grind
        have h_eq_mod_aw0 : (air.cols.addr_offset row 0).val = (air.cols.addr_word_0 row 0).val % 4
        := by
          clear *- h_offset_diff_nonneg ub_aw0 ub_addr_offset h_div_four_aw0
          omega
        clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3
                 h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
                 ub_addr_offset h_offset_diff_nonneg h_div_four_aw0
                 h_off_aligned_addr h_offset_characterisation
        obtain h_off_b_o1 | h_off_b_o1 := h_off_b_o1
        . obtain h_off_b_o2 | h_off_b_o2 := h_off_b_o2
          . obtain h_off_b_o3 | h_off_b_o3 := h_off_b_o3
            . simp_all
            . exfalso; grind
          . exfalso; grind
        . exfalso; grind

  namespace ExtHashMap

    lemma insert_eq_self [BEq K] [LawfulBEq K] [Hashable K]
      (m : Std.ExtHashMap K V)
      (h : m.get? k = .some v)
    :
      m.insert k v = m
    := by
      grind

    lemma insert_comm [BEq K] [LawfulBEq K] [Hashable K]
      (m : Std.ExtHashMap K V)
      (h_neq : ¬ K₁ = K₂)
    :
      (m.insert K₁ V₁).insert K₂ V₂ = (m.insert K₂ V₂).insert K₁ V₁
    := by
      grind

  end ExtHashMap

  section BusEquivalence

    lemma bus_equiv
      [Field ExtF]
      (air : Valid_MemoryReadWriteAir FKB ExtF)
      (row : ℕ)
      (h_ext : bus_row_ext_asm (bus_row air row ))
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_constraints : MemoryReadWriteAir.Extraction.allHold air row)
      -- FIXME:
      -- This assumption needs to be made by the circuit
      (ASSUMPTION : ¬ (air.cols.addr_aligned row 0 < 32))
    :
      let memory_row := { (bus_row air row).Memory[0]! with multiplicity := -1 }
      let memory_bus : BusRow := {
        Program := [], ALU := [], Byte := [], State := [], Memory := [ memory_row ]
      }
      let state_bus : BusRow := {
        Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := []
      }
      (RV32IM.operation_list_effect (RV32IM.bus_operations state_bus) state).hypotheses →
        (RV32IM.operation_list_effect (RV32IM.bus_operations memory_bus) state).hypotheses ∧
        (RV32IM.operation_list_effect (RV32IM.bus_operations memory_bus) state).state =
          (RV32IM.operation_list_effect (RV32IM.bus_operations state_bus) state).state
    := by
      have h_mul : air.cols.instruction.is_lb row 0 + air.cols.instruction.is_lbu row 0 + air.cols.instruction.is_lh row 0 +
                   air.cols.instruction.is_lhu row 0 + air.cols.instruction.is_lw row 0 + air.cols.instruction.is_sb row 0 +
                   air.cols.instruction.is_sh row 0 + air.cols.instruction.is_sw row 0 = 1
      := by unfold Valid_MemoryChipCols.is_real at h_is_real; omega
      -- Process assumptions
      simp [bus_row_wf_asm] at h_wf
      obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
      clear asm_prog asm_byte asm_mem
      -- State assumptions
      simp [bus_row, *] at asm_state
      obtain ⟨ ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := asm_state
      -- ALU assumptions
      simp [bus_row, *] at asm_alu
      obtain ⟨ asm_addr, asm_neg_val ⟩ := asm_alu
      simp [ALUBus.Spec, *] at asm_addr
      obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, asm_addr ⟩ := asm_addr
      -- Constraints
      simp [
        pico_encapsulation,
        constraint_and_interaction_simplification,
        sub_eq_zero,
        h_is_real
      ] at h_constraints
      obtain ⟨ h_awrc_msbd_0, h_awrc_msbd_1, h_awrc_msbd_2, h_awrc_msbd_3,
               h_awrc_msbd_4, h_awrc_msbd_5, h_awrc_msbd_6, h_awrc_msbd_7, h_awrc_eq_msbd7_zero,
               h_awrc_decomp, h_eq_awrc_msbd_7, h_awrc_eq_upper, h_awrc_b_upper,
               h_awrc_all, h_awrc_def,
               h_constraints ⟩ := h_constraints
      have ub_addr : U32b.toNat #v[air.cols.addr_word_0 row 0, air.cols.addr_word_1 row 0, air.cols.addr_word_2 row 0, air.cols.addr_word_3 row 0] < KB_prime
      := by
        clear h_mul h_constraints asm_addr asm_neg_val
        simp [U32b.toNat]
        repeat rw [Nat.mod_eq_of_lt (by omega)]
        grind
      clear h_awrc_msbd_0 h_awrc_msbd_1 h_awrc_msbd_2 h_awrc_msbd_3
            h_awrc_msbd_4 h_awrc_msbd_5 h_awrc_msbd_6 h_awrc_msbd_7 h_awrc_eq_msbd7_zero
            h_awrc_decomp h_eq_awrc_msbd_7 h_awrc_eq_upper h_awrc_b_upper
            h_awrc_all h_awrc_def
      obtain ⟨ h_off_b_o1, h_off_b_o2, h_off_b_o3, u0,
               h_off_eq_o0, h_off_eq_o1, h_off_eq_o2, h_off_eq_o3,
               h_off_aligned_addr,
               h_off_b_b30, h_off_b_b31, h_off_b_b32, h_off_b_b33, h_off_b_b34, h_off_b_b35,
               h_off_b_b3_decomp,
               u1, u2, u3, h_eqp_mav0, h_eqp_mav1, h_eqp_mav2, h_eqp_mav3, h_constraints ⟩ := h_constraints
      clear u0 u1 u2 u3
      obtain ⟨ h_eq_mv0_lb, h_eq_mv1_lb, h_eq_mv2_lb, h_eq_mv3_lb,
               h_offset_char_lh, h_offset_char_lw,
               h_eq_mv0_lh, h_eq_mv1_lh, h_eq_mv2_lh, h_eq_mv3_lh,
               h_eq_mv0_lw, h_eq_mv1_lw, h_eq_mv2_lw, h_eq_mv3_lw,
               h_msb_d0, h_msb_d1, h_msb_d2, h_msb_d3, h_msb_d4, h_msb_d5, h_msb_d6, h_msb_d7,
               h_lb_decomp_high, h_lh_decomp_high, h_constraints ⟩ := h_constraints
      obtain ⟨ h_b_a_is_0, h_if_neg_eq, h_if_pos_eq, h_pos_eq0, h_pos_eq1, h_pos_eq2, h_pos_eq3,
               h_constraints ⟩ := h_constraints
      obtain ⟨ u0, u1, u2, u3, u4, u5, u6, u7, h_constraints ⟩ := h_constraints
      clear u0 u1 u2 u3 u4 u5 u6 u7
      obtain ⟨ h_sb_mav0, h_sb_mav1, h_sb_mav2, h_sb_mav3, h_offset_char_sh, h_offset_char_sw,
               h_sh_mav0, h_sh_mav1, h_sh_mav2, h_sh_mav3,
               h_sw_mav0, h_sw_mav1, h_sw_mav2, h_sw_mav3 ⟩ := h_constraints
      -- Externals
      simp [bus_row_ext_asm, bus_row, h_mul] at h_ext
      obtain ⟨ opcode_range, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
               op_lb, op_lh, op_lw, op_lbu, op_lhu, op_sb, op_sh, op_sw ⟩ := h_ext
      -- Further adjustments
      have eq_offset : air.cols.addr_offset row 0 = air.cols.offset_is_one row 0 + 2 * air.cols.offset_is_two row 0 + 3 * air.cols.offset_is_three row 0
      := by
        clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
        omega
      rw [← eq_offset] at h_off_b_b3_decomp
      have ub_offset : air.cols.addr_offset row 0 < 4
      := by
        clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3 h_off_eq_o0 h_off_eq_o1 h_off_eq_o2 h_off_eq_o3
        grind
      have h_aw0_le_offset : air.cols.addr_offset row 0 ≤ air.cols.addr_word_0 row 0
      := by
        clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                 h_off_b_b3_decomp ub_aw0 ub_offset
        grind
      have h_div_4_aw0_diff : 4 ∣ (air.cols.addr_word_0 row 0).val - (air.cols.addr_offset row 0).val
      := by
        clear *- h_off_b_b30 h_off_b_b31 h_off_b_b32 h_off_b_b33 h_off_b_b34 h_off_b_b35
                 h_off_b_b3_decomp h_aw0_le_offset
        simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at h_off_b_b3_decomp
        rw [Fin.sub_val_of_le (by omega)] at h_off_b_b3_decomp
        rw [h_off_b_b3_decomp]; clear h_off_b_b3_decomp
        omega
      simp [U32b.toNat] at ub_addr
      repeat rw [Nat.mod_eq_of_lt (by omega)] at ub_addr
      rw [← eq_sub_iff_add_eq] at h_off_aligned_addr
      simp [Fin.ext_iff] at h_off_aligned_addr
      rw [Fin.sub_val_of_le
          (by
            clear *- h_aw0_le_offset ub_aw0 ub_aw1 ub_aw2 ub_aw3 ub_addr
            grind
          )] at h_off_aligned_addr
      simp [Fin.val_add, Fin.val_mul] at h_off_aligned_addr
      rw [Nat.mod_eq_of_lt (by omega)] at h_off_aligned_addr
      symm at h_off_aligned_addr; rw [Nat.sub_eq_iff_eq_add (by omega)] at h_off_aligned_addr
      rw [eq_comm (a := air.cols.unsigned_mem_val_0 row 0)] at h_pos_eq0
      rw [eq_comm (a := air.cols.unsigned_mem_val_1 row 0)] at h_pos_eq1
      rw [eq_comm (a := air.cols.unsigned_mem_val_2 row 0)] at h_pos_eq2
      rw [eq_comm (a := air.cols.unsigned_mem_val_3 row 0)] at h_pos_eq3
      -- LB
      by_cases h_eq_lb : air.cols.instruction.opcode row 0 = 10
      . simp [h_eq_lb] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
        obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_lb
        simp_all
        simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
        simp [List.filterMap_cons, List.filterMap_nil]
        have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
        simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
        repeat rw [BitVec.extractLsb'_append_eq_ite]
        simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
        simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
        simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
        rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
        rw [h_off_aligned_addr]
        have ub_umv : (air.cols.unsigned_mem_val_0 row 0).val < 256
        := by
          clear *- h_msb_d0 h_msb_d1 h_msb_d2 h_msb_d3 h_msb_d4 h_msb_d5 h_msb_d6 h_msb_d7 h_lb_decomp_high
          grind
        split_ands
        . clear h_div_4_aw0_diff h_pos_eq1 h_pos_eq2 h_pos_eq3
          rw [← eq_offset]
          by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
          . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
            simp [ALUBus.Spec] at asm_neg_val
            obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
            simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
            repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at asm_neg_val
            rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
            congr; omega
          . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
            . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
              simp [ALUBus.Spec] at asm_neg_val
              obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
              simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
              repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at asm_neg_val
              rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
              congr; omega
            . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1
              . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
                simp [ALUBus.Spec] at asm_neg_val
                obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
                simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
                repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at asm_neg_val
                rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
                congr; omega
              . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
                simp [ALUBus.Spec] at asm_neg_val
                obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
                simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
                repeat rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
                congr; omega
        . clear *- h_mem_0 h_mem_1 h_mem_2 h_mem_3 h_eqp_mav0 h_eqp_mav1 h_eqp_mav2 h_eqp_mav3
          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by assumption)]
          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by assumption)]
      -- LBU
      . by_cases h_eq_lbu : air.cols.instruction.opcode row 0 = 13
        . simp [h_eq_lbu] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
          obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_lbu
          simp_all
          simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
          simp [List.filterMap_cons, List.filterMap_nil]
          have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
          simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
          repeat rw [BitVec.extractLsb'_append_eq_ite]
          simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
          simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
          simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
          rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
          rw [h_off_aligned_addr]
          split_ands
          . clear h_div_4_aw0_diff h_pos_eq1 h_pos_eq2 h_pos_eq3
            rw [← eq_offset]
            by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
            . simp_all
            . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
              . simp_all
              . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1 <;> simp_all
          . clear *- h_mem_0 h_mem_1 h_mem_2 h_mem_3 h_eqp_mav0 h_eqp_mav1 h_eqp_mav2 h_eqp_mav3
            rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
            rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
            rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by assumption)]
            rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by assumption)]
        -- LH
        . by_cases h_eq_lh : air.cols.instruction.opcode row 0 = 11
          . simp [h_eq_lh] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
            obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_lh
            simp_all
            simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
            simp [List.filterMap_cons, List.filterMap_nil]
            have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
            simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
            repeat rw [BitVec.extractLsb'_append_eq_ite]
            simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
            simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
            simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
            rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
            rw [h_off_aligned_addr]
            have ub_umv0 : (air.cols.unsigned_mem_val_0 row 0).val < 256
            := by
              clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3 ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3 h_off_eq_o0 h_eq_mv0_lh
              grind
            have ub_umv1 : (air.cols.unsigned_mem_val_1 row 0).val < 256
            := by
              clear *- h_off_b_o1 h_off_b_o2 h_off_b_o3 ub_mpv0 ub_mpv1 ub_mpv2 ub_mpv3 h_off_eq_o0 h_eq_mv1_lh
              grind
            split_ands
            . clear h_div_4_aw0_diff h_pos_eq1 h_pos_eq2 h_pos_eq3
              rw [← eq_offset]
              by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
              . simp_all
              . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
                . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
                  simp [ALUBus.Spec] at asm_neg_val
                  obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
                  simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
                  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at asm_neg_val
                  rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
                  congr; omega
                . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1
                  . simp_all
                  . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
                    simp [ALUBus.Spec] at asm_neg_val
                    obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
                    simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
                    repeat rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
                    congr; omega
            . clear h_div_4_aw0_diff h_pos_eq2 h_pos_eq3
              rw [← eq_offset]
              by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
              . simp_all
              . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
                . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
                  simp [ALUBus.Spec] at asm_neg_val
                  obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
                  simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
                  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at asm_neg_val
                  rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
                  congr; omega
                . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1
                  . simp_all
                  . obtain h_msb_d7 | h_msb_d7 := h_msb_d7 <;> simp_all
                    simp [ALUBus.Spec] at asm_neg_val
                    obtain ⟨ ⟨ ub_a0, ub_a1, ub_a2, ub_a3 ⟩, asm_neg_val ⟩ := asm_neg_val
                    simp [← BitVec.toNat_inj, U32b.toNat] at asm_neg_val
                    repeat rw [Nat.mod_eq_of_lt (by omega)] at asm_neg_val
                    congr; omega
            . clear *- h_mem_0 h_mem_1 h_mem_2 h_mem_3 h_eqp_mav0 h_eqp_mav1 h_eqp_mav2 h_eqp_mav3
              rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
              rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
              rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by assumption)]
              rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by assumption)]
          -- LHU
          . by_cases h_eq_lhu : air.cols.instruction.opcode row 0 = 14
            . simp [h_eq_lhu] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
              obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_lhu
              simp_all
              simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
              simp [List.filterMap_cons, List.filterMap_nil]
              have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
              simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
              repeat rw [BitVec.extractLsb'_append_eq_ite]
              simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
              simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
              simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
              rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
              rw [h_off_aligned_addr]
              split_ands
              . clear h_div_4_aw0_diff h_pos_eq2 h_pos_eq3
                rw [← eq_offset]
                by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
                . simp_all
                . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
                  . simp_all
                  . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1 <;> simp_all
              . clear h_div_4_aw0_diff h_pos_eq2 h_pos_eq3
                rw [← eq_offset]
                by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
                . simp_all
                . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
                  . simp_all
                  . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1 <;> simp_all
              . clear *- h_mem_0 h_mem_1 h_mem_2 h_mem_3 h_eqp_mav0 h_eqp_mav1 h_eqp_mav2 h_eqp_mav3
                rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
                rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
                rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by assumption)]
                rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by assumption)]
            -- LW
            . by_cases h_eq_lw : air.cols.instruction.opcode row 0 = 12
              . simp [h_eq_lw] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
                obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_lw
                simp [eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw] at h_eqp_mav0 h_eqp_mav1 h_eqp_mav2 h_eqp_mav3
                simp_all
                simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
                simp [List.filterMap_cons, List.filterMap_nil]
                have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
                simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
                repeat rw [BitVec.extractLsb'_append_eq_ite]
                simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
                simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
                simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
                rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
                rw [h_off_aligned_addr]
                clear h_div_4_aw0_diff
                rw [← eq_offset]
                constructor
                . by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
                  . simp_all
                  . by_cases h_off_2 : air.cols.offset_is_two row 0 = 1
                    . simp_all
                    . by_cases h_off_3 : air.cols.offset_is_three row 0 = 1 <;> simp_all
                . clear *- h_mem_0 h_mem_1 h_mem_2 h_mem_3 h_eqp_mav0 h_eqp_mav1 h_eqp_mav2 h_eqp_mav3
                  rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
                  rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
                  rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by assumption)]
                  rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by assumption)]
              -- SB
              . by_cases h_eq_sb : air.cols.instruction.opcode row 0 = 15
                . simp [h_eq_sb] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
                  obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_sb
                  simp_all
                  simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
                  simp [List.filterMap_cons, List.filterMap_nil]
                  have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
                  simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
                  repeat rw [BitVec.extractLsb'_append_eq_ite]
                  simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
                  simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
                  simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
                  rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
                  rw [h_off_aligned_addr]
                  clear h_div_4_aw0_diff
                  rw [← eq_offset]
                  . by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
                    . simp_all
                      rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
                      rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                      rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                    . by_cases h_off_1 : air.cols.offset_is_two row 0 = 1
                      . simp_all
                        rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
                        rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
                        rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                      . by_cases h_off_1 : air.cols.offset_is_three row 0 = 1 <;> simp_all
                        . rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by assumption)]
                        . rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                -- LH
                . by_cases h_eq_sh : air.cols.instruction.opcode row 0 = 16
                  . simp [h_eq_sh] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
                    obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_sh
                    simp_all
                    simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
                    simp [List.filterMap_cons, List.filterMap_nil]
                    have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
                    simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
                    repeat rw [BitVec.extractLsb'_append_eq_ite]
                    simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
                    simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
                    simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
                    rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
                    rw [h_off_aligned_addr]
                    clear h_div_4_aw0_diff
                    rw [← eq_offset]
                    . by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
                      . simp_all
                      . by_cases h_off_1 : air.cols.offset_is_two row 0 = 1
                        . simp_all
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val) (h := by assumption)]
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 1) (h := by assumption)]
                        . by_cases h_off_1 : air.cols.offset_is_three row 0 = 1 <;> simp_all
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 2) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                          rw [ExtHashMap.insert_eq_self (k := (air.cols.addr_aligned row 0).val + 3) (h := by simp [Std.ExtHashMap.getElem?_insert]; assumption)]
                  -- LW
                  . by_cases h_eq_sw : air.cols.instruction.opcode row 0 = 17
                    . simp [h_eq_sw] at op_lb op_lh op_lw op_lbu op_lhu op_sb op_sh op_sw
                      obtain ⟨ eq_lb, eq_lbu, eq_lh, eq_lhu, eq_lw, eq_sb, eq_sh, eq_sw ⟩ := op_sw
                      simp_all
                      simp [RV32IM.operation_list_effect, RV32IM.operation_effect, RV32IM.bus_operations, bus_row, *]
                      simp [List.filterMap_cons, List.filterMap_nil]
                      have : ¬ (air.cols.addr_aligned row 0 < 32) := by omega
                      simp [this, RV32IM.operation_effect, BitVec.extractLsb, U32b.toBV]; clear this
                      repeat rw [BitVec.extractLsb'_append_eq_ite]
                      simp; intro h_mem_0 h_mem_1 h_mem_2 h_mem_3
                      simp [← BitVec.toNat_inj] at asm_addr; rw [← asm_addr]; clear asm_addr
                      simp [U32b.toNat]; repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
                      rw [mul_comm (b := 256), mul_comm (b := 65536), mul_comm (b := 16777216)]
                      rw [h_off_aligned_addr]
                      clear h_div_4_aw0_diff
                      rw [← eq_offset]
                      . by_cases h_off_1 : air.cols.offset_is_one row 0 = 1
                        . simp_all
                        . by_cases h_off_1 : air.cols.offset_is_two row 0 = 1
                          . simp_all
                          . by_cases h_off_1 : air.cols.offset_is_three row 0 = 1 <;> simp_all
                    . clear *- opcode_range h_eq_lb h_eq_lbu h_eq_lh h_eq_lhu h_eq_lw h_eq_sb h_eq_sh h_eq_sw
                      omega

  end BusEquivalence

end MemoryReadWriteAir.Spec
