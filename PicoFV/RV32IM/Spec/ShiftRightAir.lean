import PicoFV.RV32IM.Constraints.ShiftRightAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace ShiftRightAir.Spec

  open RV32IM_Interactions
  open ShiftRightAir.ConstraintsAndBuses
  open ShiftRightAir.Interactions

  -- Helper: selector breakdown (is_srl, is_sra are binary, sum is binary)
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_ShiftRightAir FKB ExtF)
    (row : ℕ)
    (h_constraints : ShiftRightAir.Extraction.allHold air row)
  :
    (air.cols.is_srl row 0 = 0 ∨ air.cols.is_srl row 0 = 1) ∧
    (air.cols.is_sra row 0 = 0 ∨ air.cols.is_sra row 0 = 1) ∧
    (air.cols.is_srl row 0 + air.cols.is_sra row 0 = 0 ∨
     air.cols.is_srl row 0 + air.cols.is_sra row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

  -- Helper: Convert ByteBusEntry opcode 4 (SHR carry output) to Nat equations
  private lemma shr_byte_nat (sb carry bsr low3 : FKB)
      (hsb : sb.val < 256) (hcarry : carry.val < 256)
      (hbsr : bsr.val < 256) (hlow3 : low3.val < 8)
      (h_sb : sb = bsr >>> low3)
      (h_carry : carry = bsr - (sb <<< low3)) :
      bsr.val = sb.val * 2^low3.val + carry.val ∧ carry.val < 2^low3.val := by
    have h_sb_val : sb.val = bsr.val / 2^low3.val := by subst h_sb; simp [Nat.shiftRight_eq_div_pow]
    have h_pow_bound : 2^low3.val < 256 := by interval_cases low3.val <;> simp
    have h_shl_le_bsr : sb.val * 2^low3.val ≤ bsr.val := by
      rw [h_sb_val]
      have h_dam := Nat.div_add_mod bsr.val (2^low3.val)
      grind
    have h_shl_nat : (sb <<< low3 : FKB).val = sb.val * 2^low3.val := by
      simp [Nat.shiftLeft_eq]; omega
    have h_carry_val : carry.val = bsr.val - sb.val * 2^low3.val := by grind
    have h_pos : (0 : ℕ) < 2^low3.val := by positivity
    constructor
    · omega
    · rw [h_carry_val, h_sb_val]
      have h_dam := Nat.div_add_mod bsr.val (2^low3.val)
      have : bsr.val / 2 ^ low3.val * 2 ^ low3.val = 2 ^ low3.val * (bsr.val / 2 ^ low3.val) := by ring
      have := Nat.mod_lt bsr.val h_pos
      omega

  -- Helper: Convert carry chain constraint to Nat equation
  -- bit_shift_result_i = shifted_byte_i + carry_next * divisor (FKB)
  -- → bit_shift_result_i.val = shifted_byte_i.val + carry_next.val * divisor.val (Nat)
  private lemma carry_chain_nat (btr sb cn div : FKB)
      (hbtr : btr.val < 256) (hsb : sb.val < 256)
      (hcn : cn.val < 256) (hdiv : div.val ≤ 256)
      (heq : btr = sb + cn * div) :
      btr.val = sb.val + cn.val * div.val := by
    have hprod : cn.val * div.val ≤ 255 * 256 := Nat.mul_le_mul (by omega) hdiv
    grind

  -- Helper: right-shift split from KB to Nat
  private lemma sub_shift_val_KB_to_Nat {a b : FKB}
  :
    (a - a >>> b <<< b).val = a.val - a.val >>> b.val <<< b.val
  := by
    rw [Fin.sub_val_of_le]
    . simp [Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt]
      apply lt_of_le_of_lt (b := a.val) (by apply Nat.div_mul_le_self) (hbc := by simp)
    . simp [Fin.le_def]
      simp [Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt]
      . apply Nat.div_mul_le_self
      . apply lt_of_le_of_lt (b := a.val) (by apply Nat.div_mul_le_self) (hbc := by simp)

  -- Helper: right-shift split from Nat to Int
  private lemma sub_shift_val_Nat_to_Int {a b : ℕ}
  :
    ((↑(a - a >>> b <<< b)) : ℤ) = ↑a - (↑a / (2 ^ ↑b) * (2 ^ ↑b))
  := by
    rw [Int.ofNat_sub] <;> simp [Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow]
    apply Nat.div_mul_le_self

  -- Tactic macro for closing each SRL shift case with a concrete shift amount
  set_option hygiene false in
  local macro "close_srl" : tactic =>
    `(tactic| (
      simp_all
      simp [← BitVec.toNat_inj, U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
      try simp [Fin.val_add, Fin.val_mul, sub_shift_val_KB_to_Nat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      try simp [Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow]
      try omega))

  lemma spec_SRL
    [Field ExtF]
    (air : Valid_ShiftRightAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightAir.Extraction.allHold air row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_is_srl : air.cols.is_srl row 0 = 1)
  :
    ALUBus.Spec
      6
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Derive is_sra = 0 from constraints
    have h_is_sra : air.cols.is_sra row 0 = 0 := by
      have selectors := selector_breakdown air row h_constraints
      grind
    -- Unfold ALUBus.Spec for opcode 6
    simp only [ALUBus.Spec]
    simp [bus_row_ext_asm, bus_row, h_is_real, h_is_srl, h_is_sra] at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Get byte bounds from assumptions
    simp [bus_row_wf_asm, bus_row, h_is_real, ByteBus.Spec] at h_wf
    -- Simplify constraints
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    -- Extract all constraints
    obtain ⟨h_constrain_interactions, h_c0_decomp,
      h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel,
      h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel,
      h_sbn_sum,
      h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel,
      h_sbnb_sum,
      h_bs0_bsr0, h_bs0_bsr1, h_bs0_bsr2, h_bs0_bsr3,
      h_bs0_bsr4, h_bs0_bsr5, h_bs0_bsr6, h_bs0_bsr7,
      h_bs1_bsr0, h_bs1_bsr1, h_bs1_bsr2,
      h_bs1_bsr3, h_bs1_bsr4, h_bs1_bsr5, h_bs1_bsr6,
      h_bs2_bsr0, h_bs2_bsr1,
      h_bs2_bsr2, h_bs2_bsr3, h_bs2_bsr4, h_bs2_bsr5,
      h_bs3_bsr0,
      h_bs3_bsr1, h_bs3_bsr2, h_bs3_bsr3, h_bs3_bsr4,
      h_cc7, h_cc6, h_cc5, h_cc4, h_cc3, h_cc2, h_cc1, h_cc0,
      h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq,
      h_is_srl_bin, h_is_sra_bin, h_is_real_bin, h_b_msb_bin,
      h_sbnb0_bin, h_sbnb1_bin, h_sbnb2_bin, h_sbnb3_bin,
      h_sbn0_bin, h_sbn1_bin, h_sbn2_bin, h_sbn3_bin,
      h_sbn4_bin, h_sbn5_bin, h_sbn6_bin, h_sbn7_bin,
      h_lsb0_bin, h_lsb1_bin, h_lsb2_bin, h_lsb3_bin,
      h_lsb4_bin, h_lsb5_bin, h_lsb6_bin, h_lsb7_bin,
      h_is_srl_bin2, h_is_sra_bin2, h_is_real_bin2,
      h_sel_sum⟩ := h_constraints
    -- Extract assumptions (ByteBus entries + bounds)
    obtain ⟨⟨h_b_msb_eq, h_b_msb_bound, h_b3_bound_dup⟩,
      ⟨h_sb7_eq, h_carry7_eq, h_sb7_bound, h_carry7_bound, h_bsr7_bound_bb, h_low3_bound_bb7⟩,
      ⟨h_sb6_eq, h_carry6_eq, h_sb6_bound, h_carry6_bound, h_bsr6_bound_bb, h_low3_bound_bb6⟩,
      ⟨h_sb5_eq, h_carry5_eq, h_sb5_bound, h_carry5_bound, h_bsr5_bound_bb, h_low3_bound_bb5⟩,
      ⟨h_sb4_eq, h_carry4_eq, h_sb4_bound, h_carry4_bound, h_bsr4_bound_bb, h_low3_bound_bb4⟩,
      ⟨h_sb3_eq, h_carry3_eq, h_sb3_bound, h_carry3_bound, h_bsr3_bound_bb, h_low3_bound_bb3⟩,
      ⟨h_sb2_eq, h_carry2_eq, h_sb2_bound, h_carry2_bound, h_bsr2_bound_bb, h_low3_bound_bb2⟩,
      ⟨h_sb1_eq, h_carry1_eq, h_sb1_bound, h_carry1_bound, h_bsr1_bound_bb, h_low3_bound_bb1⟩,
      ⟨h_sb0_eq, h_carry0_eq, h_sb0_bound, h_carry0_bound, h_bsr0_bound_bb, h_low3_bound_bb0⟩,
      ⟨h_bsr0_bound, h_bsr1_bound⟩, ⟨h_bsr2_bound, h_bsr3_bound⟩,
      ⟨h_bsr4_bound, h_bsr5_bound⟩, ⟨h_bsr6_bound, h_bsr7_bound⟩,
      ⟨h_bitsr0_bound, h_bitsr1_bound⟩, ⟨h_bitsr2_bound, h_bitsr3_bound⟩,
      ⟨h_bitsr4_bound, h_bitsr5_bound⟩, ⟨h_bitsr6_bound, h_bitsr7_bound⟩,
      rest⟩ := h_wf
    -- Clear duplicates
    clear h_b3_bound_dup rest
    -- Get the mod 32
    have h_mod_32:
      U32.toNat #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
                   BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] % 32
        =
      air.cols.c_least_sig_byte_0 row 0 + 2 * air.cols.c_least_sig_byte_1 row 0 +
      4 * air.cols.c_least_sig_byte_2 row 0 + 8 * air.cols.c_least_sig_byte_3 row 0 + 16 * air.cols.c_least_sig_byte_4 row 0
    := by
      simp [U32.toNat, ← h_c0_decomp]
      clear *- hc0 hc1 hc2 hc3 h_lsb0_bin
               h_lsb0_bin h_lsb1_bin h_lsb2_bin h_lsb3_bin
               h_lsb4_bin h_lsb5_bin h_lsb6_bin h_lsb7_bin
      grind
    rw [h_mod_32]
    clear h_c0_decomp h_mod_32 hc0 hc1 hc2 hc3
    symm at h_cc0 h_cc1 h_cc2 h_cc3 h_cc4 h_cc5 h_cc6 h_cc7

    clear h_constrain_interactions h_is_real_bin h_is_real_bin2 h_sel_sum h_is_real
    simp [h_is_sra] at h_bs0_bsr4 h_bs0_bsr5 h_bs0_bsr6 h_bs0_bsr7
                       h_bs1_bsr3 h_bs1_bsr4 h_bs1_bsr5 h_bs1_bsr6
                       h_bs2_bsr2 h_bs2_bsr3 h_bs2_bsr4 h_bs2_bsr5
                       h_bs3_bsr1 h_bs3_bsr2 h_bs3_bsr3 h_bs3_bsr4
    clear h_is_srl_bin h_is_srl_bin2 h_is_srl h_is_sra_bin h_is_sra_bin2 h_is_sra
    clear h_low3_bound_bb0 h_low3_bound_bb1 h_low3_bound_bb2 h_low3_bound_bb3 h_low3_bound_bb4 h_low3_bound_bb5 h_low3_bound_bb6 h_low3_bound_bb7
    clear h_lsb5_bin h_lsb6_bin h_lsb7_bin

    rcases h_lsb0_bin with h0 | h0 <;>
    rcases h_lsb1_bin with h1 | h1 <;>
    rcases h_lsb2_bin with h2 | h2 <;>
    rcases h_lsb3_bin with h3 | h3 <;>
    rcases h_lsb4_bin with h4 | h4

    all_goals
      simp [h0, h1, h2, h3, h4]
      set shift := air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4
      have eq_shift : shift = air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4 := by rfl
      simp [h0, h1, h2] at eq_shift; clear h0 h1 h2
      simp [eq_shift] at h_sbn0_sel h_sbn1_sel h_sbn2_sel h_sbn3_sel h_sbn4_sel h_sbn5_sel h_sbn6_sel h_sbn7_sel
                         h_sb0_eq h_sb1_eq h_sb2_eq h_sb3_eq h_sb4_eq h_sb5_eq h_sb6_eq h_sb7_eq
                         h_carry0_eq h_carry1_eq h_carry2_eq h_carry3_eq h_carry4_eq h_carry5_eq h_carry6_eq h_carry7_eq
      clear eq_shift; subst shift
      simp [h3, h4] at h_sbnb0_sel h_sbnb1_sel h_sbnb2_sel h_sbnb3_sel
      simp [h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel] at h_sbnb_sum
      clear h3 h4
      simp [h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel, h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel] at h_sbn_sum
      clear h_sbn0_bin h_sbn1_bin h_sbn2_bin h_sbn3_bin h_sbn4_bin h_sbn5_bin h_sbn6_bin h_sbn7_bin
      simp [h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel, h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel, h_sbn_sum]
        at h_cc0 h_cc1 h_cc2 h_cc3 h_cc4 h_cc5 h_cc6 h_cc7
      clear h_sbn0_sel h_sbn1_sel h_sbn2_sel h_sbn3_sel h_sbn4_sel h_sbn5_sel h_sbn6_sel h_sbn7_sel h_sbn_sum
      simp [h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel, h_sbnb_sum]
        at h_bs0_bsr0 h_bs0_bsr1 h_bs0_bsr2 h_bs0_bsr3 h_bs0_bsr4 h_bs0_bsr5 h_bs0_bsr6 h_bs0_bsr7
           h_bs1_bsr0 h_bs1_bsr1 h_bs1_bsr2 h_bs1_bsr3 h_bs1_bsr4 h_bs1_bsr5 h_bs1_bsr6
           h_bs2_bsr0 h_bs2_bsr1 h_bs2_bsr2 h_bs2_bsr3 h_bs2_bsr4 h_bs2_bsr5
           h_bs3_bsr0 h_bs3_bsr1 h_bs3_bsr2 h_bs3_bsr3 h_bs3_bsr4
      clear h_sbnb0_bin h_sbnb1_bin h_sbnb2_bin h_sbnb3_bin
            h_sbnb0_sel h_sbnb1_sel h_sbnb2_sel h_sbnb3_sel h_sbnb_sum
      simp [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq,
            h_bitsr0_bound, h_bitsr1_bound, h_bitsr2_bound, h_bitsr3_bound]
      simp [h_bs0_bsr0, h_bs0_bsr1, h_bs0_bsr2, h_bs0_bsr3, h_bs0_bsr4, h_bs0_bsr5, h_bs0_bsr6, h_bs0_bsr7,
            h_bs1_bsr0, h_bs1_bsr1, h_bs1_bsr2, h_bs1_bsr3, h_bs1_bsr4, h_bs1_bsr5, h_bs1_bsr6,
            h_bs2_bsr0, h_bs2_bsr1, h_bs2_bsr2, h_bs2_bsr3, h_bs2_bsr4, h_bs2_bsr5,
            h_bs3_bsr0, h_bs3_bsr1, h_bs3_bsr2, h_bs3_bsr3, h_bs3_bsr4]
        at h_sb0_eq h_sb1_eq h_sb2_eq h_sb3_eq h_sb4_eq h_sb5_eq h_sb6_eq h_sb7_eq
           h_carry0_eq h_carry1_eq h_carry2_eq h_carry3_eq h_carry4_eq h_carry5_eq h_carry6_eq h_carry7_eq
           h_bsr0_bound h_bsr1_bound h_bsr2_bound h_bsr3_bound h_bsr4_bound h_bsr5_bound h_bsr6_bound h_bsr7_bound
      clear h_bs0_bsr0 h_bs0_bsr1 h_bs0_bsr2 h_bs0_bsr3 h_bs0_bsr4 h_bs0_bsr5 h_bs0_bsr6 h_bs0_bsr7
            h_bs1_bsr0 h_bs1_bsr1 h_bs1_bsr2 h_bs1_bsr3 h_bs1_bsr4 h_bs1_bsr5 h_bs1_bsr6
            h_bs2_bsr0 h_bs2_bsr1 h_bs2_bsr2 h_bs2_bsr3 h_bs2_bsr4 h_bs2_bsr5
            h_bs3_bsr0 h_bs3_bsr1 h_bs3_bsr2 h_bs3_bsr3 h_bs3_bsr4
      simp [h_sb0_eq, h_sb1_eq, h_sb2_eq, h_sb3_eq, h_sb4_eq, h_sb5_eq, h_sb6_eq, h_sb7_eq]
        at h_sb0_bound h_sb1_bound h_sb2_bound h_sb3_bound h_sb4_bound h_sb5_bound h_sb6_bound h_sb7_bound
           h_cc0 h_cc1 h_cc2 h_cc3 h_cc4 h_cc5 h_cc6 h_cc7
           h_carry0_eq h_carry1_eq h_carry2_eq h_carry3_eq h_carry4_eq h_carry5_eq h_carry6_eq h_carry7_eq
      clear h_sb0_eq h_sb1_eq h_sb2_eq h_sb3_eq h_sb4_eq h_sb5_eq h_sb6_eq h_sb7_eq
      simp [h_cc0, h_cc1, h_cc2, h_cc3, h_cc4, h_cc5, h_cc6, h_cc7]
        at h_bitsr0_bound h_bitsr1_bound h_bitsr2_bound h_bitsr3_bound h_bitsr4_bound h_bitsr5_bound h_bitsr6_bound h_bitsr7_bound ⊢
      simp [h_carry1_eq, h_carry2_eq, h_carry3_eq, h_carry4_eq]
      simp [← BitVec.toNat_inj, U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
      try simp [Fin.val_add, Fin.val_mul, sub_shift_val_KB_to_Nat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      try simp [Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow]
      try omega

  lemma spec_SRA
    [Field ExtF]
    (air : Valid_ShiftRightAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightAir.Extraction.allHold air row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_is_sra : air.cols.is_sra row 0 = 1)
  :
    ALUBus.Spec
      7
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Derive is_srl = 0 from constraints
    have h_is_srl : air.cols.is_srl row 0 = 0 := by
      have selectors := selector_breakdown air row h_constraints
      grind
    -- Unfold ALUBus.Spec for opcode 7
    simp only [ALUBus.Spec]
    simp [bus_row_ext_asm, bus_row, h_is_real, h_is_srl, h_is_sra] at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Get byte bounds from assumptions
    simp [bus_row_wf_asm, bus_row, h_is_real, ByteBus.Spec] at h_wf
    -- Simplify constraints
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    -- Extract all constraints
    obtain ⟨h_constrain_interactions, h_c0_decomp,
      h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel,
      h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel,
      h_sbn_sum,
      h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel,
      h_sbnb_sum,
      h_bs0_bsr0, h_bs0_bsr1, h_bs0_bsr2, h_bs0_bsr3,
      h_bs0_bsr4, h_bs0_bsr5, h_bs0_bsr6, h_bs0_bsr7,
      h_bs1_bsr0, h_bs1_bsr1, h_bs1_bsr2,
      h_bs1_bsr3, h_bs1_bsr4, h_bs1_bsr5, h_bs1_bsr6,
      h_bs2_bsr0, h_bs2_bsr1,
      h_bs2_bsr2, h_bs2_bsr3, h_bs2_bsr4, h_bs2_bsr5,
      h_bs3_bsr0,
      h_bs3_bsr1, h_bs3_bsr2, h_bs3_bsr3, h_bs3_bsr4,
      h_cc7, h_cc6, h_cc5, h_cc4, h_cc3, h_cc2, h_cc1, h_cc0,
      h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq,
      h_is_srl_bin, h_is_sra_bin, h_is_real_bin, h_b_msb_bin,
      h_sbnb0_bin, h_sbnb1_bin, h_sbnb2_bin, h_sbnb3_bin,
      h_sbn0_bin, h_sbn1_bin, h_sbn2_bin, h_sbn3_bin,
      h_sbn4_bin, h_sbn5_bin, h_sbn6_bin, h_sbn7_bin,
      h_lsb0_bin, h_lsb1_bin, h_lsb2_bin, h_lsb3_bin,
      h_lsb4_bin, h_lsb5_bin, h_lsb6_bin, h_lsb7_bin,
      h_is_srl_bin2, h_is_sra_bin2, h_is_real_bin2,
      h_sel_sum⟩ := h_constraints
    -- Extract assumptions (ByteBus entries + bounds)
    obtain ⟨⟨h_b_msb_eq, h_b_msb_bound, h_b3_bound_dup⟩,
      ⟨h_sb7_eq, h_carry7_eq, h_sb7_bound, h_carry7_bound, h_bsr7_bound_bb, h_low3_bound_bb7⟩,
      ⟨h_sb6_eq, h_carry6_eq, h_sb6_bound, h_carry6_bound, h_bsr6_bound_bb, h_low3_bound_bb6⟩,
      ⟨h_sb5_eq, h_carry5_eq, h_sb5_bound, h_carry5_bound, h_bsr5_bound_bb, h_low3_bound_bb5⟩,
      ⟨h_sb4_eq, h_carry4_eq, h_sb4_bound, h_carry4_bound, h_bsr4_bound_bb, h_low3_bound_bb4⟩,
      ⟨h_sb3_eq, h_carry3_eq, h_sb3_bound, h_carry3_bound, h_bsr3_bound_bb, h_low3_bound_bb3⟩,
      ⟨h_sb2_eq, h_carry2_eq, h_sb2_bound, h_carry2_bound, h_bsr2_bound_bb, h_low3_bound_bb2⟩,
      ⟨h_sb1_eq, h_carry1_eq, h_sb1_bound, h_carry1_bound, h_bsr1_bound_bb, h_low3_bound_bb1⟩,
      ⟨h_sb0_eq, h_carry0_eq, h_sb0_bound, h_carry0_bound, h_bsr0_bound_bb, h_low3_bound_bb0⟩,
      ⟨h_bsr0_bound, h_bsr1_bound⟩, ⟨h_bsr2_bound, h_bsr3_bound⟩,
      ⟨h_bsr4_bound, h_bsr5_bound⟩, ⟨h_bsr6_bound, h_bsr7_bound⟩,
      ⟨h_bitsr0_bound, h_bitsr1_bound⟩, ⟨h_bitsr2_bound, h_bitsr3_bound⟩,
      ⟨h_bitsr4_bound, h_bitsr5_bound⟩, ⟨h_bitsr6_bound, h_bitsr7_bound⟩,
      rest⟩ := h_wf
    -- Clear duplicates
    clear h_b3_bound_dup rest
    -- Get the mod 32
    have h_mod_32:
      U32.toNat #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
                   BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] % 32
        =
      air.cols.c_least_sig_byte_0 row 0 + 2 * air.cols.c_least_sig_byte_1 row 0 +
      4 * air.cols.c_least_sig_byte_2 row 0 + 8 * air.cols.c_least_sig_byte_3 row 0 + 16 * air.cols.c_least_sig_byte_4 row 0
    := by
      simp [U32.toNat, ← h_c0_decomp]
      clear *- hc0 hc1 hc2 hc3 h_lsb0_bin
               h_lsb0_bin h_lsb1_bin h_lsb2_bin h_lsb3_bin
               h_lsb4_bin h_lsb5_bin h_lsb6_bin h_lsb7_bin
      grind
    rw [h_mod_32]
    clear h_c0_decomp h_mod_32 hc0 hc1 hc2 hc3
    symm at h_cc0 h_cc1 h_cc2 h_cc3 h_cc4 h_cc5 h_cc6 h_cc7

    -- b_msb is the MSB of b
    have h_b_msb_is_msb :
      (BitVec.ofNat 8 ↑(air.cols.b_3 row 0)).msb = true
      ↔ air.cols.b_msb row 0 = 1
    := by
      simp [BitVec.msb_eq_decide]
      grind (splits := 10)

    have h_b_msb_is_msb_shift_b3 :
      ∀ m n, n < 8 → m.val = 2 ^ (8 - n.val) →
       ((BitVec.ofNat 8 ↑(air.cols.b_3 row 0 >>> n +
         (air.cols.b_msb row 0 * 255 - (air.cols.b_msb row 0 * 255) >>> n <<< n) * m)).msb = true
        ↔ air.cols.b_msb row 0 = 1)
    := by
      intro m n h_n h_m
      simp [BitVec.msb_eq_decide, Fin.val_add, Fin.val_mul, sub_shift_val_KB_to_Nat]
      rw [Nat.mod_eq_of_lt (a := _ * _) (b := KB_prime) (by grind)]
      simp [Fin.lt_def] at h_n
      obtain h_b_msb_bin | h_b_msb_bin := h_b_msb_bin <;>
        simp [h_b_msb_bin] <;> simp [h_b_msb_eq] at h_b_msb_bin <;>
        interval_cases n.val <;> clear *- hb3 h_n h_m h_b_msb_bin <;>
        simp [Nat.shiftRight_eq_div_pow] <;>
        omega

    have h_b_msb_is_msb_shift_msb :
      ∀ m n, n < 8 → m.val = 2 ^ (8 - n.val) →
       ((BitVec.ofNat 8 ↑((air.cols.b_msb row 0 * 255) >>> n +
         (air.cols.b_msb row 0 * 255 - (air.cols.b_msb row 0 * 255) >>> n <<< n) * m)).msb = true
        ↔ air.cols.b_msb row 0 = 1)
    := by
      intro m n h_n h_m
      simp [BitVec.msb_eq_decide, Fin.val_add, Fin.val_mul, sub_shift_val_KB_to_Nat]
      rw [Nat.mod_eq_of_lt (a := _ * _) (b := KB_prime) (by grind)]
      simp [Fin.lt_def] at h_n
      obtain h_b_msb_bin | h_b_msb_bin := h_b_msb_bin <;>
        simp [h_b_msb_bin]; simp [h_b_msb_eq] at h_b_msb_bin;
        interval_cases n.val <;> clear *- hb3 h_n h_m h_b_msb_bin <;>
        simp [Nat.shiftRight_eq_div_pow] <;>
        omega

    clear h_constrain_interactions h_is_real_bin h_is_real_bin2 h_sel_sum h_is_real
    simp [h_is_sra] at h_bs0_bsr4 h_bs0_bsr5 h_bs0_bsr6 h_bs0_bsr7
                       h_bs1_bsr3 h_bs1_bsr4 h_bs1_bsr5 h_bs1_bsr6
                       h_bs2_bsr2 h_bs2_bsr3 h_bs2_bsr4 h_bs2_bsr5
                       h_bs3_bsr1 h_bs3_bsr2 h_bs3_bsr3 h_bs3_bsr4
    clear h_is_srl_bin h_is_srl_bin2 h_is_srl h_is_sra_bin h_is_sra_bin2 h_is_sra
    clear h_low3_bound_bb0 h_low3_bound_bb1 h_low3_bound_bb2 h_low3_bound_bb3 h_low3_bound_bb4 h_low3_bound_bb5 h_low3_bound_bb6 h_low3_bound_bb7
    clear h_lsb5_bin h_lsb6_bin h_lsb7_bin
    clear h_b_msb_eq

    rcases h_lsb0_bin with h0 | h0 <;>
    rcases h_lsb1_bin with h1 | h1 <;>
    rcases h_lsb2_bin with h2 | h2 <;>
    rcases h_lsb3_bin with h3 | h3 <;>
    rcases h_lsb4_bin with h4 | h4

    all_goals
      have msb_shift_b3 :=
        h_b_msb_is_msb_shift_b3
          (n := air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4)
          (m := ⟨ 2 ^ (8 - (air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4)).val, by simp [h0, h1, h2]⟩)
          (by simp [h0, h1, h2])
          (by simp [h0, h1, h2])
      have msb_shift_msb :=
        h_b_msb_is_msb_shift_msb
          (n := air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4)
          (m := ⟨ 2 ^ (8 - (air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4)).val, by simp [h0, h1, h2]⟩)
          (by simp [h0, h1, h2])
          (by simp [h0, h1, h2])

    all_goals
      simp [h0, h1, h2, h3, h4] at msb_shift_b3 msb_shift_msb ⊢
      set shift := air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4
      have eq_shift : shift = air.cols.c_least_sig_byte_0 row 0 + air.cols.c_least_sig_byte_1 row 0 * 2 + air.cols.c_least_sig_byte_2 row 0 * 4 := by rfl
      simp [h0, h1, h2] at eq_shift; clear h0 h1 h2
      simp [eq_shift] at h_sbn0_sel h_sbn1_sel h_sbn2_sel h_sbn3_sel h_sbn4_sel h_sbn5_sel h_sbn6_sel h_sbn7_sel
                         h_sb0_eq h_sb1_eq h_sb2_eq h_sb3_eq h_sb4_eq h_sb5_eq h_sb6_eq h_sb7_eq
                         h_carry0_eq h_carry1_eq h_carry2_eq h_carry3_eq h_carry4_eq h_carry5_eq h_carry6_eq h_carry7_eq
      clear eq_shift; subst shift
      simp [h3, h4] at h_sbnb0_sel h_sbnb1_sel h_sbnb2_sel h_sbnb3_sel
      simp [h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel] at h_sbnb_sum
      clear h3 h4
      simp [h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel, h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel] at h_sbn_sum
      clear h_sbn0_bin h_sbn1_bin h_sbn2_bin h_sbn3_bin h_sbn4_bin h_sbn5_bin h_sbn6_bin h_sbn7_bin
      simp [h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel, h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel, h_sbn_sum]
        at h_cc0 h_cc1 h_cc2 h_cc3 h_cc4 h_cc5 h_cc6 h_cc7
      clear h_sbn0_sel h_sbn1_sel h_sbn2_sel h_sbn3_sel h_sbn4_sel h_sbn5_sel h_sbn6_sel h_sbn7_sel h_sbn_sum
      simp [h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel, h_sbnb_sum]
        at h_bs0_bsr0 h_bs0_bsr1 h_bs0_bsr2 h_bs0_bsr3 h_bs0_bsr4 h_bs0_bsr5 h_bs0_bsr6 h_bs0_bsr7
           h_bs1_bsr0 h_bs1_bsr1 h_bs1_bsr2 h_bs1_bsr3 h_bs1_bsr4 h_bs1_bsr5 h_bs1_bsr6
           h_bs2_bsr0 h_bs2_bsr1 h_bs2_bsr2 h_bs2_bsr3 h_bs2_bsr4 h_bs2_bsr5
           h_bs3_bsr0 h_bs3_bsr1 h_bs3_bsr2 h_bs3_bsr3 h_bs3_bsr4
      clear h_sbnb0_bin h_sbnb1_bin h_sbnb2_bin h_sbnb3_bin
            h_sbnb0_sel h_sbnb1_sel h_sbnb2_sel h_sbnb3_sel h_sbnb_sum
      simp [h_a0_eq, h_a1_eq, h_a2_eq, h_a3_eq,
            h_bitsr0_bound, h_bitsr1_bound, h_bitsr2_bound, h_bitsr3_bound]
      simp [h_bs0_bsr0, h_bs0_bsr1, h_bs0_bsr2, h_bs0_bsr3, h_bs0_bsr4, h_bs0_bsr5, h_bs0_bsr6, h_bs0_bsr7,
            h_bs1_bsr0, h_bs1_bsr1, h_bs1_bsr2, h_bs1_bsr3, h_bs1_bsr4, h_bs1_bsr5, h_bs1_bsr6,
            h_bs2_bsr0, h_bs2_bsr1, h_bs2_bsr2, h_bs2_bsr3, h_bs2_bsr4, h_bs2_bsr5,
            h_bs3_bsr0, h_bs3_bsr1, h_bs3_bsr2, h_bs3_bsr3, h_bs3_bsr4]
        at h_sb0_eq h_sb1_eq h_sb2_eq h_sb3_eq h_sb4_eq h_sb5_eq h_sb6_eq h_sb7_eq
           h_carry0_eq h_carry1_eq h_carry2_eq h_carry3_eq h_carry4_eq h_carry5_eq h_carry6_eq h_carry7_eq
           h_bsr0_bound h_bsr1_bound h_bsr2_bound h_bsr3_bound h_bsr4_bound h_bsr5_bound h_bsr6_bound h_bsr7_bound
      clear h_bs0_bsr0 h_bs0_bsr1 h_bs0_bsr2 h_bs0_bsr3 h_bs0_bsr4 h_bs0_bsr5 h_bs0_bsr6 h_bs0_bsr7
            h_bs1_bsr0 h_bs1_bsr1 h_bs1_bsr2 h_bs1_bsr3 h_bs1_bsr4 h_bs1_bsr5 h_bs1_bsr6
            h_bs2_bsr0 h_bs2_bsr1 h_bs2_bsr2 h_bs2_bsr3 h_bs2_bsr4 h_bs2_bsr5
            h_bs3_bsr0 h_bs3_bsr1 h_bs3_bsr2 h_bs3_bsr3 h_bs3_bsr4
      simp [h_sb0_eq, h_sb1_eq, h_sb2_eq, h_sb3_eq, h_sb4_eq, h_sb5_eq, h_sb6_eq, h_sb7_eq]
        at h_sb0_bound h_sb1_bound h_sb2_bound h_sb3_bound h_sb4_bound h_sb5_bound h_sb6_bound h_sb7_bound
           h_cc0 h_cc1 h_cc2 h_cc3 h_cc4 h_cc5 h_cc6 h_cc7
           h_carry0_eq h_carry1_eq h_carry2_eq h_carry3_eq h_carry4_eq h_carry5_eq h_carry6_eq h_carry7_eq
      clear h_sb0_eq h_sb1_eq h_sb2_eq h_sb3_eq h_sb4_eq h_sb5_eq h_sb6_eq h_sb7_eq
      simp [h_cc0, h_cc1, h_cc2, h_cc3, h_cc4, h_cc5, h_cc6, h_cc7]
        at h_bitsr0_bound h_bitsr1_bound h_bitsr2_bound h_bitsr3_bound h_bitsr4_bound h_bitsr5_bound h_bitsr6_bound h_bitsr7_bound ⊢
      simp [h_carry1_eq, h_carry2_eq, h_carry3_eq, h_carry4_eq]

      simp [← BitVec.toInt_inj, U32.toInt, ← U32.msb_3_negative]
      simp [h_b_msb_is_msb, msb_shift_b3, msb_shift_msb]

    . simp [U32.toNat,
            Fin.val_add, Fin.val_mul,
            sub_shift_val_KB_to_Nat]
      ring_nf
      clear *- hb0 hb1 hb2 hb3
      omega

    all_goals
      split_ifs with h_b_msb
      . simp [h_b_msb, U32.toNat,
             Fin.val_add, Fin.val_mul,
             sub_shift_val_KB_to_Nat, sub_shift_val_Nat_to_Int,
             Int.shiftRight_eq_div_pow]
        repeat rw [Int.emod_eq_of_lt (b := KB_prime) (by omega) (by grind)]
        repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)]
        ring_nf
        clear *- hb0 hb1 hb2 hb3
        omega
      . simp [h_b_msb] at h_b_msb_bin
        simp [h_b_msb_bin, U32.toNat,
             Fin.val_add, Fin.val_mul,
             sub_shift_val_KB_to_Nat, sub_shift_val_Nat_to_Int,
             Int.shiftRight_eq_div_pow]
        repeat rw [Int.emod_eq_of_lt (b := KB_prime) (by omega) (by grind)]
        repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)]
        ring_nf
        clear *- hb0 hb1 hb2 hb3
        omega

end ShiftRightAir.Spec
