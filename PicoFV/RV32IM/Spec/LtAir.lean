import PicoFV.RV32IM.Constraints.LtAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace LtAir.Spec

  open RV32IM_Interactions
  open LtAir.ConstraintsAndBuses
  open LtAir.Interactions
  open LtAir.Interpretations

  set_option maxHeartbeats 1_000_000_000

  private lemma msb_is_bool (b bm msb : FKB)
      (hb : (b : ℕ) < 256)
      (hbm : bm = b &&& 127)
      (hmsb : msb = (b - bm) * 2114060289) :
      msb = 0 ∨ msb = 1 := by
    subst hbm; subst hmsb
    have h_and : (b &&& 127 : FKB).val = b.val % 128 := by
      simp only [Fin.and_val]
      change b.val &&& 127 = b.val % 128
      conv_lhs => rw [show (127 : ℕ) = 2 ^ 7 - 1 from by norm_num]
      conv_rhs => rw [show (128 : ℕ) = 2 ^ 7 from by norm_num]
      exact Nat.and_two_pow_sub_one_eq_mod b.val 7
    have h_sub : (b - (b &&& 127) : FKB).val = b.val - b.val % 128 := by
      rw [Fin.val_sub, h_and]; omega
    have h4 : b.val / 128 = 0 ∨ b.val / 128 = 1 := by omega
    rcases h4 with h | h
    · left
      have : (b - (b &&& 127) : FKB) = 0 := by ext; rw [h_sub]; omega
      simp [this]
    · right
      have hsub_val : (b - (b &&& 127) : FKB).val = 128 := by rw [h_sub]; omega
      have : ((b - (b &&& 127)) * 2114060289 : FKB).val = 1 := by
        simp only [Fin.val_mul, hsub_val]; norm_num
      exact_mod_cast Fin.ext this

  private lemma not_negative_of_msb_lt
      (b0 b1 b2 b3 : FKB) (_h0 : b0 < 256) (_h1 : b1 < 256) (_h2 : b2 < 256) (h3 : (b3 : ℕ) < 128) :
      ¬ U32.negative #v[(b0 : BitVec 8), (b1 : BitVec 8), (b2 : BitVec 8), (b3 : BitVec 8)] := by
    simp [U32.negative, U32.toNat]; omega

  private lemma negative_of_msb_ge
      (b0 b1 b2 b3 : FKB) (_h0 : b0 < 256) (_h1 : b1 < 256) (h2 : b2 < 256) (h3 : 128 ≤ (b3 : ℕ))
      (h4 : b3 < 256) :
      U32.negative #v[(b0 : BitVec 8), (b1 : BitVec 8), (b2 : BitVec 8), (b3 : BitVec 8)] := by
    simp [U32.negative, U32.toNat]; omega

  --
  -- Externals
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_LtAir FKB ExtF)
    (row : ℕ)
    (h_constraints : LtAir.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    obtain ⟨ h_b_add, h_b_sub, h_b_sum ⟩ := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row]
    grind

  --
  -- Opcode specifications
  --

  lemma spec_SLT
    [Field ExtF]
    (air : Valid_LtAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtAir.Extraction.allHold air row)
    (h_slt : air.cols.is_slt row 0 = 1)
  :
    ALUBus.Spec 8
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Establish is_slt_u = 0
    have selectors := selector_breakdown air row h_constraints
    have h_sltu : air.cols.is_slt_u row 0 = 0 := by grind
    -- Simplify ALUBus.Spec with opcode 8
    simp only [ALUBus.Spec]
    -- Simplify constraints and assumptions
    simp [constraint_and_interaction_simplification, sub_eq_zero, h_slt, h_sltu] at h_constraints
    simp [bus_row_wf_asm, bus_row, h_slt, h_sltu, ByteBus.Spec] at h_wf
    -- Extract assumptions
    obtain ⟨⟨h_bm_eq, h_bm_lt, h_b3_lt⟩, ⟨h_cm_eq, h_cm_lt, h_c3_lt⟩,
            h_sltu_eq, h_cb0_lt, h_cb1_lt⟩ := h_wf
    -- Extract constraints
    obtain ⟨_, h_msb_b, h_msb_c, h_same_bit_binary, h_bb, h_bc, h_ssb_zero_or_eq, h_ssb_or, h_a0, h_a1, h_a2, h_a3,
            h_ceq_bool, h_bf0_bool, h_bf1_bool, h_bf2_bool, h_bf3_bool, _,
            h_sum_eq, h_c18, _, h_c20, _, h_c22, _, h_c24, _,
            h_cb0_eq, h_cb1_eq, h_c28⟩ := h_constraints
    -- Derive bit_b and bit_c are boolean
    have h_bb_bool := msb_is_bool _ _ (air.cols.bit_b row 0) h_b3_lt h_bm_eq
      (by rw [h_bb]; exact h_msb_b)
    have h_bc_bool := msb_is_bool _ _ (air.cols.bit_c row 0) h_c3_lt h_cm_eq
      (by rw [h_bc]; exact h_msb_c)
    -- Derive byte decomposition: b_3 = b_masked + bit_b * 128
    have h_b3_decomp : air.cols.b_3 row 0 = air.cols.b_masked row 0 + air.cols.bit_b row 0 * 128 := by
      have : air.cols.bit_b row 0 * 128 = air.cols.b_3 row 0 - air.cols.b_masked row 0 := by
        rw [h_bb, h_msb_b, mul_assoc, show (2114060289 : FKB) * 128 = 1 from by decide, mul_one]
      rw [this, add_sub_cancel]
    have h_c3_decomp : air.cols.c_3 row 0 = air.cols.c_masked row 0 + air.cols.bit_c row 0 * 128 := by
      have : air.cols.bit_c row 0 * 128 = air.cols.c_3 row 0 - air.cols.c_masked row 0 := by
        rw [h_bc, h_msb_c, mul_assoc, show (2114060289 : FKB) * 128 = 1 from by decide, mul_one]
      rw [this, add_sub_cancel]
    -- Derive Nat-level byte bounds from FKB decomposition
    have h_b3_ge : air.cols.bit_b row 0 = 1 → 128 ≤ (air.cols.b_3 row 0).val := by
      intro h; have h_eq := h_b3_decomp; simp [h] at h_eq
      have := congr_arg Fin.val h_eq; simp [Fin.val_add] at this; omega
    have h_b3_lt' : air.cols.bit_b row 0 = 0 → (air.cols.b_3 row 0).val < 128 := by
      intro h; have h_eq := h_b3_decomp; simp [h] at h_eq
      rw [h_eq, h_bm_eq]; simp [Fin.and_val]
      exact lt_of_le_of_lt Nat.and_le_right (by omega)
    have h_c3_ge : air.cols.bit_c row 0 = 1 → 128 ≤ (air.cols.c_3 row 0).val := by
      intro h; have h_eq := h_c3_decomp; simp [h] at h_eq
      have := congr_arg Fin.val h_eq; simp [Fin.val_add] at this; omega
    have h_c3_lt' : air.cols.bit_c row 0 = 0 → (air.cols.c_3 row 0).val < 128 := by
      intro h; have h_eq := h_c3_decomp; simp [h] at h_eq
      rw [h_eq, h_cm_eq]; simp [Fin.and_val]
      exact lt_of_le_of_lt Nat.and_le_right (by omega)
    -- Intro ops_range
    simp [bus_row_ext_asm, bus_row, h_slt, h_sltu] at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Simplify a_1 = a_2 = a_3 = 0
    simp [h_a1, h_a2, h_a3]
    -- result_range for a_0
    have h_a0_lt : air.cols.a_0 row 0 < 256 := by
      rw [h_a0]; rcases h_bb_bool with hb | hb <;> rcases h_bc_bool with hc | hc <;>
      simp [hb, hc, h_sltu_eq] <;> split_ifs <;> clear *- h_same_bit_binary <;> omega
    simp [h_a0_lt, ← BitVec.toNat_inj, U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    -- Simplify the outer if-then-else .toNat and convert toInt
    simp only [apply_ite BitVec.toNat]
    simp only [show (1#32).toNat = 1 from rfl, show (0#32).toNat = 0 from rfl]
    -- Case split on sign bits FIRST, then handle each case cleanly
    rcases h_bb_bool with hbb | hbb <;> rcases h_bc_bool with hbc | hbc
    · -- bit_b = 0, bit_c = 0 (both positive → toInt = toNat)
      have hbn := not_negative_of_msb_lt _ _ _ _ hb0 hb1 hb2 (h_b3_lt' hbb)
      have hcn := not_negative_of_msb_lt _ _ _ _ hc0 hc1 hc2 (h_c3_lt' hbc)
      simp only [U32.toInt, hbn, hcn, ↓reduceIte, U32.toNat]
      -- Now goal is about toNat < toNat, same as SLTU
      simp [hbb, hbc] at h_a0 h_ssb_or
      simp [h_a0, h_ssb_or, apply_ite Fin.val, h_sltu_eq, h_cb0_eq, h_cb1_eq]
      -- Clear FKB-specific hypotheses to prevent simp_all recursion
      clear h_bm_eq h_cm_eq h_msb_b h_msb_c h_bb h_bc
            h_b3_ge h_b3_lt' h_c3_ge h_c3_lt' hbn hcn h_ssb_zero_or_eq h_ssb_or
            h_same_bit_binary h_a0
      rcases h_ceq_bool with hce | hce <;>
      rcases h_bf3_bool with hbf3 | hbf3 <;>
      rcases h_bf2_bool with hbf2 | hbf2 <;>
      rcases h_bf1_bool with hbf1 | hbf1 <;>
      rcases h_bf0_bool with hbf0 | hbf0 <;>
      simp_all <;> grind
    · -- bit_b = 0, bit_c = 1 (b positive, c negative → b.toInt ≥ c.toInt → result = 0)
      have hbn := not_negative_of_msb_lt _ _ _ _ hb0 hb1 hb2 (h_b3_lt' hbb)
      have hcn := negative_of_msb_ge _ _ _ _ hc0 hc1 hc2 (h_c3_ge hbc) hc3
      have h_ssb_zero : air.cols.is_sign_bit_same row 0 = 0 := by
        rcases h_ssb_zero_or_eq with h | h; exact h; simp [hbb, hbc] at h
      simp only [U32.toInt, hbn, hcn, ↓reduceIte, U32.toNat]
      simp [hbb, hbc, h_ssb_zero] at h_a0
      simp [h_a0]; omega
    · -- bit_b = 1, bit_c = 0 (b negative, c positive → b.toInt < c.toInt → result = 1)
      have hbn := negative_of_msb_ge _ _ _ _ hb0 hb1 hb2 (h_b3_ge hbb) hb3
      have hcn := not_negative_of_msb_lt _ _ _ _ hc0 hc1 hc2 (h_c3_lt' hbc)
      have h_ssb_zero : air.cols.is_sign_bit_same row 0 = 0 := by
        rcases h_ssb_zero_or_eq with h | h; exact h; simp [hbb, hbc] at h
      simp only [U32.toInt, hbn, hcn, ↓reduceIte, U32.toNat]
      simp [hbb, hbc, h_ssb_zero] at h_a0
      simp [h_a0]; omega
    · -- bit_b = 1, bit_c = 1 (both negative → toInt comparison = toNat comparison)
      have hbn := negative_of_msb_ge _ _ _ _ hb0 hb1 hb2 (h_b3_ge hbb) hb3
      have hcn := negative_of_msb_ge _ _ _ _ hc0 hc1 hc2 (h_c3_ge hbc) hc3
      simp only [U32.toInt, hbn, hcn, ↓reduceIte, U32.toNat]
      -- Now goal is about toNat < toNat (offset cancels)
      simp [hbb, hbc] at h_a0 h_ssb_or
      simp [h_a0, h_ssb_or, apply_ite Fin.val, h_sltu_eq, h_cb0_eq, h_cb1_eq]
      -- Clear FKB-specific hypotheses to prevent simp_all recursion
      clear h_bm_eq h_cm_eq h_msb_b h_msb_c h_bb h_bc
            h_b3_ge h_b3_lt' h_c3_ge h_c3_lt' hbn hcn h_ssb_zero_or_eq h_ssb_or
            h_same_bit_binary h_a0
      rcases h_ceq_bool with hce | hce <;>
      rcases h_bf3_bool with hbf3 | hbf3 <;>
      rcases h_bf2_bool with hbf2 | hbf2 <;>
      rcases h_bf1_bool with hbf1 | hbf1 <;>
      rcases h_bf0_bool with hbf0 | hbf0 <;>
      simp_all <;> try grind
      all_goals
        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
        simp [Fin.val_add]
        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
        grind

  lemma spec_SLTU
    [Field ExtF]
    (air : Valid_LtAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtAir.Extraction.allHold air row)
    (h_sltu : air.cols.is_slt_u row 0 = 1)
  :
    ALUBus.Spec 9
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Establish is_slt = 0
    have selectors := selector_breakdown air row h_constraints
    have h_slt : air.cols.is_slt row 0 = 0 := by grind
    -- Simplify ALUBus.Spec with opcode 9
    simp only [ALUBus.Spec]
    -- Simplify constraints and assumptions
    simp [constraint_and_interaction_simplification, sub_eq_zero, h_slt, h_sltu] at h_constraints
    simp [bus_row_wf_asm, bus_row, h_slt, h_sltu, ByteBus.Spec] at h_wf
    -- Extract assumptions
    obtain ⟨⟨_, _, _⟩, ⟨_, _, _⟩, h_sltu_eq, h_cb0_lt, h_cb1_lt⟩ := h_wf
    -- Extract constraints
    obtain ⟨_, _, _, _, h_bb, h_bc, _, h_ssb_or, h_a0, h_a1, h_a2, h_a3,
            h_ceq_bool, h_bf0_bool, h_bf1_bool, h_bf2_bool, h_bf3_bool, _,
            h_sum_eq, h_c18, _, h_c20, _, h_c22, _, h_c24, _,
            h_cb0_eq, h_cb1_eq, h_c28⟩ := h_constraints
    -- Derive is_sign_bit_same = 1
    have h_ssb : air.cols.is_sign_bit_same row 0 = 1 := by
      rcases h_ssb_or with h | h; exact h; simp [h_bb, h_bc] at h
    -- Simplify a_0 = slt_u
    simp [h_bb, h_bc, h_ssb] at h_a0
    -- Intro ops_range
    simp [bus_row_ext_asm, bus_row, h_slt, h_sltu] at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Rewrite goal with constraint equalities
    simp [h_a0, h_a1, h_a2, h_a3]
    -- result_range and U32 comparison
    have h_slt : air.cols.slt_u row 0 < 256
      := by simp [h_sltu_eq]; split_ifs <;> omega
    simp [h_slt, ← BitVec.toNat_inj, U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    -- Relate slt_u to byte comparison, then to word comparison
    simp [apply_ite BitVec.toNat, h_sltu_eq, apply_ite Fin.val, h_cb0_eq, h_cb1_eq]
    -- Case split on all byte flags
    rcases h_ceq_bool with hce | hce <;>
    rcases h_bf3_bool with hbf3 | hbf3 <;>
    rcases h_bf2_bool with hbf2 | hbf2 <;>
    rcases h_bf1_bool with hbf1 | hbf1 <;>
    rcases h_bf0_bool with hbf0 | hbf0 <;>
    simp_all <;> grind

  --
  -- Well-formedness
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_LtAir FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtAir.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    -- Set up assumptions
    have h_wf' := h_wf
    simp [bus_row_wf_asm] at h_wf'
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf'
    -- Main proof
    simp [bus_row_wf_asrt]
    constructor
    -- Program
    . simp [bus_row]
    . constructor
      . -- ALU
        simp [bus_row]
        intro h_mult
        have selectors := selector_breakdown air row h_constraints
        obtain ⟨h1, h2, _⟩ := selectors
        rcases h1 with h_slt | h_slt
        · -- is_slt = 0
          rcases h2 with h_sltu | h_sltu
          · -- is_slt = 0, is_slt_u = 0 → contradiction with h_mult
            exfalso; grind
          · -- is_slt_u = 1
            simp only [h_slt, h_sltu, one_mul, zero_mul, zero_add]
            exact spec_SLTU air row h_ext h_wf h_constraints h_sltu
        · -- is_slt = 1
          have h_sltu : air.cols.is_slt_u row 0 = 0 := by grind
          simp only [h_slt, h_sltu, one_mul, zero_mul, add_zero]
          exact spec_SLT air row h_ext h_wf h_constraints h_slt
      . constructor
        . -- Byte
          simp [bus_row, ByteBus.Spec]
          have selectors := selector_breakdown air row h_constraints
          split_ands <;> intro h <;> exfalso <;> grind
        . -- Register
          simp [bus_row]

end LtAir.Spec
