import PicoFV.RV64IM.Constraints.ShiftRightChip
import PicoFV.RV64IM.Spec.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# ShiftRightChip — semantic specification

Four ALU outputs handled (vs two for SLLChip):

- `spec_SRL`  (opcode 6):  64-bit logical right shift, shift = low 6 bits of `c_for_lookup`.
- `spec_SRA`  (opcode 7):  64-bit arithmetic right shift (sign-extends MSB).
- `spec_SRLW` (opcode 43): 32-bit logical right shift, then sign-extend to 64.
- `spec_SRAW` (opcode 44): 32-bit arithmetic right shift, then sign-extend to 64.

## Soundness fixes incorporated from Pico PR #101

The two soundness gaps previously bridged by Lean-level `MISSING_*`
axioms have been closed upstream in commit
`0bacdaf030d4bdc812315ca2f0263410e7d6a522`
(*fix(alu): close two soundness gaps in ShiftRight chip constraints*):

1. **`b[i] · v_0123 = higher_limb[i] · 65536 + lower_limb[i] · v_0123`**
   for `i ∈ {0..3}` (Constraints 60..63) — ties the range-checked
   `(lower_limb_i, higher_limb_i)` decomposition back to `b_i`. The
   bridge from this carry equation to the Nat-level decomposition is
   performed by the `b_decomp_from_carry` helper below.

2. **`c = c_for_lookup_0`** (Constraint 59) — binds the scalar
   shift-amount column to the Word low limb broadcast on the ALU bus.

Both extracted constraints land in `Extraction.ShiftRightChip` /
`ConstraintsAndBuses` and are now part of the destructured constraint
list inside each `spec_S*` proof.
-/

namespace ShiftRightChip.Spec

  open RV64IM_Interactions
  open ShiftRightChip.ConstraintsAndBuses
  open ShiftRightChip.Interactions
  open ShiftRightChip.Interpretations
  open LeanRV64D.Functions

  set_option maxHeartbeats 4_000_000_000

  -- =====================================================================
  -- `v_0123` cascade for SR: when `c_bits_0..3` are booleans,
  -- `v_0123 = 2^(16 - k_nat)` where `k_nat = c0.val + 2 c1.val + 4 c2.val + 8 c3.val`.
  -- The cascade is `v_01 = ((1-c0)+1)·2 · ((1-c1)·3+1) = 2^(3 - c0 - 2·c1)`,
  -- and `v_0123 = 2^(16 - k_nat)`.
  -- =====================================================================
  private lemma v0123_pow_inv
      (c0 c1 c2 c3 v01 v012 v0123 : FKB)
      (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1)
      (hc2 : c2 = 0 ∨ c2 = 1) (hc3 : c3 = 0 ∨ c3 = 1)
      (h_v01  : v01   = ((1 - c0) + 1) * 2 * ((1 - c1) * 3 + 1))
      (h_v012 : v012  = v01 * ((1 - c2) * 15 + 1))
      (h_v0123: v0123 = v012 * ((1 - c3) * 255 + 1))
    : c0.val + 2*c1.val + 4*c2.val + 8*c3.val ≤ 15 ∧
      v0123 = ((2^(16 - (c0.val + 2*c1.val + 4*c2.val + 8*c3.val)) : ℕ) : FKB) := by
    rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;>
    rcases hc2 with h2 | h2 <;> rcases hc3 with h3 | h3 <;>
    subst h0 h1 h2 h3 <;>
    refine ⟨?_, ?_⟩ <;> simp_all

  -- =====================================================================
  -- `s4` decomposition: same as SLL — the FKB sum `c0·1 + c1·2 + c2·4 + c3·8`
  -- has Nat value `c0.val + 2 c1.val + 4 c2.val + 8 c3.val`, and
  -- `16 - s4_FKB` has Nat value `16 - s4_nat`.
  -- =====================================================================
  private lemma s4_FKB_val
      (c0 c1 c2 c3 : FKB)
      (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1)
      (hc2 : c2 = 0 ∨ c2 = 1) (hc3 : c3 = 0 ∨ c3 = 1)
    : (c0 + c1 * 2 + c2 * 4 + c3 * 8).val
        = c0.val + 2*c1.val + 4*c2.val + 8*c3.val ∧
      (16 - (c0 + c1 * 2 + c2 * 4 + c3 * 8) : FKB).val
        = 16 - (c0.val + 2*c1.val + 4*c2.val + 8*c3.val) := by
    rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;>
    rcases hc2 with h2 | h2 <;> rcases hc3 with h3 | h3 <;>
    subst h0 h1 h2 h3 <;> decide

  -- =====================================================================
  -- `limb_result_{i<3}` lift for SR: `(higher_i + lower_{i+1} · 2^(16-k)).val
  --     = higher_i.val + lower_{i+1}.val · 2^(16-k)` (< 2^16 — the new limb fits).
  -- =====================================================================
  private lemma lr_val_lift
      (h_i lower_next : FKB) (k_nat : ℕ)
      (hk : k_nat ≤ 15)
      (hhi : h_i.val < 2^(16 - k_nat))
      (hlow : lower_next.val < 2^k_nat)
    : (h_i + lower_next * ((2^(16-k_nat) : ℕ) : FKB)).val
        = h_i.val + lower_next.val * 2^(16-k_nat) := by
    have hpow_prod : (2^k_nat : ℕ) * 2^(16-k_nat) = 2^16 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : k_nat ≤ 16)]
    have hpow_lt : (2^(16-k_nat) : ℕ) < KB_prime := by
      have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hpow_val : (((2^(16-k_nat):ℕ):FKB)).val = 2^(16-k_nat) := by
      rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt hpow_lt
    have h_prod_val :
        (lower_next * ((2^(16-k_nat):ℕ):FKB)).val = lower_next.val * 2^(16-k_nat) := by
      rw [Fin.val_mul, hpow_val]
      apply Nat.mod_eq_of_lt
      have h1 : lower_next.val * 2^(16-k_nat) < 2^k_nat * 2^(16-k_nat) :=
        Nat.mul_lt_mul_of_pos_right hlow (Nat.two_pow_pos _)
      rw [hpow_prod] at h1; omega
    rw [Fin.val_add, h_prod_val]
    apply Nat.mod_eq_of_lt
    have h_prod_le : lower_next.val * 2^(16-k_nat) ≤ 2^16 - 2^(16-k_nat) := by
      have hle : lower_next.val ≤ 2^k_nat - 1 := by omega
      have h1 : lower_next.val * 2^(16-k_nat) ≤ (2^k_nat - 1) * 2^(16-k_nat) :=
        Nat.mul_le_mul_right _ hle
      have h2 : (2^k_nat - 1) * 2^(16-k_nat) = 2^16 - 2^(16-k_nat) := by
        rw [Nat.sub_mul, one_mul, hpow_prod]
      omega
    omega

  -- =====================================================================
  -- `b_decomp_from_carry`: bridges the per-limb carry equation
  --     b · v_0123 = higher · 65536 + lower · v_0123
  -- (Pico PR #101 constraints 60..63) into the Nat-level decomposition
  --     b.val = higher.val · 2^k + lower.val
  -- with `v_0123 = 2^(16 - k)` and the byte-bus bounds on (higher, lower).
  -- =====================================================================
  private lemma b_decomp_from_carry
      (b higher lower v_0123 : FKB) (k : ℕ)
      (hk_le : k ≤ 15)
      (hhi : higher.val < 2^(16 - k))
      (hlow : lower.val < 2^k)
      (hv : v_0123 = ((2^(16-k):ℕ):FKB))
      (hcarry : b * v_0123 = higher * 65536 + lower * v_0123)
    : b.val = higher.val * 2^k + lower.val := by
    have hk_le16 : k ≤ 16 := by omega
    have hpow_prod_nat : (2^(16-k) : ℕ) * 2^k = 2^16 := by
      rw [← pow_add, Nat.sub_add_cancel hk_le16]
    have hpow16k_le : (2^(16-k) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
    have hpowk_le : (2^k : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) hk_le16
    have hKB16 : 2^16 < KB_prime := by decide
    have hv_val : v_0123.val = 2^(16-k) := by
      rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt; omega
    have hv_pos : 0 < v_0123.val := by rw [hv_val]; exact Nat.two_pow_pos _
    have hv_ne : v_0123 ≠ 0 := by
      intro h; rw [h] at hv_pos; simp at hv_pos
    -- 65536 = v_0123 · 2^k in FKB.
    have h65k : (65536 : FKB) = v_0123 * ((2^k : ℕ) : FKB) := by
      rw [hv]
      have hcast : ((2^(16-k):ℕ):FKB) * ((2^k:ℕ):FKB) = ((2^(16-k) * 2^k : ℕ):FKB) := by
        push_cast; ring
      rw [hcast, hpow_prod_nat]
      decide
    -- Field-level decomposition (cancel v_0123).
    have hb_field : b = higher * ((2^k:ℕ):FKB) + lower := by
      have h1 : b * v_0123 = (higher * ((2^k:ℕ):FKB) + lower) * v_0123 := by
        rw [hcarry, h65k]; ring
      exact mul_right_cancel₀ hv_ne h1
    -- Take .val on both sides; bounds keep us under KB_prime.
    have hpowk_val : (((2^k:ℕ):FKB)).val = 2^k := by
      rw [Fin.val_natCast]; apply Nat.mod_eq_of_lt; omega
    have hbound : higher.val * 2^k < 2^16 := by
      calc higher.val * 2^k
          < 2^(16-k) * 2^k := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2^16            := hpow_prod_nat
    have h_prod_val : (higher * ((2^k:ℕ):FKB)).val = higher.val * 2^k := by
      rw [Fin.val_mul, hpowk_val]
      apply Nat.mod_eq_of_lt
      omega
    have h_sum_val : (higher * ((2^k:ℕ):FKB) + lower).val
                       = higher.val * 2^k + lower.val := by
      rw [Fin.val_add, h_prod_val]
      apply Nat.mod_eq_of_lt
      have hlo16 : lower.val < 2^16 := lt_of_lt_of_le hlow hpowk_le
      omega
    apply_fun Fin.val at hb_field
    rw [h_sum_val] at hb_field
    exact hb_field

  -- =====================================================================
  -- `c_0` mod-64 decomposition (same as SLLChip but with `c` replacing
  -- the `c_0` column).
  -- =====================================================================
  private lemma c_mod64
      (c_col s5_FKB : FKB)
      (hs5_val : s5_FKB.val ≤ 63)
      (hdecomp : ((c_col - s5_FKB) * 2097414145).val < 1024)
    : c_col.val % 64 = s5_FKB.val := by
    set t : FKB := (c_col - s5_FKB) * 2097414145 with ht_def
    have hinv : (64 : FKB) * 2097414145 = 1 := by decide
    have h64t : 64 * t = c_col - s5_FKB := by
      rw [ht_def]; linear_combination (c_col - s5_FKB) * hinv
    have hc_eq : c_col = s5_FKB + 64 * t := by rw [h64t]; ring
    have h64t_val : (64 * t : FKB).val = 64 * t.val := by
      rw [Fin.val_mul]
      have : (((64 : FKB)).val : ℕ) = 64 := by decide
      rw [this]
      apply Nat.mod_eq_of_lt
      have : t.val < 1024 := hdecomp
      omega
    have hsum_val : (s5_FKB + 64 * t : FKB).val = s5_FKB.val + 64 * t.val := by
      rw [Fin.val_add, h64t_val]
      apply Nat.mod_eq_of_lt
      have : t.val < 1024 := hdecomp
      omega
    apply_fun Fin.val at hc_eq
    rw [hsum_val] at hc_eq
    omega

  -- =====================================================================
  -- spec_SRL — opcode 6 (64-bit logical right shift).
  -- =====================================================================

  lemma spec_SRL
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_srl : air.cols.values.is_srl row 0 = 1)
    (h_is_sra : air.cols.values.is_sra row 0 = 0)
    (h_is_srlw : air.cols.values.is_srlw row 0 = 0)
    (h_is_sraw : air.cols.values.is_sraw row 0 = 0)
  :
    ALUBus.Spec
      6
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    -- Step 1: `is_real = 1` from the 4 selector hypotheses.
    have h_is_real :
      air.cols.values.is_srl row 0 + air.cols.values.is_sra row 0 +
      air.cols.values.is_srlw row 0 + air.cols.values.is_sraw row 0 = 1
      := by rw [h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]; ring
    -- Step 2: Extract operand u16 bounds from h_ext.
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Step 3: Extract byte-bus assumptions from h_wf.
    --   With is_srl = 1, is_sra = is_srlw = is_sraw = 0, all U16MSB byte
    --   entries (gated by is_sra, is_sraw, is_srlw + is_sraw) are
    --   vacuous. Only the 9 BitRange (opcode 9) entries fire.
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_wf
    obtain ⟨h_c_decomp,
            ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, _, h_hi3⟩ := h_wf
    -- Step 4: Extract all 64 constraints (post-simp with selectors).
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_srl, h_is_sra, h_is_srlw, h_is_sraw] at h_constraints
    obtain ⟨_, _h_imm_c_b, _h_w_imm,
            h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_v01, h_v012, h_v0123,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b,
            h_su2_sel, h_su2_b, h_su3_sel, h_su3_b,
            h_su_sum,
            h_lr0, h_lr1, h_lr2, h_lr3,
            _h_b_msb_b, h_b_msb_zero, h_sra_msb_v0123,
            _h_srw_msb_b, h_srw_msb_zero,
            h_su0_a0, h_su0_a1, h_su0_a2, h_su0_a3,
            h_su1_a0, h_su1_a1, h_su1_a2, h_su1_a3,
            h_su2_a0, h_su2_a1, h_su2_a2, h_su2_a3,
            h_su3_a0, h_su3_a1, h_su3_a2, h_su3_a3,
            h_c_eq,
            h_b_carry_0, h_b_carry_1, h_b_carry_2, h_b_carry_3⟩ := h_constraints
    -- Step 5: Derive `v_0123 = 2^(16-k)` and `k ≤ 15` (where `k = c_bits sum`).
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow_inv _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: Convert byte-bus bounds to Nat form using s4_FKB_val.
    rw [hs4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [h16s4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(16 - k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: Per-limb b-decomposition via Pico PR #101 carry constraints 60..63.
    have h_decomp_0 : (air.cols.values.b_0 row 0).val
        = (air.cols.values.higher_limb_0 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_0 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi0 h_lo0 hv h_b_carry_0
    have h_decomp_1 : (air.cols.values.b_1 row 0).val
        = (air.cols.values.higher_limb_1 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_1 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi1 h_lo1 hv h_b_carry_1
    have h_decomp_2 : (air.cols.values.b_2 row 0).val
        = (air.cols.values.higher_limb_2 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_2 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi2 h_lo2 hv h_b_carry_2
    have h_decomp_3 : (air.cols.values.b_3 row 0).val
        = (air.cols.values.higher_limb_3 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_3 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi3 h_lo3 hv h_b_carry_3
    -- Step 8: Compute Nat values of `limb_result_i`.
    rw [hv] at h_lr0 h_lr1 h_lr2
    have h_lr0_val := lr_val_lift _ _ k_nat hk_le h_hi0 h_lo1
    have h_lr1_val := lr_val_lift _ _ k_nat hk_le h_hi1 h_lo2
    have h_lr2_val := lr_val_lift _ _ k_nat hk_le h_hi2 h_lo3
    rw [← h_lr0] at h_lr0_val
    rw [← h_lr1] at h_lr1_val
    rw [← h_lr2] at h_lr2_val
    -- limb_result_3 = higher_limb_3 (no lower carry-in for top u16)
    have h_lr3_val : (air.cols.values.limb_result_3 row 0).val
        = (air.cols.values.higher_limb_3 row 0).val := by
      apply_fun Fin.val at h_lr3; exact h_lr3
    -- Step 9: Bounds for limb_result_i.
    have hpow_prod : (2^k_nat : ℕ) * 2^(16-k_nat) = 2^16 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : k_nat ≤ 16)]
    have hpow_le15 : (2^(16 - k_nat) : ℕ) ≤ 2^16 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h_lr0_lt : (air.cols.values.limb_result_0 row 0).val < 65536 := by
      rw [h_lr0_val]
      have h1 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_1 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr1_lt : (air.cols.values.limb_result_1 row 0).val < 65536 := by
      rw [h_lr1_val]
      have h1 : (air.cols.values.lower_limb_2 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_2 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_2 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr2_lt : (air.cols.values.limb_result_2 row 0).val < 65536 := by
      rw [h_lr2_val]
      have h1 : (air.cols.values.lower_limb_3 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_3 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_3 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr3_lt : (air.cols.values.limb_result_3 row 0).val < 65536 := by
      rw [h_lr3_val]; have : (2^(16-k_nat) : ℕ) ≤ 2^16 := hpow_le15; omega
    -- Step 10: For SRL, simplify the dispatch via h_b_msb_zero / h_srw_msb_zero /
    -- h_sra_msb_v0123 (= 0 since b_msb = 0).
    have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
      rw [h_sra_msb_v0123, h_b_msb_zero]; ring
    -- Step 11: Case-split on (c_bits_4, c_bits_5).
    rcases h_cb5_b with hcb5 | hcb5 <;> rcases h_cb4_b with hcb4 | hcb4
    -- Case (c5=0, c4=0): shift_u16_0 = 1, a_i = lr_i, shift = k_nat.
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
        rcases h_su2_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
        rcases h_su3_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su0_a0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_su0_a1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha2 : air.cols.values.a_2 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su0_a2 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha3 : air.cols.values.a_3 row 0 = air.cols.values.limb_result_3 row 0 := by
        rcases h_su0_a3 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_right,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨h_lr0_lt, h_lr1_lt, h_lr2_lt, h_lr3_lt⟩, ?_⟩
      -- BitVec identity for case (c5=0, c4=0): shift = k_nat.
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 0 * 32 : FKB).val = k_nat := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) := by ring
        rw [heq, hs4_val]
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      -- Bridge `c.val % 64 = k_nat` to `c_for_lookup_0.val % 64 = k_nat`
      -- via `h_c_eq` (PR #101 constraint 59: `c = c_for_lookup_0`).
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      apply BitVec.eq_of_toNat_eq
      simp [-BitVec.toNat_ushiftRight]
      rw [BitVec.toNat_ushiftRight]
      simp [U64w.toNat]
      rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_lr1_lt,
          Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt h_lr3_lt,
          Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
          Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
          Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
          Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
      -- c_for_lookup.toNat mod 64 = c_for_lookup_0.val mod 64 = k_nat.
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64 = k_nat := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rw [h_c_sum_mod_64, h_lr0_val, h_lr1_val, h_lr2_val, h_lr3_val,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
      clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_b_msb_zero h_sra_msb_v0123 h_srw_msb_zero h_sra_msb_zero
            _h_b_msb_b _h_srw_msb_b _h_imm_c_b _h_w_imm
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            ha0 ha1 ha2 ha3 hsu0 hsu1 hsu2 hsu3
            h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega
    -- Case (c5=0, c4=1): shift_u16_1 = 1, a_0=lr_1, a_1=lr_2, a_2=lr_3, a_3=0, shift=k+16.
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
        rcases h_su2_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
        rcases h_su3_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 1 := by
        rw [hsu0, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha2 : air.cols.values.a_2 row 0 = air.cols.values.limb_result_3 row 0 := by
        rcases h_su1_a2 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha3 : air.cols.values.a_3 row 0 = 0 := by
        rcases h_su1_a3 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_right,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨h_lr1_lt, h_lr2_lt, h_lr3_lt, ?_⟩, ?_⟩
      . simp
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 0 * 32 : FKB).val = k_nat + 16 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 16 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h16 : ((16 : FKB)).val = 16 := by decide
        rw [h16]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      apply BitVec.eq_of_toNat_eq
      simp [-BitVec.toNat_ushiftRight]
      rw [BitVec.toNat_ushiftRight]
      simp [U64w.toNat]
      rw [Nat.mod_eq_of_lt h_lr1_lt, Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt h_lr3_lt,
          Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
          Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
          Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
          Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
              = k_nat + 16 := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rw [h_c_sum_mod_64, h_lr1_val, h_lr2_val, h_lr3_val,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
      clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_b_msb_zero h_sra_msb_v0123 h_srw_msb_zero h_sra_msb_zero
            _h_b_msb_b _h_srw_msb_b _h_imm_c_b _h_w_imm
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            ha0 ha1 ha2 ha3 hsu0 hsu1 hsu2 hsu3
            h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega
    -- Case (c5=1, c4=0): shift_u16_2 = 1, a_0=lr_2, a_1=lr_3, a_2=0, a_3=0, shift=k+32.
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
        rcases h_su3_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 1 := by
        rw [hsu0, hsu1, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su2_a0 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_3 row 0 := by
        rcases h_su2_a1 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha2 : air.cols.values.a_2 row 0 = 0 := by
        rcases h_su2_a2 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      have ha3 : air.cols.values.a_3 row 0 = 0 := by
        rcases h_su2_a3 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_right,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨h_lr2_lt, h_lr3_lt, ?_, ?_⟩, ?_⟩
      . simp
      . simp
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 1 * 32 : FKB).val = k_nat + 32 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 32 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h32 : ((32 : FKB)).val = 32 := by decide
        rw [h32]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      apply BitVec.eq_of_toNat_eq
      simp [-BitVec.toNat_ushiftRight]
      rw [BitVec.toNat_ushiftRight]
      simp [U64w.toNat]
      rw [Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt h_lr3_lt,
          Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
          Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
          Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
          Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
              = k_nat + 32 := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rw [h_c_sum_mod_64, h_lr2_val, h_lr3_val,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
      clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_b_msb_zero h_sra_msb_v0123 h_srw_msb_zero h_sra_msb_zero
            _h_b_msb_b _h_srw_msb_b _h_imm_c_b _h_w_imm
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            ha0 ha1 ha2 ha3 hsu0 hsu1 hsu2 hsu3
            h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega
    -- Case (c5=1, c4=1): shift_u16_3 = 1, a_0=lr_3, a_1=0, a_2=0, a_3=0, shift=k+48.
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
        rcases h_su2_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 1 := by
        rw [hsu0, hsu1, hsu2] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_3 row 0 := by
        rcases h_su3_a0 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha1 : air.cols.values.a_1 row 0 = 0 := by
        rcases h_su3_a1 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      have ha2 : air.cols.values.a_2 row 0 = 0 := by
        rcases h_su3_a2 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      have ha3 : air.cols.values.a_3 row 0 = 0 := by
        rcases h_su3_a3 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_right,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨h_lr3_lt, ?_, ?_, ?_⟩, ?_⟩
      . simp
      . simp
      . simp
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 1 * 32 : FKB).val = k_nat + 48 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 48 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h48 : ((48 : FKB)).val = 48 := by decide
        rw [h48]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      apply BitVec.eq_of_toNat_eq
      simp [-BitVec.toNat_ushiftRight]
      rw [BitVec.toNat_ushiftRight]
      simp [U64w.toNat]
      rw [Nat.mod_eq_of_lt h_lr3_lt,
          Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
          Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
          Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
          Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
              = k_nat + 48 := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rw [h_c_sum_mod_64, h_lr3_val,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
      clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_b_msb_zero h_sra_msb_v0123 h_srw_msb_zero h_sra_msb_zero
            _h_b_msb_b _h_srw_msb_b _h_imm_c_b _h_w_imm
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            ha0 ha1 ha2 ha3 hsu0 hsu1 hsu2 hsu3
            h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega

  -- =====================================================================
  -- `neg_one_minus_div`: shift-right of `2^w - 1 - x` factors through the
  -- shift-right of `x` itself. Used in `spec_SRA` / `spec_SRAW` to turn the
  -- `BitVec.toNat_sshiftRight_of_msb_true` expression
  --   `2^w - 1 - (2^w - 1 - b.toNat) >>> k`
  -- into the chip-friendly form
  --   `b.toNat >>> k + (2^w - 2^(w - k))`
  -- (i.e. shift the value, then OR in the sign-extension fill).
  -- =====================================================================
  private lemma neg_one_minus_div (x k w : ℕ) (h : k ≤ w) (hx : x < 2^w) :
      (2^w - 1 - x) / 2^k = 2^(w - k) - 1 - x / 2^k := by
    have hk_pos : 0 < 2^k := Nat.two_pow_pos _
    have hpow : 2^(w - k) * 2^k = 2^w := by
      rw [← pow_add, Nat.sub_add_cancel h]
    generalize ha : 2^k = a at *
    generalize hb : 2^(w - k) = b at *
    generalize hc : 2^w = c at *
    have hxd : a * (x / a) + x % a = x := Nat.div_add_mod x a
    have hr_lt : x % a < a := Nat.mod_lt _ hk_pos
    have hq_lt : x / a < b := by
      by_contra hge
      push_neg at hge
      have h1 : b * a ≤ x / a * a := Nat.mul_le_mul_right _ hge
      rw [hpow] at h1
      have h2 : x / a * a ≤ x := Nat.div_mul_le_self _ _
      omega
    have hpa_le : x / a * a + a ≤ c := by
      have hmul : (x / a + 1) * a ≤ b * a := Nat.mul_le_mul_right a hq_lt
      rw [add_mul, one_mul, hpow] at hmul
      exact hmul
    have hxd' : x / a * a + x % a = x := by rw [mul_comm]; exact hxd
    have key : c - 1 - x = (a - 1 - x % a) + (b - 1 - x / a) * a := by
      have hsub : (b - 1 - x / a) * a = c - a - x / a * a := by
        have h2 : (b - 1 - x / a) * a = b * a - a - x / a * a := by
          rw [Nat.sub_mul, Nat.sub_mul, one_mul]
        rw [h2, hpow]
      rw [hsub]; omega
    rw [key]
    rw [Nat.add_mul_div_right _ _ hk_pos]
    rw [Nat.div_eq_of_lt (by omega : a - 1 - x % a < a)]
    omega

  -- =====================================================================
  -- spec_SRA — opcode 7 (64-bit arithmetic right shift, sign-extends b's MSB).
  --
  -- Same skeleton as `spec_SRL` (4-way case split on (c_bits_4, c_bits_5))
  -- but `b_msb` is no longer pinned to 0. Instead it is bound to the actual
  -- MSB of `b_3` by the U16MSB byte-bus entry (gated by `is_sra`); the
  -- partition `b_msb = 0 ∧ b_3 < 32768 ∨ b_msb = 1 ∧ 32768 ≤ b_3` is then
  -- derived directly from `h_msb_u16` and `h_b_msb_b` via `grind`. We then
  -- case-split on `b_msb ∈ {0, 1}`:
  -- - `b_msb = 0`: MSB(b) is false, so `BitVec.sshiftRight b = b >>> shift`
  --                and the proof is the SRL-style ushiftRight identity.
  -- - `b_msb = 1`: MSB(b) is true, so the top `shift` bits become all 1s
  --                via `2^64 - 2^(64 - shift)`; the chip realises this
  --                through the boundary-limb correction
  --                `b_msb · 65536 - sra_msb_v0123 = b_msb · (2^16 - v_0123)`
  --                and the `b_msb · 65535` fillers for the limbs entirely
  --                above the shift. The `neg_one_minus_div` helper bridges
  --                `BitVec.toNat_sshiftRight_of_msb_true` with this form.
  -- =====================================================================

  lemma spec_SRA
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_srl : air.cols.values.is_srl row 0 = 0)
    (h_is_sra : air.cols.values.is_sra row 0 = 1)
    (h_is_srlw : air.cols.values.is_srlw row 0 = 0)
    (h_is_sraw : air.cols.values.is_sraw row 0 = 0)
  :
    ALUBus.Spec
      7
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    -- Step 1: `is_real = 1`.
    have h_is_real :
      air.cols.values.is_srl row 0 + air.cols.values.is_sra row 0 +
      air.cols.values.is_srlw row 0 + air.cols.values.is_sraw row 0 = 1
      := by rw [h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]; ring
    -- Step 2: u16 bounds on operand limbs.
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Step 3: Byte-bus assumptions from h_wf.
    --   With is_sra = 1, is_srl = is_srlw = is_sraw = 0:
    --   9 BitRange entries fire + U16Range on `b_3` fires.
    --   The other two U16MSB entries (is_sraw, is_srlw+is_sraw) are vacuous.
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_wf
    obtain ⟨h_c_decomp,
            ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, ⟨_, h_hi3⟩,
            h_msb_u16⟩ := h_wf
    -- Step 4: Extract all 64 constraints (post-simp with selectors).
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_srl, h_is_sra, h_is_srlw, h_is_sraw] at h_constraints
    obtain ⟨_, _h_imm_c_b, _h_w_imm,
            h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_v01, h_v012, h_v0123,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b,
            h_su2_sel, h_su2_b, h_su3_sel, h_su3_b,
            h_su_sum,
            h_lr0, h_lr1, h_lr2, h_lr3,
            h_b_msb_b, h_sra_msb_v0123,
            _h_srw_msb_b, h_srw_msb_zero,
            h_su0_a0, h_su0_a1, h_su0_a2, h_su0_a3,
            h_su1_a0, h_su1_a1, h_su1_a2, h_su1_a3,
            h_su2_a0, h_su2_a1, h_su2_a2, h_su2_a3,
            h_su3_a0, h_su3_a1, h_su3_a2, h_su3_a3,
            h_c_eq,
            h_b_carry_0, h_b_carry_1, h_b_carry_2, h_b_carry_3⟩ := h_constraints
    -- Step 5: Derive `v_0123 = 2^(16-k)` and `k ≤ 15` (where `k = c_bits sum`).
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow_inv _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: Convert byte-bus bounds to Nat form using s4_FKB_val.
    rw [hs4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [h16s4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(16 - k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: Per-limb b-decomposition from PR #101 carry constraints.
    have h_decomp_0 : (air.cols.values.b_0 row 0).val
        = (air.cols.values.higher_limb_0 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_0 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi0 h_lo0 hv h_b_carry_0
    have h_decomp_1 : (air.cols.values.b_1 row 0).val
        = (air.cols.values.higher_limb_1 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_1 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi1 h_lo1 hv h_b_carry_1
    have h_decomp_2 : (air.cols.values.b_2 row 0).val
        = (air.cols.values.higher_limb_2 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_2 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi2 h_lo2 hv h_b_carry_2
    have h_decomp_3 : (air.cols.values.b_3 row 0).val
        = (air.cols.values.higher_limb_3 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_3 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi3 h_lo3 hv h_b_carry_3
    -- Step 8: Compute Nat values of `limb_result_i`.
    rw [hv] at h_lr0 h_lr1 h_lr2
    have h_lr0_val := lr_val_lift _ _ k_nat hk_le h_hi0 h_lo1
    have h_lr1_val := lr_val_lift _ _ k_nat hk_le h_hi1 h_lo2
    have h_lr2_val := lr_val_lift _ _ k_nat hk_le h_hi2 h_lo3
    rw [← h_lr0] at h_lr0_val
    rw [← h_lr1] at h_lr1_val
    rw [← h_lr2] at h_lr2_val
    have h_lr3_val : (air.cols.values.limb_result_3 row 0).val
        = (air.cols.values.higher_limb_3 row 0).val := by
      apply_fun Fin.val at h_lr3; exact h_lr3
    -- Step 9: limb_result_i bounds (< 2^16).
    have hpow_prod : (2^k_nat : ℕ) * 2^(16-k_nat) = 2^16 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : k_nat ≤ 16)]
    have hpow_le16 : (2^(16 - k_nat) : ℕ) ≤ 2^16 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h_lr0_lt : (air.cols.values.limb_result_0 row 0).val < 65536 := by
      rw [h_lr0_val]
      have h1 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_1 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr1_lt : (air.cols.values.limb_result_1 row 0).val < 65536 := by
      rw [h_lr1_val]
      have h1 : (air.cols.values.lower_limb_2 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_2 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_2 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr2_lt : (air.cols.values.limb_result_2 row 0).val < 65536 := by
      rw [h_lr2_val]
      have h1 : (air.cols.values.lower_limb_3 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_3 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_3 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr3_lt : (air.cols.values.limb_result_3 row 0).val < 65536 := by
      rw [h_lr3_val]; have : (2^(16-k_nat) : ℕ) ≤ 2^16 := hpow_le16; omega
    -- Step 10: SRA — `b_msb` is determined by MSB of `b_3` via U16MSBGadget.
    -- Combine `h_msb_u16` (range check on `2·b_3 - b_msb·65536`), `h_b_msb_b`
    -- (`b_msb ∈ {0,1}`), and `hb3` (`b_3 < 65536`) to derive the partition.
    have h_b_msb : (air.cols.values.b_msb.msb row 0 = 0 ∧
                    (air.cols.values.b_3 row 0).val < 32768) ∨
                   (air.cols.values.b_msb.msb row 0 = 1 ∧
                    32768 ≤ (air.cols.values.b_3 row 0).val) := by
      rcases h_b_msb_b with hm | hm
      . left; refine ⟨hm, ?_⟩; rw [hm] at h_msb_u16; grind
      . right; refine ⟨hm, ?_⟩; rw [hm] at h_msb_u16; grind
    -- Step 11: Case-split on (c_bits_4, c_bits_5).
    rcases h_cb5_b with hcb5 | hcb5 <;> rcases h_cb4_b with hcb4 | hcb4
    -- =============================================================
    -- Case (c5=0, c4=0): shift_u16_0 = 1, shift = k_nat ∈ [0, 15].
    -- =============================================================
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
        rcases h_su2_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
        rcases h_su3_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su0_a0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_su0_a1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha2 : air.cols.values.a_2 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su0_a2 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha3_raw : air.cols.values.a_3 row 0
                      = air.cols.values.limb_result_3 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su0_a3 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      -- c.val % 64 = k_nat (via byte-bus c_decomp + s5 lift).
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 0 * 32 : FKB).val = k_nat := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) := by ring
        rw [heq, hs4_val]
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64 = k_nat := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      -- Sub-case on b_msb ∈ {0, 1}.
      rcases h_b_msb with ⟨hbm0, hb3_lt⟩ | ⟨hbm1, hb3_ge⟩
      . -- b_msb = 0 sub-case: MSB(b) = false; sshiftRight reduces to ushiftRight.
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha3 : air.cols.values.a_3 row 0 = air.cols.values.limb_result_3 row 0 := by
          rw [ha3_raw, hbm0, h_sra_msb_zero]; ring
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure,
                   ha0, ha1, ha2, ha3]
        refine ⟨⟨h_lr0_lt, h_lr1_lt, h_lr2_lt, h_lr3_lt⟩, ?_⟩
        apply BitVec.eq_of_toNat_eq
        have h_msb_false : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                          air.cols.values.b_1 row 0,
                                          air.cols.values.b_2 row 0,
                                          air.cols.values.b_3 row 0]).msb = false := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_false]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_lr1_lt,
            Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt h_lr3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr0_val, h_lr1_val, h_lr2_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1 ha2 ha3 ha3_raw hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb_zero h_msb_u16 h_msb_false
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case: MSB(b) = true; sign-ext fills top k bits with 1s.
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha3_form : air.cols.values.a_3 row 0
                      = air.cols.values.limb_result_3 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha3_raw, hbm1, h_sra_msb]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha3_val : (air.cols.values.a_3 row 0).val
                     = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha3_form, Fin.val_add, h_diff_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.limb_result_3 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha3_lt : (air.cols.values.a_3 row 0).val < 65536 := by
          rw [ha3_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure,
                   ha0, ha1, ha2]
        refine ⟨⟨h_lr0_lt, h_lr1_lt, h_lr2_lt, ha3_lt⟩, ?_⟩
        apply BitVec.eq_of_toNat_eq
        have h_msb_true : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                         air.cols.values.b_1 row 0,
                                         air.cols.values.b_2 row 0,
                                         air.cols.values.b_3 row 0]).msb = true := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_true]
        -- Apply neg_one_minus_div to flatten the inner subtraction.
        have h_b_toNat_lt : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                           air.cols.values.b_1 row 0,
                                           air.cols.values.b_2 row 0,
                                           air.cols.values.b_3 row 0]).toNat < 2^64 :=
          BitVec.isLt _
        simp only [Nat.shiftRight_eq_div_pow]
        rw [neg_one_minus_div _ _ 64 (by
          -- shift amount ≤ 64
          have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                air.cols.values.c_for_lookup_1 row 0,
                                air.cols.values.c_for_lookup_2 row 0,
                                air.cols.values.c_for_lookup_3 row 0]).toNat % 64 < 64 :=
            Nat.mod_lt _ (by decide)
          omega) h_b_toNat_lt]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_lr1_lt,
            Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt ha3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr0_val, h_lr1_val, h_lr2_val, ha3_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt ha3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b h_msb_u16 h_msb_true
              h_b_toNat_lt
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1 ha2 ha3_raw ha3_form ha3_val
              hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb h_diff_val hv_val
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=0, c4=1): shift_u16_1 = 1, shift = k_nat + 16.
    -- a_0 = lr_1, a_1 = lr_2, a_2 = lr_3 + boundary, a_3 = b_msb · 65535.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
        rcases h_su2_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
        rcases h_su3_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 1 := by
        rw [hsu0, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha2_raw : air.cols.values.a_2 row 0
                      = air.cols.values.limb_result_3 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su1_a2 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha3_raw : air.cols.values.a_3 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su1_a3 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 0 * 32 : FKB).val = k_nat + 16 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 16 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h16 : ((16 : FKB)).val = 16 := by decide
        rw [h16]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
              = k_nat + 16 := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rcases h_b_msb with ⟨hbm0, hb3_lt⟩ | ⟨hbm1, hb3_ge⟩
      . -- b_msb = 0 sub-case
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha2 : air.cols.values.a_2 row 0 = air.cols.values.limb_result_3 row 0 := by
          rw [ha2_raw, hbm0, h_sra_msb_zero]; ring
        have ha3 : air.cols.values.a_3 row 0 = 0 := by
          rw [ha3_raw, hbm0]; ring
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure,
                   ha0, ha1, ha2, ha3]
        refine ⟨⟨h_lr1_lt, h_lr2_lt, h_lr3_lt, ?_⟩, ?_⟩
        . simp
        apply BitVec.eq_of_toNat_eq
        have h_msb_false : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                          air.cols.values.b_1 row 0,
                                          air.cols.values.b_2 row 0,
                                          air.cols.values.b_3 row 0]).msb = false := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_false]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr1_lt, Nat.mod_eq_of_lt h_lr2_lt,
            Nat.mod_eq_of_lt h_lr3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr1_val, h_lr2_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1 ha2 ha3 ha2_raw ha3_raw hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb_zero h_msb_u16 h_msb_false
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha2_form : air.cols.values.a_2 row 0
                      = air.cols.values.limb_result_3 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha2_raw, hbm1, h_sra_msb]; ring
        have ha3 : air.cols.values.a_3 row 0 = (65535 : FKB) := by
          rw [ha3_raw, hbm1]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha2_val : (air.cols.values.a_2 row 0).val
                     = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha2_form, Fin.val_add, h_diff_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.limb_result_3 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha2_lt : (air.cols.values.a_2 row 0).val < 65536 := by
          rw [ha2_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have ha3_val : (air.cols.values.a_3 row 0).val = 65535 := by
          rw [ha3]; decide
        have ha3_lt : (air.cols.values.a_3 row 0).val < 65536 := by
          rw [ha3_val]; decide
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure,
                   ha0, ha1]
        refine ⟨⟨h_lr1_lt, h_lr2_lt, ha2_lt, ha3_lt⟩, ?_⟩
        apply BitVec.eq_of_toNat_eq
        have h_msb_true : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                         air.cols.values.b_1 row 0,
                                         air.cols.values.b_2 row 0,
                                         air.cols.values.b_3 row 0]).msb = true := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_true]
        have h_b_toNat_lt : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                           air.cols.values.b_1 row 0,
                                           air.cols.values.b_2 row 0,
                                           air.cols.values.b_3 row 0]).toNat < 2^64 :=
          BitVec.isLt _
        simp only [Nat.shiftRight_eq_div_pow]
        rw [neg_one_minus_div _ _ 64 (by
          have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                air.cols.values.c_for_lookup_1 row 0,
                                air.cols.values.c_for_lookup_2 row 0,
                                air.cols.values.c_for_lookup_3 row 0]).toNat % 64 < 64 :=
            Nat.mod_lt _ (by decide)
          omega) h_b_toNat_lt]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr1_lt, Nat.mod_eq_of_lt h_lr2_lt,
            Nat.mod_eq_of_lt ha2_lt, Nat.mod_eq_of_lt ha3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr1_val, h_lr2_val, ha2_val, ha3_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt ha2_lt ha3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b h_msb_u16 h_msb_true
              h_b_toNat_lt
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1 ha2_raw ha2_form ha2_val ha3 ha3_raw ha3_val
              hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb h_diff_val hv_val
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=1, c4=0): shift_u16_2 = 1, shift = k_nat + 32.
    -- a_0 = lr_2, a_1 = lr_3 + boundary, a_2 = b_msb · 65535, a_3 = b_msb · 65535.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
        rcases h_su3_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 1 := by
        rw [hsu0, hsu1, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su2_a0 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha1_raw : air.cols.values.a_1 row 0
                      = air.cols.values.limb_result_3 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su2_a1 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha2_raw : air.cols.values.a_2 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su2_a2 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha3_raw : air.cols.values.a_3 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su2_a3 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 1 * 32 : FKB).val = k_nat + 32 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 32 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h32 : ((32 : FKB)).val = 32 := by decide
        rw [h32]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
              = k_nat + 32 := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rcases h_b_msb with ⟨hbm0, hb3_lt⟩ | ⟨hbm1, hb3_ge⟩
      . -- b_msb = 0 sub-case
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_3 row 0 := by
          rw [ha1_raw, hbm0, h_sra_msb_zero]; ring
        have ha2 : air.cols.values.a_2 row 0 = 0 := by
          rw [ha2_raw, hbm0]; ring
        have ha3 : air.cols.values.a_3 row 0 = 0 := by
          rw [ha3_raw, hbm0]; ring
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure,
                   ha0, ha1, ha2, ha3]
        refine ⟨⟨h_lr2_lt, h_lr3_lt, ?_, ?_⟩, ?_⟩
        . simp
        . simp
        apply BitVec.eq_of_toNat_eq
        have h_msb_false : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                          air.cols.values.b_1 row 0,
                                          air.cols.values.b_2 row 0,
                                          air.cols.values.b_3 row 0]).msb = false := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_false]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt h_lr3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr2_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1 ha2 ha3 ha1_raw ha2_raw ha3_raw hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb_zero h_msb_u16 h_msb_false
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha1_form : air.cols.values.a_1 row 0
                      = air.cols.values.limb_result_3 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha1_raw, hbm1, h_sra_msb]; ring
        have ha2 : air.cols.values.a_2 row 0 = (65535 : FKB) := by
          rw [ha2_raw, hbm1]; ring
        have ha3 : air.cols.values.a_3 row 0 = (65535 : FKB) := by
          rw [ha3_raw, hbm1]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha1_val : (air.cols.values.a_1 row 0).val
                     = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha1_form, Fin.val_add, h_diff_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.limb_result_3 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by
          rw [ha1_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have ha2_val : (air.cols.values.a_2 row 0).val = 65535 := by rw [ha2]; decide
        have ha3_val : (air.cols.values.a_3 row 0).val = 65535 := by rw [ha3]; decide
        have ha2_lt : (air.cols.values.a_2 row 0).val < 65536 := by rw [ha2_val]; decide
        have ha3_lt : (air.cols.values.a_3 row 0).val < 65536 := by rw [ha3_val]; decide
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, ha0]
        refine ⟨⟨h_lr2_lt, ha1_lt, ha2_lt, ha3_lt⟩, ?_⟩
        apply BitVec.eq_of_toNat_eq
        have h_msb_true : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                         air.cols.values.b_1 row 0,
                                         air.cols.values.b_2 row 0,
                                         air.cols.values.b_3 row 0]).msb = true := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_true]
        have h_b_toNat_lt : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                           air.cols.values.b_1 row 0,
                                           air.cols.values.b_2 row 0,
                                           air.cols.values.b_3 row 0]).toNat < 2^64 :=
          BitVec.isLt _
        simp only [Nat.shiftRight_eq_div_pow]
        rw [neg_one_minus_div _ _ 64 (by
          have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                air.cols.values.c_for_lookup_1 row 0,
                                air.cols.values.c_for_lookup_2 row 0,
                                air.cols.values.c_for_lookup_3 row 0]).toNat % 64 < 64 :=
            Nat.mod_lt _ (by decide)
          omega) h_b_toNat_lt]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr2_lt, Nat.mod_eq_of_lt ha1_lt,
            Nat.mod_eq_of_lt ha2_lt, Nat.mod_eq_of_lt ha3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr2_val, ha1_val, ha2_val, ha3_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt ha1_lt ha2_lt ha3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b h_msb_u16 h_msb_true
              h_b_toNat_lt
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1_raw ha1_form ha1_val ha2 ha2_raw ha2_val ha3 ha3_raw ha3_val
              hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb h_diff_val hv_val
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=1, c4=1): shift_u16_3 = 1, shift = k_nat + 48.
    -- a_0 = lr_3 + boundary, a_1 = a_2 = a_3 = b_msb · 65535.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
        rcases h_su2_sel with h | h
        . exact h
        . rw [hcb4, hcb5] at h; exact absurd h (by decide)
      have hsu3 : air.cols.values.shift_u16_3 row 0 = 1 := by
        rw [hsu0, hsu1, hsu2] at h_su_sum; linear_combination h_su_sum
      have ha0_raw : air.cols.values.a_0 row 0
                      = air.cols.values.limb_result_3 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su3_a0 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      have ha1_raw : air.cols.values.a_1 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su3_a1 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      have ha2_raw : air.cols.values.a_2 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su3_a2 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      have ha3_raw : air.cols.values.a_3 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su3_a3 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 1 * 32 : FKB).val = k_nat + 48 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 48 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h48 : ((48 : FKB)).val = 48 := by decide
        rw [h48]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_c_sum_mod_64 :
          ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
              = k_nat + 48 := by
        have heq : ((air.cols.values.c_for_lookup_0 row 0).val
            + (air.cols.values.c_for_lookup_1 row 0).val * 65536
            + (air.cols.values.c_for_lookup_2 row 0).val * 4294967296
            + (air.cols.values.c_for_lookup_3 row 0).val * 281474976710656) % 64
            = (air.cols.values.c_for_lookup_0 row 0).val % 64 := by omega
        rw [heq]; exact h_cfl0_mod64
      rcases h_b_msb with ⟨hbm0, hb3_lt⟩ | ⟨hbm1, hb3_ge⟩
      . -- b_msb = 0 sub-case
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_3 row 0 := by
          rw [ha0_raw, hbm0, h_sra_msb_zero]; ring
        have ha1 : air.cols.values.a_1 row 0 = 0 := by
          rw [ha1_raw, hbm0]; ring
        have ha2 : air.cols.values.a_2 row 0 = 0 := by
          rw [ha2_raw, hbm0]; ring
        have ha3 : air.cols.values.a_3 row 0 = 0 := by
          rw [ha3_raw, hbm0]; ring
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure,
                   ha0, ha1, ha2, ha3]
        refine ⟨⟨h_lr3_lt, ?_, ?_, ?_⟩, ?_⟩
        . simp
        . simp
        . simp
        apply BitVec.eq_of_toNat_eq
        have h_msb_false : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                          air.cols.values.b_1 row 0,
                                          air.cols.values.b_2 row 0,
                                          air.cols.values.b_3 row 0]).msb = false := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_false]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt h_lr3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0 ha1 ha2 ha3 ha0_raw ha1_raw ha2_raw ha3_raw hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb_zero h_msb_u16 h_msb_false
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha0_form : air.cols.values.a_0 row 0
                      = air.cols.values.limb_result_3 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha0_raw, hbm1, h_sra_msb]; ring
        have ha1 : air.cols.values.a_1 row 0 = (65535 : FKB) := by
          rw [ha1_raw, hbm1]; ring
        have ha2 : air.cols.values.a_2 row 0 = (65535 : FKB) := by
          rw [ha2_raw, hbm1]; ring
        have ha3 : air.cols.values.a_3 row 0 = (65535 : FKB) := by
          rw [ha3_raw, hbm1]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha0_val : (air.cols.values.a_0 row 0).val
                     = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha0_form, Fin.val_add, h_diff_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.limb_result_3 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.limb_result_3 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by
          rw [ha0_val]
          have h_lr3_le : (air.cols.values.limb_result_3 row 0).val < 2^(16-k_nat) := by
            rw [h_lr3_val]; exact h_hi3
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have ha1_val : (air.cols.values.a_1 row 0).val = 65535 := by rw [ha1]; decide
        have ha2_val : (air.cols.values.a_2 row 0).val = 65535 := by rw [ha2]; decide
        have ha3_val : (air.cols.values.a_3 row 0).val = 65535 := by rw [ha3]; decide
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1_val]; decide
        have ha2_lt : (air.cols.values.a_2 row 0).val < 65536 := by rw [ha2_val]; decide
        have ha3_lt : (air.cols.values.a_3 row 0).val < 65536 := by rw [ha3_val]; decide
        simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure]
        refine ⟨⟨ha0_lt, ha1_lt, ha2_lt, ha3_lt⟩, ?_⟩
        apply BitVec.eq_of_toNat_eq
        have h_msb_true : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                         air.cols.values.b_1 row 0,
                                         air.cols.values.b_2 row 0,
                                         air.cols.values.b_3 row 0]).msb = true := by
          rw [BitVec.msb_eq_decide, U64w.toBV_toNat]
          simp [U64w.toNat,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
          omega
        rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_true]
        have h_b_toNat_lt : (U64w.toBV #v[air.cols.values.b_0 row 0,
                                           air.cols.values.b_1 row 0,
                                           air.cols.values.b_2 row 0,
                                           air.cols.values.b_3 row 0]).toNat < 2^64 :=
          BitVec.isLt _
        simp only [Nat.shiftRight_eq_div_pow]
        rw [neg_one_minus_div _ _ 64 (by
          have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                air.cols.values.c_for_lookup_1 row 0,
                                air.cols.values.c_for_lookup_2 row 0,
                                air.cols.values.c_for_lookup_3 row 0]).toNat % 64 < 64 :=
            Nat.mod_lt _ (by decide)
          omega) h_b_toNat_lt]
        simp [U64w.toNat]
        rw [Nat.mod_eq_of_lt ha0_lt, Nat.mod_eq_of_lt ha1_lt,
            Nat.mod_eq_of_lt ha2_lt, Nat.mod_eq_of_lt ha3_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
            Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
        rw [h_c_sum_mod_64, ha0_val, ha1_val, ha2_val, ha3_val, h_lr3_val,
            h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt ha0_lt ha1_lt ha2_lt ha3_lt
              h_sra_msb_v0123 h_srw_msb_zero h_b_msb_b h_msb_u16 h_msb_true
              h_b_toNat_lt
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
              h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
              h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
              h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
              ha0_raw ha0_form ha0_val ha1 ha1_raw ha1_val
              ha2 ha2_raw ha2_val ha3 ha3_raw ha3_val
              hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_64 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_sra_msb h_diff_val hv_val
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega

  -- =====================================================================
  -- spec_SRLW — opcode 43 (32-bit logical right shift, sign-extended to
  -- 64 via `srw_msb = MSB(a_1)`).
  --
  -- For SRLW, `b_msb` is forced to 0 by constraint 32
  -- (`(is_srl + is_srlw) · b_msb = 0`), so the 32-bit shift has no
  -- sign-extension within itself — only the post-shift extension from
  -- 32 → 64 bits via `srw_msb`. We case-split on (c_bits_4, c_bits_5)
  -- (4 cases); c_bits_5 only contributes to `c mod 64`, not to the
  -- 5-bit shift dispatch, so cases (c5=*, c4=0) share the `shift_u16_0`
  -- branch and (c5=*, c4=1) share the `shift_u16_1` branch.
  --
  -- The 64-bit result is built by the `U32w.extend` bridge:
  -- `U64w.toBV #v[a_0, a_1, srw_msb·65535, srw_msb·65535]`
  --   = `(U32w.extend #v[a_0, a_1] true).toBV`
  --   = `sign_extend 64 (U32w.toBV #v[a_0, a_1])`
  --   = `sign_extend 64 (BitVec.ushiftRight (b.setWidth 32) (c.toNat % 32))`.
  -- =====================================================================

  lemma spec_SRLW
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_srl : air.cols.values.is_srl row 0 = 0)
    (h_is_sra : air.cols.values.is_sra row 0 = 0)
    (h_is_srlw : air.cols.values.is_srlw row 0 = 1)
    (h_is_sraw : air.cols.values.is_sraw row 0 = 0)
  :
    ALUBus.Spec
      43
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    -- Step 1: is_real = 1.
    have h_is_real :
      air.cols.values.is_srl row 0 + air.cols.values.is_sra row 0 +
      air.cols.values.is_srlw row 0 + air.cols.values.is_sraw row 0 = 1
      := by rw [h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]; ring
    -- Step 2: u16 bounds.
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Step 3: Byte-bus assumptions.
    --   With is_srlw = 1, others = 0: 9 BitRange + U16Range on a_1 fire.
    --   The b_msb-on-b_3 (is_sra=0) and b_msb-on-b_1 (is_sraw=0) entries are vacuous.
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_wf
    obtain ⟨h_c_decomp,
            ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, ⟨_, h_hi3⟩,
            h_srw_msb_u16⟩ := h_wf
    -- Step 4: Extract constraints (post-simp with selectors).
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_srl, h_is_sra, h_is_srlw, h_is_sraw] at h_constraints
    obtain ⟨_, _h_imm_c_b, _h_w_imm,
            h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_v01, h_v012, h_v0123,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b,
            h_su2_sel, h_su2_b, h_su3_sel, h_su3_b,
            h_su_sum,
            h_lr0, h_lr1, h_lr2, h_lr3,
            _h_b_msb_b, h_b_msb_zero, h_sra_msb_v0123,
            h_srw_msb_b,
            h_su0_a0, h_su0_a1,
            h_su1_a0, h_su1_a1,
            h_a2_msb, h_a3_msb,
            h_c_eq,
            h_b_carry_0, h_b_carry_1, h_b_carry_2, h_b_carry_3⟩ := h_constraints
    -- Step 5: Derive `v_0123 = 2^(16-k)` and `k ≤ 15`.
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow_inv _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: Byte-bus bounds in Nat form.
    rw [hs4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [h16s4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(16 - k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: Per-limb b-decomposition (we only need b_0, b_1 for 32-bit ops).
    have h_decomp_0 : (air.cols.values.b_0 row 0).val
        = (air.cols.values.higher_limb_0 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_0 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi0 h_lo0 hv h_b_carry_0
    have h_decomp_1 : (air.cols.values.b_1 row 0).val
        = (air.cols.values.higher_limb_1 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_1 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi1 h_lo1 hv h_b_carry_1
    -- Step 8: limb_result_0 value & bound (only the low limb of the shift result).
    rw [hv] at h_lr0
    have h_lr0_val := lr_val_lift _ _ k_nat hk_le h_hi0 h_lo1
    rw [← h_lr0] at h_lr0_val
    have hpow_prod : (2^k_nat : ℕ) * 2^(16-k_nat) = 2^16 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : k_nat ≤ 16)]
    have hpow_le16 : (2^(16 - k_nat) : ℕ) ≤ 2^16 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h_lr0_lt : (air.cols.values.limb_result_0 row 0).val < 65536 := by
      rw [h_lr0_val]
      have h1 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_1 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    -- Step 9: shift_u16_2 = shift_u16_3 = 0 always (c_bits_4 ∈ {0,1} can't equal 2 or 3).
    have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
      rcases h_su2_sel with h | h
      . exact h
      . rcases h_cb4_b with hcb | hcb <;> rw [hcb] at h <;> exact absurd h (by decide)
    have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
      rcases h_su3_sel with h | h
      . exact h
      . rcases h_cb4_b with hcb | hcb <;> rw [hcb] at h <;> exact absurd h (by decide)
    -- Step 10: Case-split on (c_bits_5, c_bits_4).
    rcases h_cb5_b with hcb5 | hcb5 <;> rcases h_cb4_b with hcb4 | hcb4
    -- =============================================================
    -- Case (c5=0, c4=0): shift_u16_0 = 1, shift mod 32 = k_nat.
    -- =============================================================
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
        rw [h_sra_msb_v0123, h_b_msb_zero]; ring
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su0_a0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.higher_limb_1 row 0 := by
        rcases h_su0_a1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by
        rw [ha1]
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      -- U16MSBGadget for srw_msb on a_1.
      have h_gadget_wf :
          bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                          (air.cols.values.srw_msb.msb row 0)) := by
        simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
        exact h_srw_msb_u16
      have h_gadget_cstr :
          U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
        refine ⟨by ring, ?_⟩
        rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
      have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
      -- c.val mod 64 = k_nat → c.val mod 32 = k_nat.
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 0 * 32 : FKB).val = k_nat := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) := by ring
        rw [heq, hs4_val]
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      -- ALUBus.Spec for opcode 43.
      simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure, Sail.shift_bits_right,
                 ha0, ha1, h_a2_msb, h_a3_msb]
      refine ⟨⟨h_lr0_lt, h_hi1_lt, ?_, ?_⟩, ?_⟩
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      -- BitVec identity via U32w.extend bridge.
      trans (U32w.extend
              #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                 BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)] true).toBV
      . simp [U32w.extend, U32w.ext]
        suffices h_msb_eq :
            BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
              if U32w.negative
                  #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                     BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)]
              then 65535#16 else 0#16 by
          congr
        simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
        rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
        . rw [hmsb]; simp
          rw [ha1] at ha_lt
          have : (air.cols.values.higher_limb_1 row 0).val < 32768 := ha_lt
          omega
        . rw [hmsb]; simp
          rw [ha1] at ha_ge
          have : 32768 ≤ (air.cols.values.higher_limb_1 row 0).val := ha_ge
          omega
      . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [-BitVec.toNat_ushiftRight]
        rw [BitVec.toNat_ushiftRight]
        simp [U32w.toNat]
        rw [Nat.mod_eq_of_lt h_lr0_lt,
            Nat.mod_eq_of_lt h_hi1_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
        have h_c_sum_mod_32 :
            ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat := by
          have heq : ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
              = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
          rw [heq]
          have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := h_cfl0_mod64
          omega
        rw [h_c_sum_mod_32, h_lr0_val, h_decomp_0, h_decomp_1]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt
              h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
              h_b_msb_zero h_sra_msb_zero
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm _h_b_msb_b
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
              h_a2_msb h_a3_msb
              ha0 ha1 ha1_lt hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_gadget_wf h_gadget_cstr
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=0, c4=1): shift_u16_1 = 1, shift mod 32 = k_nat + 16.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 1 := by
        rw [hsu0, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
        rw [h_sra_msb_v0123, h_b_msb_zero]; ring
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.higher_limb_1 row 0 := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha1 : air.cols.values.a_1 row 0 = 0 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by rw [ha0]; exact h_hi1_lt
      have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; decide
      -- U16MSBGadget on a_1 → srw_msb = 0 (since a_1 = 0).
      have h_gadget_wf :
          bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                          (air.cols.values.srw_msb.msb row 0)) := by
        simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
        exact h_srw_msb_u16
      have h_gadget_cstr :
          U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
        refine ⟨by ring, ?_⟩
        rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
      have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 0 * 32 : FKB).val = k_nat + 16 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 16 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h16 : ((16 : FKB)).val = 16 := by decide
        rw [h16]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure, Sail.shift_bits_right,
                 ha0, ha1, h_a2_msb, h_a3_msb]
      refine ⟨⟨h_hi1_lt, ?_, ?_, ?_⟩, ?_⟩
      . simp
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      trans (U32w.extend
              #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                 (0 : BitVec 16)] true).toBV
      . suffices h_msb_eq :
            BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
              if U32w.negative
                  #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                     (0 : BitVec 16)]
              then 65535#16 else 0#16 by
          simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
        simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
        rcases h_msb_iff with ⟨hmsb, _⟩ | ⟨hmsb, ha_ge⟩
        . rw [hmsb]; simp
        . rw [ha1] at ha_ge; simp at ha_ge
      . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [-BitVec.toNat_ushiftRight]
        rw [BitVec.toNat_ushiftRight]
        simp [U32w.toNat]
        rw [Nat.mod_eq_of_lt h_hi1_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
        have h_c_sum_mod_32 :
            ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat + 16 := by
          have heq : ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
              = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
          rw [heq]
          have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := h_cfl0_mod64
          omega
        rw [h_c_sum_mod_32, h_decomp_0, h_decomp_1]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt
              h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
              h_b_msb_zero h_sra_msb_zero
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm _h_b_msb_b
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
              h_a2_msb h_a3_msb
              ha0 ha1 ha0_lt ha1_lt hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_gadget_wf h_gadget_cstr
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=1, c4=0): shift_u16_0 = 1, shift mod 32 = k_nat.
    -- (c.val mod 64 = k_nat + 32; c_bits_5 contributes 32 but is stripped by mod 32.)
    -- =============================================================
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
        rw [h_sra_msb_v0123, h_b_msb_zero]; ring
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su0_a0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.higher_limb_1 row 0 := by
        rcases h_su0_a1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by
        rw [ha1]
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      have h_gadget_wf :
          bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                          (air.cols.values.srw_msb.msb row 0)) := by
        simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
        exact h_srw_msb_u16
      have h_gadget_cstr :
          U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
        refine ⟨by ring, ?_⟩
        rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
      have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 1 * 32 : FKB).val = k_nat + 32 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 32 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h32 : ((32 : FKB)).val = 32 := by decide
        rw [h32]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure, Sail.shift_bits_right,
                 ha0, ha1, h_a2_msb, h_a3_msb]
      refine ⟨⟨h_lr0_lt, h_hi1_lt, ?_, ?_⟩, ?_⟩
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      trans (U32w.extend
              #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                 BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)] true).toBV
      . suffices h_msb_eq :
            BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
              if U32w.negative
                  #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                     BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)]
              then 65535#16 else 0#16 by
          simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
        simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
        rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
        . rw [hmsb]; simp
          rw [ha1] at ha_lt
          have : (air.cols.values.higher_limb_1 row 0).val < 32768 := ha_lt
          omega
        . rw [hmsb]; simp
          rw [ha1] at ha_ge
          have : 32768 ≤ (air.cols.values.higher_limb_1 row 0).val := ha_ge
          omega
      . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [-BitVec.toNat_ushiftRight]
        rw [BitVec.toNat_ushiftRight]
        simp [U32w.toNat]
        have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
          have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
          omega
        rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_hi1_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
        have h_c_sum_mod_32 :
            ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat := by
          have heq : ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
              = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
          rw [heq]
          have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := h_cfl0_mod64
          omega
        rw [h_c_sum_mod_32, h_lr0_val, h_decomp_0, h_decomp_1]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt
              h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
              h_b_msb_zero h_sra_msb_zero
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm _h_b_msb_b
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
              h_a2_msb h_a3_msb
              ha0 ha1 ha1_lt hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_gadget_wf h_gadget_cstr
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=1, c4=1): shift_u16_1 = 1, shift mod 32 = k_nat + 16.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 1 := by
        rw [hsu0, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
        rw [h_sra_msb_v0123, h_b_msb_zero]; ring
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.higher_limb_1 row 0 := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . rw [h_b_msb_zero, h_sra_msb_zero] at h
          simp at h; exact h
      have ha1 : air.cols.values.a_1 row 0 = 0 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . rw [h_b_msb_zero] at h; simp at h; exact h
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by rw [ha0]; exact h_hi1_lt
      have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; decide
      have h_gadget_wf :
          bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                          (air.cols.values.srw_msb.msb row 0)) := by
        simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
        exact h_srw_msb_u16
      have h_gadget_cstr :
          U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
        refine ⟨by ring, ?_⟩
        rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
      have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 1 * 32 : FKB).val = k_nat + 48 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 48 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h48 : ((48 : FKB)).val = 48 := by decide
        rw [h48]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure, Sail.shift_bits_right,
                 ha0, ha1, h_a2_msb, h_a3_msb]
      refine ⟨⟨h_hi1_lt, ?_, ?_, ?_⟩, ?_⟩
      . simp
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
      trans (U32w.extend
              #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                 (0 : BitVec 16)] true).toBV
      . suffices h_msb_eq :
            BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
              if U32w.negative
                  #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                     (0 : BitVec 16)]
              then 65535#16 else 0#16 by
          simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
        simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
        rcases h_msb_iff with ⟨hmsb, _⟩ | ⟨hmsb, ha_ge⟩
        . rw [hmsb]; simp
        . rw [ha1] at ha_ge; simp at ha_ge
      . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [-BitVec.toNat_ushiftRight]
        rw [BitVec.toNat_ushiftRight]
        simp [U32w.toNat]
        rw [Nat.mod_eq_of_lt h_hi1_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
        have h_c_sum_mod_32 :
            ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat + 16 := by
          have heq : ((air.cols.values.c_for_lookup_0 row 0).val
              + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
              = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
          rw [heq]
          have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := h_cfl0_mod64
          omega
        rw [h_c_sum_mod_32, h_decomp_0, h_decomp_1]
        clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt
              h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
              h_b_msb_zero h_sra_msb_zero
              h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
              _h_imm_c_b _h_w_imm _h_b_msb_b
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
              h_a2_msb h_a3_msb
              ha0 ha1 ha0_lt ha1_lt hsu0 hsu1 hsu2 hsu3
              h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
              h_gadget_wf h_gadget_cstr
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega

  -- =====================================================================
  -- spec_SRAW — opcode 44 (32-bit arithmetic right shift, sign-extended
  -- to 64 via `srw_msb = MSB(a_1)`).
  --
  -- Combines the SRA pattern (sign-ext within the 32-bit shift via
  -- `b_msb = MSB(b_1)`, the U16MSB gadget on `b_1` gated by `is_sraw`)
  -- with the W-variant 32 → 64 sign-extension via `srw_msb`. We case-split
  -- on (c_bits_4, c_bits_5) (4 cases) and within each on `b_msb ∈ {0, 1}`
  -- (8 sub-cases total).
  --
  -- - `b_msb = 0`: MSB(b32) is false → `BitVec.sshiftRight = ushiftRight`,
  --                same as the SRLW case for the inner 32-bit shift.
  -- - `b_msb = 1`: MSB(b32) is true → use `BitVec.toNat_sshiftRight_of_msb_true`
  --                + `neg_one_minus_div` with `w = 32` to bridge to the
  --                chip's `(b_msb · 65536 - sra_msb_v0123)` boundary
  --                correction and `b_msb · 65535` fillers.
  --
  -- The 64-bit result uses the same `U32w.extend` bridge as SRLW; the
  -- inner 32-bit equality is closed by `suffices h_eq : U32w.toBV [a_0, a_1]
  --   = (U32w.toBV [b_0, b_1]).sshiftRight (c.toNat % 32)`.
  -- =====================================================================

  lemma spec_SRAW
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_srl : air.cols.values.is_srl row 0 = 0)
    (h_is_sra : air.cols.values.is_sra row 0 = 0)
    (h_is_srlw : air.cols.values.is_srlw row 0 = 0)
    (h_is_sraw : air.cols.values.is_sraw row 0 = 1)
  :
    ALUBus.Spec
      44
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    have h_is_real :
      air.cols.values.is_srl row 0 + air.cols.values.is_sra row 0 +
      air.cols.values.is_srlw row 0 + air.cols.values.is_sraw row 0 = 1
      := by rw [h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]; ring
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- h_wf: 9 BitRange + U16MSB on b_1 (is_sraw=1) + U16MSB on a_1 (is_srlw + is_sraw = 1).
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_wf
    obtain ⟨h_c_decomp,
            ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, ⟨_, h_hi3⟩,
            h_b_msb_u16, h_srw_msb_u16⟩ := h_wf
    -- Step 4: constraints (b_msb_zero and srw_msb_zero both trivialize for SRAW).
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_srl, h_is_sra, h_is_srlw, h_is_sraw] at h_constraints
    obtain ⟨_, _h_imm_c_b, _h_w_imm,
            h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_v01, h_v012, h_v0123,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b,
            h_su2_sel, h_su2_b, h_su3_sel, h_su3_b,
            h_su_sum,
            h_lr0, h_lr1, h_lr2, h_lr3,
            h_b_msb_b, h_sra_msb_v0123,
            h_srw_msb_b,
            h_su0_a0, h_su0_a1,
            h_su1_a0, h_su1_a1,
            h_a2_msb, h_a3_msb,
            h_c_eq,
            h_b_carry_0, h_b_carry_1, h_b_carry_2, h_b_carry_3⟩ := h_constraints
    -- Step 5: v_0123 cascade, k_nat ≤ 15.
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow_inv _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: byte-bus bounds.
    rw [hs4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [h16s4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(16 - k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: b-decomposition (b_0 and b_1 used for 32-bit ops).
    have h_decomp_0 : (air.cols.values.b_0 row 0).val
        = (air.cols.values.higher_limb_0 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_0 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi0 h_lo0 hv h_b_carry_0
    have h_decomp_1 : (air.cols.values.b_1 row 0).val
        = (air.cols.values.higher_limb_1 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_1 row 0).val :=
      b_decomp_from_carry _ _ _ _ k_nat hk_le h_hi1 h_lo1 hv h_b_carry_1
    -- Step 8: limb_result_0 value & bounds.
    rw [hv] at h_lr0
    have h_lr0_val := lr_val_lift _ _ k_nat hk_le h_hi0 h_lo1
    rw [← h_lr0] at h_lr0_val
    have hpow_prod : (2^k_nat : ℕ) * 2^(16-k_nat) = 2^16 := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega : k_nat ≤ 16)]
    have hpow_le16 : (2^(16 - k_nat) : ℕ) ≤ 2^16 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h_lr0_lt : (air.cols.values.limb_result_0 row 0).val < 65536 := by
      rw [h_lr0_val]
      have h1 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
              ≤ 2^16 - 2^(16 - k_nat) := by
        have hle : (air.cols.values.lower_limb_1 row 0).val ≤ 2^k_nat - 1 := by omega
        have h2 : (air.cols.values.lower_limb_1 row 0).val * 2^(16 - k_nat)
                ≤ (2^k_nat - 1) * 2^(16 - k_nat) := Nat.mul_le_mul_right _ hle
        have h3 : (2^k_nat - 1) * 2^(16 - k_nat) = 2^16 - 2^(16 - k_nat) := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    -- Step 9: shift_u16_2 = shift_u16_3 = 0 (c_bits_4 ∈ {0,1} can't equal 2 or 3).
    have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
      rcases h_su2_sel with h | h
      . exact h
      . rcases h_cb4_b with hcb | hcb <;> rw [hcb] at h <;> exact absurd h (by decide)
    have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
      rcases h_su3_sel with h | h
      . exact h
      . rcases h_cb4_b with hcb | hcb <;> rw [hcb] at h <;> exact absurd h (by decide)
    -- Step 10: b_msb partition via U16MSBGadget on b_1.
    have h_b_msb : (air.cols.values.b_msb.msb row 0 = 0 ∧
                    (air.cols.values.b_1 row 0).val < 32768) ∨
                   (air.cols.values.b_msb.msb row 0 = 1 ∧
                    32768 ≤ (air.cols.values.b_1 row 0).val) := by
      rcases h_b_msb_b with hm | hm
      . left; refine ⟨hm, ?_⟩; rw [hm] at h_b_msb_u16; grind
      . right; refine ⟨hm, ?_⟩; rw [hm] at h_b_msb_u16; grind
    -- Step 11: Case-split on (c_bits_5, c_bits_4).
    rcases h_cb5_b with hcb5 | hcb5 <;> rcases h_cb4_b with hcb4 | hcb4
    -- =============================================================
    -- Case (c5=0, c4=0): shift_u16_0 = 1, shift mod 32 = k_nat.
    -- =============================================================
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su0_a0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1_raw : air.cols.values.a_1 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su0_a1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 0 * 32 : FKB).val = k_nat := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) := by ring
        rw [heq, hs4_val]
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      rcases h_b_msb with ⟨hbm0, hb1_lt⟩ | ⟨hbm1, hb1_ge⟩
      . -- b_msb = 0 sub-case (MSB(b32) = false, no sign-ext within 32-bit shift).
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha1 : air.cols.values.a_1 row 0 = air.cols.values.higher_limb_1 row 0 := by
          rw [ha1_raw, hbm0, h_sra_msb_zero]; ring
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; exact h_hi1_lt
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   ha0, ha1, h_a2_msb, h_a3_msb]
        refine ⟨⟨h_lr0_lt, h_hi1_lt, ?_, ?_⟩, ?_⟩
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                       BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
            rw [ha1] at ha_lt
            have : (air.cols.values.higher_limb_1 row 0).val < 32768 := ha_lt
            omega
          . rw [hmsb]; simp
            rw [ha1] at ha_ge
            have : 32768 ≤ (air.cols.values.higher_limb_1 row 0).val := ha_ge
            omega
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          congr 1
          have h_msb_b32_false : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                air.cols.values.b_1 row 0]).msb = false := by
            rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
            simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
            omega
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_b32_false]
          simp [U32w.toNat]
          rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_hi1_lt,
              Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
              Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
          have h_c_sum_mod_32 :
              ((air.cols.values.c_for_lookup_0 row 0).val
                + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat := by
            have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
            rw [heq]
            have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := h_cfl0_mod64
            omega
          rw [h_c_sum_mod_32, h_lr0_val, h_decomp_0, h_decomp_1]
          clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                h_lr0_lt h_hi1_lt
                h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                h_b_msb_b h_b_msb_u16 h_sra_msb_zero h_msb_b32_false
                h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                _h_imm_c_b _h_w_imm
                h_su0_sel h_su0_b h_su1_sel h_su1_b
                h_su2_sel h_su2_b h_su3_sel h_su3_b
                h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                h_a2_msb h_a3_msb
                ha0 ha1 ha1_lt ha1_raw hsu0 hsu1 hsu2 hsu3
                h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                h_gadget_wf h_gadget_cstr
          have hk_le' : k_nat ≤ 15 := hk_le
          interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case (MSB(b32) = true, sign-ext within 32-bit shift).
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha1_form : air.cols.values.a_1 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha1_raw, hbm1, h_sra_msb]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha1_val : (air.cols.values.a_1 row 0).val
                     = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha1_form, Fin.val_add, h_diff_val]
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.higher_limb_1 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by
          rw [ha1_val]
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   ha0, h_a2_msb, h_a3_msb]
        refine ⟨⟨h_lr0_lt, ha1_lt, ?_, ?_⟩, ?_⟩
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                       BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
            have : (air.cols.values.a_1 row 0).val < 32768 := ha_lt
            omega
          . rw [hmsb]; simp
            have : 32768 ≤ (air.cols.values.a_1 row 0).val := ha_ge
            omega
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          suffices h_eq :
            U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
              = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                  (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . have h_msb_b32_true : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                air.cols.values.b_1 row 0]).msb = true := by
              rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
              simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
              omega
            have h_b32_toNat_lt : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                air.cols.values.b_1 row 0]).toNat < 2^32 :=
              BitVec.isLt _
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_b32_true]
            simp only [Nat.shiftRight_eq_div_pow]
            rw [neg_one_minus_div _ _ 32 (by
              have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                    air.cols.values.c_for_lookup_1 row 0,
                                    air.cols.values.c_for_lookup_2 row 0,
                                    air.cols.values.c_for_lookup_3 row 0]).toNat % 32 < 32 :=
                Nat.mod_lt _ (by decide)
              omega) h_b32_toNat_lt]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt ha1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := h_cfl0_mod64
              omega
            have h_c64_mod_32 : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                                air.cols.values.c_for_lookup_1 row 0,
                                                air.cols.values.c_for_lookup_2 row 0,
                                                air.cols.values.c_for_lookup_3 row 0]).toNat % 32
                              = k_nat := by
              simp [U64w.toNat, Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1,
                    Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hc3]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, ha1_val, h_lr0_val, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt ha1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb h_diff_val hv_val
                  h_msb_b32_true h_b32_toNat_lt
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0 ha1_raw ha1_form ha1_val hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr h_c64_mod_32
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=0, c4=1): shift_u16_1 = 1, shift mod 32 = k_nat + 16.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 1 := by
        rw [hsu0, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0_raw : air.cols.values.a_0 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha1_raw : air.cols.values.a_1 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 0 * 32 : FKB).val = k_nat + 16 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 16 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h16 : ((16 : FKB)).val = 16 := by decide
        rw [h16]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      rcases h_b_msb with ⟨hbm0, hb1_lt⟩ | ⟨hbm1, hb1_ge⟩
      . -- b_msb = 0 sub-case
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha0 : air.cols.values.a_0 row 0 = air.cols.values.higher_limb_1 row 0 := by
          rw [ha0_raw, hbm0, h_sra_msb_zero]; ring
        have ha1 : air.cols.values.a_1 row 0 = 0 := by
          rw [ha1_raw, hbm0]; ring
        have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by rw [ha0]; exact h_hi1_lt
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; decide
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   ha0, ha1, h_a2_msb, h_a3_msb]
        refine ⟨⟨h_hi1_lt, ?_, ?_, ?_⟩, ?_⟩
        . simp
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                   (0 : BitVec 16)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                       (0 : BitVec 16)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, _⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
          . rw [ha1] at ha_ge; simp at ha_ge
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          have h_msb_b32_false : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                air.cols.values.b_1 row 0]).msb = false := by
            rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
            simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
            omega
          suffices h_eq :
              U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                           0#16]
                = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                                BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                    (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0),
                                   BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_b32_false]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt h_hi1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat + 16 := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb_zero h_msb_b32_false
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0 ha1 ha0_lt ha1_lt ha0_raw ha1_raw hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha0_form : air.cols.values.a_0 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha0_raw, hbm1, h_sra_msb]; ring
        have ha1 : air.cols.values.a_1 row 0 = (65535 : FKB) := by
          rw [ha1_raw, hbm1]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha0_val : (air.cols.values.a_0 row 0).val
                     = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha0_form, Fin.val_add, h_diff_val]
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.higher_limb_1 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by
          rw [ha0_val]
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have ha1_val : (air.cols.values.a_1 row 0).val = 65535 := by rw [ha1]; decide
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1_val]; decide
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   h_a2_msb, h_a3_msb]
        refine ⟨⟨ha0_lt, ha1_lt, ?_, ?_⟩, ?_⟩
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.a_0 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.a_0 row 0),
                       BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
            have : (air.cols.values.a_1 row 0).val < 32768 := ha_lt
            omega
          . rw [hmsb]; simp
            have : 32768 ≤ (air.cols.values.a_1 row 0).val := ha_ge
            omega
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          suffices h_eq :
              U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.a_0 row 0),
                           BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                                BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                    (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0),
                                   BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . have h_msb_b32_true : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                 air.cols.values.b_1 row 0]).msb = true := by
              rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
              simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
              omega
            have h_b32_toNat_lt : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                 air.cols.values.b_1 row 0]).toNat < 2^32 :=
              BitVec.isLt _
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_b32_true]
            simp only [Nat.shiftRight_eq_div_pow]
            rw [neg_one_minus_div _ _ 32 (by
              have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                    air.cols.values.c_for_lookup_1 row 0,
                                    air.cols.values.c_for_lookup_2 row 0,
                                    air.cols.values.c_for_lookup_3 row 0]).toNat % 32 < 32 :=
                Nat.mod_lt _ (by decide)
              omega) h_b32_toNat_lt]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt ha0_lt, Nat.mod_eq_of_lt ha1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat + 16 := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 16 := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, ha0_val, ha1_val, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt ha0_lt ha1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb h_diff_val hv_val
                  h_msb_b32_true h_b32_toNat_lt
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0_raw ha0_form ha0_val ha1 ha1_raw ha1_val hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=1, c4=0): shift_u16_0 = 1, shift mod 32 = k_nat.
    -- =============================================================
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su0_a0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1_raw : air.cols.values.a_1 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su0_a1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 1 * 32 : FKB).val = k_nat + 32 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 32 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h32 : ((32 : FKB)).val = 32 := by decide
        rw [h32]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      rcases h_b_msb with ⟨hbm0, hb1_lt⟩ | ⟨hbm1, hb1_ge⟩
      . -- b_msb = 0 sub-case
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha1 : air.cols.values.a_1 row 0 = air.cols.values.higher_limb_1 row 0 := by
          rw [ha1_raw, hbm0, h_sra_msb_zero]; ring
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; exact h_hi1_lt
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   ha0, ha1, h_a2_msb, h_a3_msb]
        refine ⟨⟨h_lr0_lt, h_hi1_lt, ?_, ?_⟩, ?_⟩
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                       BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
            rw [ha1] at ha_lt
            have : (air.cols.values.higher_limb_1 row 0).val < 32768 := ha_lt
            omega
          . rw [hmsb]; simp
            rw [ha1] at ha_ge
            have : 32768 ≤ (air.cols.values.higher_limb_1 row 0).val := ha_ge
            omega
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          have h_msb_b32_false : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                air.cols.values.b_1 row 0]).msb = false := by
            rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
            simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
            omega
          suffices h_eq :
              U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                           BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0)]
                = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                                BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                    (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0),
                                   BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_b32_false]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_hi1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, h_lr0_val, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb_zero h_msb_b32_false
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0 ha1 ha1_lt ha1_raw hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha1_form : air.cols.values.a_1 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha1_raw, hbm1, h_sra_msb]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha1_val : (air.cols.values.a_1 row 0).val
                     = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha1_form, Fin.val_add, h_diff_val]
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.higher_limb_1 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by
          rw [ha1_val]
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   ha0, h_a2_msb, h_a3_msb]
        refine ⟨⟨h_lr0_lt, ha1_lt, ?_, ?_⟩, ?_⟩
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                       BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
            have : (air.cols.values.a_1 row 0).val < 32768 := ha_lt
            omega
          . rw [hmsb]; simp
            have : 32768 ≤ (air.cols.values.a_1 row 0).val := ha_ge
            omega
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          suffices h_eq :
              U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                           BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                                BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                    (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0),
                                   BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . have h_msb_b32_true : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                 air.cols.values.b_1 row 0]).msb = true := by
              rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
              simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
              omega
            have h_b32_toNat_lt : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                 air.cols.values.b_1 row 0]).toNat < 2^32 :=
              BitVec.isLt _
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_b32_true]
            simp only [Nat.shiftRight_eq_div_pow]
            rw [neg_one_minus_div _ _ 32 (by
              have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                    air.cols.values.c_for_lookup_1 row 0,
                                    air.cols.values.c_for_lookup_2 row 0,
                                    air.cols.values.c_for_lookup_3 row 0]).toNat % 32 < 32 :=
                Nat.mod_lt _ (by decide)
              omega) h_b32_toNat_lt]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt ha1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 32 := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, ha1_val, h_lr0_val, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt ha1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb h_diff_val hv_val
                  h_msb_b32_true h_b32_toNat_lt
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0 ha1_raw ha1_form ha1_val hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega
    -- =============================================================
    -- Case (c5=1, c4=1): shift_u16_1 = 1, shift mod 32 = k_nat + 16.
    -- =============================================================
    . have hsu0 : air.cols.values.shift_u16_0 row 0 = 0 := by
        rcases h_su0_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 1 := by
        rw [hsu0, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0_raw : air.cols.values.a_0 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + (air.cols.values.b_msb.msb row 0 * 65536
                          - air.cols.values.sra_msb_v0123 row 0) := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha1_raw : air.cols.values.a_1 row 0
                      = air.cols.values.b_msb.msb row 0 * 65535 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 1 * 32 : FKB).val = k_nat + 48 := by
        have heq : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 1 * 16 + 1 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) + 48 := by ring
        rw [heq, Fin.val_add, hs4_val]
        have h48 : ((48 : FKB)).val = 48 := by decide
        rw [h48]; apply Nat.mod_eq_of_lt; omega
      have hs5_le : (air.cols.values.c_bits_0 row 0
                  + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8
                  + 1 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c_mod64 := c_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c_mod64
      have h_cfl0_mod64 :
          (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := by
        rw [h_c_eq] at h_c_mod64; exact h_c_mod64
      have h_hi1_lt : (air.cols.values.higher_limb_1 row 0).val < 65536 := by
        have : (2^(16 - k_nat) : ℕ) ≤ 2^16 := hpow_le16
        omega
      rcases h_b_msb with ⟨hbm0, hb1_lt⟩ | ⟨hbm1, hb1_ge⟩
      . -- b_msb = 0 sub-case
        have h_sra_msb_zero : air.cols.values.sra_msb_v0123 row 0 = 0 := by
          rw [h_sra_msb_v0123, hbm0]; ring
        have ha0 : air.cols.values.a_0 row 0 = air.cols.values.higher_limb_1 row 0 := by
          rw [ha0_raw, hbm0, h_sra_msb_zero]; ring
        have ha1 : air.cols.values.a_1 row 0 = 0 := by
          rw [ha1_raw, hbm0]; ring
        have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by rw [ha0]; exact h_hi1_lt
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; decide
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   ha0, ha1, h_a2_msb, h_a3_msb]
        refine ⟨⟨h_hi1_lt, ?_, ?_, ?_⟩, ?_⟩
        . simp
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                   0#16] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                       0#16]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, _⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
          . rw [ha1] at ha_ge; simp at ha_ge
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          have h_msb_b32_false : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                air.cols.values.b_1 row 0]).msb = false := by
            rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
            simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
            omega
          suffices h_eq :
              U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.higher_limb_1 row 0),
                           0#16]
                = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                                BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                    (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0),
                                   BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_false h_msb_b32_false]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt h_hi1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat + 16 := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb_zero h_msb_b32_false
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0 ha1 ha0_lt ha1_lt ha0_raw ha1_raw hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega
      . -- b_msb = 1 sub-case
        have h_sra_msb : air.cols.values.sra_msb_v0123 row 0 = air.cols.values.v_0123 row 0 := by
          rw [h_sra_msb_v0123, hbm1]; ring
        have hv_val : (air.cols.values.v_0123 row 0).val = 2^(16-k_nat) := by
          rw [hv, Fin.val_natCast]; apply Nat.mod_eq_of_lt
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2^16 : ℕ) < KB_prime := by decide
          clear *- h_cb0_b h_cb1_b h_cb2_b h_cb3_b
          grind
        have ha0_form : air.cols.values.a_0 row 0
                      = air.cols.values.higher_limb_1 row 0
                        + ((65536 : FKB) - air.cols.values.v_0123 row 0) := by
          rw [ha0_raw, hbm1, h_sra_msb]; ring
        have ha1 : air.cols.values.a_1 row 0 = (65535 : FKB) := by
          rw [ha1_raw, hbm1]; ring
        have hv_le : (2^(16-k_nat) : ℕ) ≤ 65536 := by
          have : (2^(16-k_nat) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have h_diff_val : ((65536 : FKB) - air.cols.values.v_0123 row 0).val
                        = 65536 - 2^(16-k_nat) := by
          rw [Fin.sub_def]
          have h65536 : ((65536 : FKB)).val = 65536 := by decide
          rw [h65536, hv_val]
          show (KB_prime - 2^(16-k_nat) + 65536) % KB_prime = 65536 - 2^(16-k_nat)
          have hKB : (65536 : ℕ) < KB_prime := by decide
          omega
        have ha0_val : (air.cols.values.a_0 row 0).val
                     = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat) := by
          rw [ha0_form, Fin.val_add, h_diff_val]
          have hKB : (65536 : ℕ) < KB_prime := by decide
          show ((air.cols.values.higher_limb_1 row 0).val + (65536 - 2^(16-k_nat))) % KB_prime
                = (air.cols.values.higher_limb_1 row 0).val + 65536 - 2^(16-k_nat)
          omega
        have ha0_lt : (air.cols.values.a_0 row 0).val < 65536 := by
          rw [ha0_val]
          have hpow_pos : 0 < (2^(16-k_nat) : ℕ) := Nat.two_pow_pos _
          omega
        have ha1_val : (air.cols.values.a_1 row 0).val = 65535 := by rw [ha1]; decide
        have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1_val]; decide
        have h_gadget_wf :
            bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                            (air.cols.values.srw_msb.msb row 0)) := by
          simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
          exact h_srw_msb_u16
        have h_gadget_cstr :
            U16MSBGadget.AbsConstraints 1 (air.cols.values.srw_msb.msb row 0) := by
          refine ⟨by ring, ?_⟩
          rcases h_srw_msb_b with h | h <;> rw [h] <;> ring
        have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
        simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure,
                   h_a2_msb, h_a3_msb]
        refine ⟨⟨ha0_lt, ha1_lt, ?_, ?_⟩, ?_⟩
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        . rcases h_srw_msb_b with h | h <;> rw [h] <;> decide
        trans (U32w.extend
                #v[BitVec.ofNat 16 ↑(air.cols.values.a_0 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)] true).toBV
        . suffices h_msb_eq :
              BitVec.ofNat 16 ↑(air.cols.values.srw_msb.msb row 0 * 65535) =
                if U32w.negative
                    #v[BitVec.ofNat 16 ↑(air.cols.values.a_0 row 0),
                       BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                then 65535#16 else 0#16 by
            simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide, h_msb_eq]
          simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
          . rw [hmsb]; simp
            have : (air.cols.values.a_1 row 0).val < 32768 := ha_lt
            omega
          . rw [hmsb]; simp
            have : 32768 ≤ (air.cols.values.a_1 row 0).val := ha_ge
            omega
        . simp [U32w.extend_BitVec_extend, BitVec.extend, U64w.setWidth_32_eq_low_U32w]
          suffices h_eq :
              U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.a_0 row 0),
                           BitVec.ofNat 16 ↑(air.cols.values.a_1 row 0)]
                = (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                                BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)]).sshiftRight
                    (U32w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_0 row 0),
                                   BitVec.ofNat 16 ↑(air.cols.values.c_for_lookup_1 row 0)] % 32)
          . rw [h_eq]
          . have h_msb_b32_true : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                 air.cols.values.b_1 row 0]).msb = true := by
              rw [BitVec.msb_eq_decide, U32w.toBV_toNat]
              simp [U32w.toNat, Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1]
              omega
            have h_b32_toNat_lt : (U32w.toBV #v[air.cols.values.b_0 row 0,
                                                 air.cols.values.b_1 row 0]).toNat < 2^32 :=
              BitVec.isLt _
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sshiftRight_of_msb_true h_msb_b32_true]
            simp only [Nat.shiftRight_eq_div_pow]
            rw [neg_one_minus_div _ _ 32 (by
              have : (U64w.toBV #v[air.cols.values.c_for_lookup_0 row 0,
                                    air.cols.values.c_for_lookup_1 row 0,
                                    air.cols.values.c_for_lookup_2 row 0,
                                    air.cols.values.c_for_lookup_3 row 0]).toNat % 32 < 32 :=
                Nat.mod_lt _ (by decide)
              omega) h_b32_toNat_lt]
            simp [U32w.toNat]
            rw [Nat.mod_eq_of_lt ha0_lt, Nat.mod_eq_of_lt ha1_lt,
                Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
                Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
            have h_c_sum_mod_32 :
                ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32 = k_nat + 16 := by
              have heq : ((air.cols.values.c_for_lookup_0 row 0).val
                  + (air.cols.values.c_for_lookup_1 row 0).val * 65536) % 32
                  = (air.cols.values.c_for_lookup_0 row 0).val % 32 := by omega
              rw [heq]
              have : (air.cols.values.c_for_lookup_0 row 0).val % 64 = k_nat + 48 := h_cfl0_mod64
              omega
            rw [h_c_sum_mod_32, ha0_val, ha1_val, h_decomp_0, h_decomp_1]
            clear h_c_decomp h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
                  h_lr0_lt h_hi1_lt ha0_lt ha1_lt
                  h_sra_msb_v0123 h_srw_msb_u16 h_msb_iff h_srw_msb_b
                  h_b_msb_b h_b_msb_u16 h_sra_msb h_diff_val hv_val
                  h_msb_b32_true h_b32_toNat_lt
                  h_b_carry_0 h_b_carry_1 h_b_carry_2 h_b_carry_3
                  _h_imm_c_b _h_w_imm
                  h_su0_sel h_su0_b h_su1_sel h_su1_b
                  h_su2_sel h_su2_b h_su3_sel h_su3_b
                  h_su0_a0 h_su0_a1 h_su1_a0 h_su1_a1
                  h_a2_msb h_a3_msb
                  ha0_raw ha0_form ha0_val ha1 ha1_raw ha1_val hsu0 hsu1 hsu2 hsu3
                  h_c_sum_mod_32 h_c_mod64 h_cfl0_mod64 hs5_lift hs5_le
                  h_gadget_wf h_gadget_cstr
            have hk_le' : k_nat ≤ 15 := hk_le
            interval_cases k_nat <;> omega

  --
  -- Externals — vacuous (negative byte multiplicities, never +1).
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row]
    intro h; exfalso; grind

  --
  -- wf_asrt — dispatches the ALU bus entry to `spec_SRL` / `spec_SRA` /
  -- `spec_SRLW` / `spec_SRAW` based on which selector is 1 (via
  -- `selector_breakdown`). The byte entries are vacuous (negative
  -- multiplicities, never +1).
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row]
    refine ⟨?_, ?_⟩
    -- ALU entry: dispatch by which selector is 1.
    . intro h_real
      obtain ⟨h_srl_disj, h_sra_disj, h_srlw_disj, h_sraw_disj⟩ := selectors
      rcases h_srl_disj with h_srl | h_srl
      . rcases h_sra_disj with h_sra | h_sra
        . rcases h_srlw_disj with h_srlw | h_srlw
          . -- all four = 0 ⇒ is_sraw = 1
            have h_sraw : air.cols.values.is_sraw row 0 = 1 := by grind
            simp [h_srl, h_sra, h_srlw, h_sraw]
            exact spec_SRAW air row h_ext h_wf h_constraints h_srl h_sra h_srlw h_sraw
          . -- is_srlw = 1, others = 0
            have h_sraw : air.cols.values.is_sraw row 0 = 0 := by grind
            simp [h_srl, h_sra, h_srlw, h_sraw]
            exact spec_SRLW air row h_ext h_wf h_constraints h_srl h_sra h_srlw h_sraw
        . -- is_sra = 1
          have h_srlw : air.cols.values.is_srlw row 0 = 0 := by grind
          have h_sraw : air.cols.values.is_sraw row 0 = 0 := by grind
          simp [h_srl, h_sra, h_srlw, h_sraw]
          exact spec_SRA air row h_ext h_wf h_constraints h_srl h_sra h_srlw h_sraw
      . -- is_srl = 1
        have h_sra : air.cols.values.is_sra row 0 = 0 := by grind
        have h_srlw : air.cols.values.is_srlw row 0 = 0 := by grind
        have h_sraw : air.cols.values.is_sraw row 0 = 0 := by grind
        simp [h_srl, h_sra, h_srlw, h_sraw]
        exact spec_SRL air row h_ext h_wf h_constraints h_srl h_sra h_srlw h_sraw
    -- Byte entries: vacuous (negative multiplicity, never +1).
    . split_ands <;> intro h <;> exfalso <;> grind

end ShiftRightChip.Spec
