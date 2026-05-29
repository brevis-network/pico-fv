import PicoFV.RV64IM.Constraints.SLLChip
import PicoFV.RV64IM.Spec.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SLLChip — semantic specification

Ports the RV32 `SllAir.Spec` approach to the RV64 u16-limb width.
There are two ALU outputs (vs one for RV32):

- `spec_SLL`  (opcode 5):  64-bit left shift, shift amount = low 6 bits of `c`.
- `spec_SLLW` (opcode 42): 32-bit left shift, sign-extended to 64 bits;
  shift amount = low 5 bits of `c`.

The proof structure mirrors RV32:

1. Extract operand `< 65536` bounds from the chip's ALU externals
   (opcodes 5 / 42 are not in `ALUBus.operandsInternal`).
2. Extract byte-bus assumptions for each `(lower_limb_i, higher_limb_i)`
   pair (`BitRange` opcode 9) and the SLLW `U16MSBGadget` entry on `a_1`.
3. Simplify the 53 constraints into named hypotheses.
4. Lift the per-limb FKB carry equations
   `b_i · v_0123 = higher_limb_i · 65536 + lower_limb_i · v_0123`
   to Nat-level identities, using the bus bounds and the bit-shift
   booleans on `c_bits_0..3`.
5. Case-split on the low 6 bits (`c_bits_0..5`) — 64 cases for SLL,
   32 for SLLW (the SLLW selector forces `c_bits_5 = 0`-effective via
   the `c_bits_4 + 2·c_bits_5·is_sll` shift_u16 selector wiring).
6. In each case, the concrete values of `v_0123` and `shift_u16`
   resolve the chip's `a_i` assignments. Close with
   `BitVec.eq_of_toNat_eq + omega` (Nat-level shift identity).
-/

namespace SLLChip.Spec

  open RV64IM_Interactions
  open SLLChip.ConstraintsAndBuses
  open SLLChip.Interactions
  open SLLChip.Interpretations
  open LeanRV64D.Functions

  set_option maxHeartbeats 4_000_000_000

  -- =====================================================================
  -- `v_0123` cascade: when `c_bits_0..3` are booleans, `v_0123 = 2^k` in
  -- FKB where `k = c0.val + 2 c1.val + 4 c2.val + 8 c3.val ≤ 15`. The 16
  -- branches reduce to a numeric check via `decide`.
  -- =====================================================================
  private lemma v0123_pow
      (c0 c1 c2 c3 v01 v012 v0123 : FKB)
      (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1)
      (hc2 : c2 = 0 ∨ c2 = 1) (hc3 : c3 = 0 ∨ c3 = 1)
      (h_v01  : v01   = (c0 + 1) * (c1 * 3 + 1))
      (h_v012 : v012  = v01 * (c2 * 15 + 1))
      (h_v0123: v0123 = v012 * (c3 * 255 + 1))
    : c0.val + 2*c1.val + 4*c2.val + 8*c3.val ≤ 15 ∧
      v0123 = ((2^(c0.val + 2*c1.val + 4*c2.val + 8*c3.val) : ℕ) : FKB) := by
    rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;>
    rcases hc2 with h2 | h2 <;> rcases hc3 with h3 | h3 <;>
    subst h0 h1 h2 h3 <;>
    refine ⟨?_, ?_⟩ <;> simp_all

  -- =====================================================================
  -- `s4` decomposition: when `c_bits_0..3` are booleans, the FKB sum
  -- `c0 + c1 * 2 + c2 * 4 + c3 * 8` has Nat value
  -- `c0.val + 2 c1.val + 4 c2.val + 8 c3.val`, and `16 - s4_FKB` has Nat
  -- value `16 - s4_nat`.
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
  -- `limb_result_0` lift: `(lower · 2^k).val = lower.val · 2^k` when
  -- `lower.val < 2^(16-k)` (the product fits in a `u16`).
  -- =====================================================================
  private lemma lr_val_first
      (lower : FKB) (k_nat : ℕ)
      (hk : k_nat ≤ 15)
      (hlow : lower.val < 2^(16-k_nat))
    : (lower * ((2^k_nat : ℕ) : FKB)).val = lower.val * 2^k_nat := by
    have hpow_lt : (2^k_nat : ℕ) < KB_prime := by
      have : (2^k_nat : ℕ) ≤ 2^15 := Nat.pow_le_pow_right (by omega) hk
      omega
    have hpow_val : (((2^k_nat:ℕ):FKB)).val = 2^k_nat := by
      rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt hpow_lt
    rw [Fin.val_mul, hpow_val]
    apply Nat.mod_eq_of_lt
    have h1 : lower.val * 2^k_nat < 2^(16-k_nat) * 2^k_nat :=
      Nat.mul_lt_mul_of_pos_right hlow (Nat.two_pow_pos _)
    have hpow_prod : (2^(16-k_nat) : ℕ) * 2^k_nat = 2^16 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : k_nat ≤ 16)]
    rw [hpow_prod] at h1; omega

  -- =====================================================================
  -- `limb_result_{i>0}` lift: `(lower · 2^k + higher).val
  --     = lower.val · 2^k + higher.val` (< `2^16`, the new limb fits).
  -- =====================================================================
  private lemma lr_val_next
      (lower higher : FKB) (k_nat : ℕ)
      (hk : k_nat ≤ 15)
      (hlow : lower.val < 2^(16-k_nat))
      (hhi : higher.val < 2^k_nat)
    : (lower * ((2^k_nat : ℕ) : FKB) + higher).val
        = lower.val * 2^k_nat + higher.val := by
    rw [Fin.val_add, lr_val_first lower k_nat hk hlow]
    apply Nat.mod_eq_of_lt
    have hpow_prod : (2^(16-k_nat) : ℕ) * 2^k_nat = 2^16 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : k_nat ≤ 16)]
    have hpos_k : (0 : ℕ) < 2^k_nat := Nat.two_pow_pos _
    have hpow_le15 : (2^k_nat : ℕ) ≤ 2^15 := Nat.pow_le_pow_right (by omega) hk
    have hpow_eq16_bnd : (2^16 : ℕ) = 65536 := by decide
    have hlow_mul : lower.val * 2^k_nat ≤ 2^16 - 2^k_nat := by
      have h_le : lower.val ≤ 2^(16-k_nat) - 1 := by omega
      have h1 : lower.val * 2^k_nat ≤ (2^(16-k_nat) - 1) * 2^k_nat :=
        Nat.mul_le_mul_right _ h_le
      have h2 : (2^(16-k_nat) - 1) * 2^k_nat = 2^16 - 2^k_nat := by
        rw [Nat.sub_mul, one_mul, hpow_prod]
      omega
    have h_sum : lower.val * 2^k_nat + higher.val < 2^16 := by omega
    omega

  -- =====================================================================
  -- `c_0` mod-64 decomposition: from `((c_0 - s5_FKB) · inv64).val < 1024`
  -- and the bounds on `c_0`, `s5_FKB`, conclude `c_0.val mod 64 = s5_FKB.val`
  -- (which is what `(c.extractLsb 5 0).toNat` evaluates to).
  -- =====================================================================
  private lemma c0_mod64
      (c_0 s5_FKB : FKB)
      (hs5_val : s5_FKB.val ≤ 63)
      (hdecomp : ((c_0 - s5_FKB) * 2097414145).val < 1024)
    : c_0.val % 64 = s5_FKB.val := by
    set t : FKB := (c_0 - s5_FKB) * 2097414145 with ht_def
    have hinv : (64 : FKB) * 2097414145 = 1 := by decide
    have h64t : 64 * t = c_0 - s5_FKB := by
      rw [ht_def]; linear_combination (c_0 - s5_FKB) * hinv
    have hc0_eq : c_0 = s5_FKB + 64 * t := by rw [h64t]; ring
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
    apply_fun Fin.val at hc0_eq
    rw [hsum_val] at hc0_eq
    omega

  -- =====================================================================
  -- Carry helper: lift the FKB carry equation `b * 2^k = higher * 65536 +
  -- lower * 2^k` to a Nat-level limb identity `b.val = higher.val *
  -- 2^(16-k) + lower.val`.
  --
  -- The key step is factoring `65536 = 2^k · 2^(16-k)` in FKB and using
  -- the field-cancellation property (since `2^k ∈ {1, …, 32768}` is a
  -- non-zero element of FKB). The Nat lift then uses the tight bound
  -- `higher.val * 2^(16-k) + lower.val < 2^17 < KB_prime`, sidestepping
  -- the potential overflow of the original product `b * v_0123`.
  -- =====================================================================
  private lemma carry_lift
      (b lower higher : FKB) (k : ℕ)
      (hk : k ≤ 15)
      (hb : b.val < 65536)
      (hlower : lower.val < 2^(16-k))
      (hhigher : higher.val < 2^k)
      (heq : b * ((2^k : ℕ) : FKB) = higher * 65536 + lower * ((2^k : ℕ) : FKB))
    : b.val = higher.val * 2^(16-k) + lower.val := by
    have hk16 : k ≤ 16 := by omega
    have hpos_k : (0 : ℕ) < 2^k := Nat.two_pow_pos k
    have hpos_16k : (0 : ℕ) < 2^(16-k) := Nat.two_pow_pos (16-k)
    have h_2k_le : (2^k : ℕ) ≤ 2^15 := Nat.pow_le_pow_right (by omega) hk
    have h_2_16k_le : (2^(16-k) : ℕ) ≤ 2^16 := Nat.pow_le_pow_right (by omega) (by omega)
    have hpow_eq16 : (2^k : ℕ) * (2^(16-k) : ℕ) = 2^16 := by
      rw [← pow_add, Nat.add_sub_cancel' hk16]
    have hcast : (65536 : FKB) = ((2^k:ℕ):FKB) * ((2^(16-k):ℕ):FKB) := by
      rw [← Nat.cast_mul, hpow_eq16]; norm_num
    have hpow_ne : ((2^k : ℕ) : FKB) ≠ 0 := by
      intro h
      apply_fun Fin.val at h
      have hlt : (2^k : ℕ) < KB_prime := by omega
      simp at h
    have h_fkb_eq : b = higher * ((2^(16-k):ℕ):FKB) + lower := by
      have h_sub : ((2^k : ℕ) : FKB) * (b - higher * ((2^(16-k):ℕ):FKB) - lower) = 0 := by
        linear_combination heq + hcast * higher
      rcases mul_eq_zero.mp h_sub with h | h
      · exact absurd h hpow_ne
      · linear_combination h
    have hpow16k_val : (((2^(16-k):ℕ):FKB)).val = 2^(16-k) := by
      have hlt : (2^(16-k) : ℕ) < KB_prime := by omega
      rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt hlt
    have h_higher_bnd : higher.val * 2^(16-k) < 2^16 := by
      have h1 : higher.val * 2^(16-k) < 2^k * 2^(16-k) :=
        (Nat.mul_lt_mul_right hpos_16k).mpr hhigher
      rw [hpow_eq16] at h1; exact h1
    have h_higher_prod_val :
        (higher * ((2^(16-k):ℕ):FKB)).val = higher.val * 2^(16-k) := by
      rw [Fin.val_mul, hpow16k_val]
      apply Nat.mod_eq_of_lt; omega
    have h_sum_val :
        (higher * ((2^(16-k):ℕ):FKB) + lower).val
          = higher.val * 2^(16-k) + lower.val := by
      rw [Fin.val_add, h_higher_prod_val]
      apply Nat.mod_eq_of_lt
      have : higher.val * 2^(16-k) + lower.val < 2^16 + 2^16 := by omega
      omega
    rw [← h_sum_val, ← h_fkb_eq]

  --
  -- spec_SLL — opcode 5 (64-bit left shift)
  --

  -- =====================================================================
  -- spec_SLL: 64-case split on c_bits_0..c_bits_5.
  -- For each case, the chip's witnesses (v_0123, shift_u16, lower/higher
  -- limb decomposition) become concrete and the result equation
  --   a = b << (c & 0x3F)
  -- closes via BitVec / omega arithmetic.
  -- =====================================================================

  lemma spec_SLL
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
    (h_is_sll : air.cols.values.is_sll row 0 = 1)
  :
    ALUBus.Spec
      5
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    -- Step 1: Selector exclusivity ⇒ is_sllw = 0, is_real = 1.
    obtain ⟨h_excl_sll, _⟩ := selector_exclusivity air row h_constraints
    have h_is_sllw : air.cols.values.is_sllw row 0 = 0 := h_excl_sll h_is_sll
    have h_is_real :
      air.cols.values.is_sll row 0 + air.cols.values.is_sllw row 0 = 1
      := by rw [h_is_sll, h_is_sllw]; ring
    -- Step 2: Extract operand u16 bounds from h_ext.
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_sll, h_is_sllw] at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Step 3: Extract byte-bus assumptions from h_wf.
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_sll, h_is_sllw] at h_wf
    obtain ⟨h_c_decomp, ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, _, h_hi3⟩ := h_wf
    -- Step 4: Extract all 53 constraints.
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_sll, h_is_sllw] at h_constraints
    obtain ⟨_, h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b, h_su2_sel, h_su2_b,
            h_su3_sel, h_su3_b, h_su_sum,
            h_v01, h_v012, h_v0123,
            h_carry0, h_carry1, h_carry2, h_carry3,
            h_lr0, h_lr1, h_lr2, h_lr3,
            h_su0_a0, h_su0_a1, h_su0_a2, h_su0_a3,
            h_su1_a0, h_su1_a1, h_su1_a2, h_su1_a3,
            h_su2_a0, h_su2_a1, h_su2_a2, h_su2_a3,
            h_su3_a0, h_su3_a1, h_su3_a2, h_su3_a3,
            _⟩ := h_constraints
    -- Step 5: Derive `v_0123 = 2^k` and `k ≤ 15` (where `k = c_bits sum`).
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: Convert the byte-bus bounds to Nat form using s4_FKB_val.
    rw [h16s4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [hs4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(16 - k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: Lift each carry equation to a per-limb Nat decomposition.
    rw [hv] at h_carry0 h_carry1 h_carry2 h_carry3
    have h_decomp_0 := carry_lift _ _ _ k_nat hk_le hb0 h_lo0 h_hi0 h_carry0
    have h_decomp_1 := carry_lift _ _ _ k_nat hk_le hb1 h_lo1 h_hi1 h_carry1
    have h_decomp_2 := carry_lift _ _ _ k_nat hk_le hb2 h_lo2 h_hi2 h_carry2
    have h_decomp_3 := carry_lift _ _ _ k_nat hk_le hb3 h_lo3 h_hi3 h_carry3
    -- Step 8: Compute Nat values of `limb_result_i`.
    rw [hv] at h_lr0 h_lr1 h_lr2 h_lr3
    have h_lr0_val := lr_val_first _ k_nat hk_le h_lo0
    have h_lr1_val := lr_val_next _ _ k_nat hk_le h_lo1 h_hi0
    have h_lr2_val := lr_val_next _ _ k_nat hk_le h_lo2 h_hi1
    have h_lr3_val := lr_val_next _ _ k_nat hk_le h_lo3 h_hi2
    rw [← h_lr0] at h_lr0_val
    rw [← h_lr1] at h_lr1_val
    rw [← h_lr2] at h_lr2_val
    rw [← h_lr3] at h_lr3_val
    -- Step 9: Establish concrete bounds for limb_result_i.
    have hpow_prod : (2^(16-k_nat) : ℕ) * 2^k_nat = 2^16 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : k_nat ≤ 16)]
    have hpow_le15 : (2^k_nat : ℕ) ≤ 2^15 := Nat.pow_le_pow_right (by omega) hk_le
    have h_lr0_bnd : (air.cols.values.limb_result_0 row 0).val < 2^16 := by
      rw [h_lr0_val]
      have : (air.cols.values.lower_limb_0 row 0).val * 2^k_nat
           < 2^(16-k_nat) * 2^k_nat :=
        Nat.mul_lt_mul_of_pos_right h_lo0 (Nat.two_pow_pos _)
      rw [hpow_prod] at this; exact this
    have h_lr1_bnd : (air.cols.values.limb_result_1 row 0).val < 2^16 := by
      rw [h_lr1_val]
      have h1 : (air.cols.values.lower_limb_1 row 0).val * 2^k_nat
              ≤ 2^16 - 2^k_nat := by
        have hle : (air.cols.values.lower_limb_1 row 0).val ≤ 2^(16-k_nat) - 1
          := by omega
        have h2 : (air.cols.values.lower_limb_1 row 0).val * 2^k_nat
                ≤ (2^(16-k_nat) - 1) * 2^k_nat := Nat.mul_le_mul_right _ hle
        have h3 : (2^(16-k_nat) - 1) * 2^k_nat = 2^16 - 2^k_nat := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr2_bnd : (air.cols.values.limb_result_2 row 0).val < 2^16 := by
      rw [h_lr2_val]
      have h1 : (air.cols.values.lower_limb_2 row 0).val * 2^k_nat
              ≤ 2^16 - 2^k_nat := by
        have hle : (air.cols.values.lower_limb_2 row 0).val ≤ 2^(16-k_nat) - 1
          := by omega
        have h2 : (air.cols.values.lower_limb_2 row 0).val * 2^k_nat
                ≤ (2^(16-k_nat) - 1) * 2^k_nat := Nat.mul_le_mul_right _ hle
        have h3 : (2^(16-k_nat) - 1) * 2^k_nat = 2^16 - 2^k_nat := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    have h_lr3_bnd : (air.cols.values.limb_result_3 row 0).val < 2^16 := by
      rw [h_lr3_val]
      have h1 : (air.cols.values.lower_limb_3 row 0).val * 2^k_nat
              ≤ 2^16 - 2^k_nat := by
        have hle : (air.cols.values.lower_limb_3 row 0).val ≤ 2^(16-k_nat) - 1
          := by omega
        have h2 : (air.cols.values.lower_limb_3 row 0).val * 2^k_nat
                ≤ (2^(16-k_nat) - 1) * 2^k_nat := Nat.mul_le_mul_right _ hle
        have h3 : (2^(16-k_nat) - 1) * 2^k_nat = 2^16 - 2^k_nat := by
          rw [Nat.sub_mul, one_mul, hpow_prod]
        omega
      omega
    -- Step 10: Case-split on `c_bits_4`, `c_bits_5` (4 cases). The `is_sll` selector
    -- forces exactly one of `shift_u16_{0..3}` to be `1` per case; the active selector
    -- picks the u16-offset of the final 16-step block.
    have h_lr0_lt : (air.cols.values.limb_result_0 row 0).val < 65536 := by
      have : (2^16 : ℕ) = 65536 := by decide
      omega
    have h_lr1_lt : (air.cols.values.limb_result_1 row 0).val < 65536 := by
      have : (2^16 : ℕ) = 65536 := by decide
      omega
    have h_lr2_lt : (air.cols.values.limb_result_2 row 0).val < 65536 := by
      have : (2^16 : ℕ) = 65536 := by decide
      omega
    have h_lr3_lt : (air.cols.values.limb_result_3 row 0).val < 65536 := by
      have : (2^16 : ℕ) = 65536 := by decide
      omega
    -- Case-split on (c_bits_4, c_bits_5) to determine which `shift_u16_? = 1`.
    rcases h_cb4_b with hcb4 | hcb4 <;> rcases h_cb5_b with hcb5 | hcb5
    -- Case (0, 0): shift_u16_0 = 1, a_i = limb_result_i.
    .
      have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
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
        rw [hsu1, hsu2, hsu3] at h_su_sum
        linear_combination h_su_sum
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
        . exact h
      sorry
    . sorry
    . sorry
    . sorry

  --
  -- spec_SLLW — opcode 42 (32-bit left shift, sign-extended)
  --

  lemma spec_SLLW
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
    (h_is_sllw : air.cols.values.is_sllw row 0 = 1)
  :
    ALUBus.Spec
      42
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    sorry

  --
  -- Externals — vacuous: byte entries have trivial externals; the
  -- ALU entry's `ext_assert_cond` (multiplicity = -1) never fires.
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row]
    intro h; exfalso; grind

  --
  -- wf_asrt — dispatches to spec_SLL / spec_SLLW
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row]
    refine ⟨?_, ?_⟩
    -- ALU entry: dispatch by selector.
    . intro h_real
      obtain ⟨h_sll_disj, h_sllw_disj, _⟩ := selectors
      rcases h_sll_disj with h_sll | h_sll
      . -- is_sll = 0 ⇒ is_sllw = 1
        have h_sllw : air.cols.values.is_sllw row 0 = 1 := by grind
        simp [h_sll, h_sllw]
        exact spec_SLLW air row h_ext h_wf h_constraints h_sllw
      . -- is_sll = 1 ⇒ is_sllw = 0
        have h_sllw : air.cols.values.is_sllw row 0 = 0 := by grind
        simp [h_sll, h_sllw]
        exact spec_SLL air row h_ext h_wf h_constraints h_sll
    -- Byte entries: vacuous (negative multiplicity, never +1).
    . split_ands <;> intro h <;> exfalso <;> grind

end SLLChip.Spec
