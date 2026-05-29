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
    -- Order: (0,0), (1,0), (0,1), (1,1) — splitting `c_bits_5` first, then `c_bits_4`.
    rcases h_cb5_b with hcb5 | hcb5 <;> rcases h_cb4_b with hcb4 | hcb4
    -- Case (0, 0): shift_u16_0 = 1, a_i = limb_result_i.
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
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_left,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨h_lr0_lt, h_lr1_lt, h_lr2_lt, h_lr3_lt⟩, ?_⟩
      -- BitVec identity for case (0,0): shift amount = k_nat.
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_val : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 0 * 32 : FKB).val ≤ 63 := by
        have : (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 0 * 32 : FKB)
             = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) := by ring
        rw [this, hs4_val]; omega
      have h_c0_mod64 := c0_mod64 _ _ hs5_val h_c_decomp
      rw [show (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8
              + 0 * 16 + 0 * 32 : FKB)
            = (air.cols.values.c_bits_0 row 0
              + air.cols.values.c_bits_1 row 0 * 2
              + air.cols.values.c_bits_2 row 0 * 4
              + air.cols.values.c_bits_3 row 0 * 8 : FKB) from by ring,
            hs4_val] at h_c0_mod64
      change (air.cols.values.c_0 row 0).val % 64 = k_nat at h_c0_mod64
      -- Now prove the BitVec equation by toNat
      apply BitVec.eq_of_toNat_eq
      simp [U64w.toBV_toNat, U64w.toNat, BitVec.toNat_shiftLeft,
            Sail.BitVec.extractLsb, BitVec.extractLsb,
            BitVec.toNat_ofNat]
      have h_lr0_mod : (air.cols.values.limb_result_0 row 0).val % 65536 = (air.cols.values.limb_result_0 row 0).val := Nat.mod_eq_of_lt h_lr0_lt
      have h_lr1_mod : (air.cols.values.limb_result_1 row 0).val % 65536 = (air.cols.values.limb_result_1 row 0).val := Nat.mod_eq_of_lt h_lr1_lt
      have h_lr2_mod : (air.cols.values.limb_result_2 row 0).val % 65536 = (air.cols.values.limb_result_2 row 0).val := Nat.mod_eq_of_lt h_lr2_lt
      have h_lr3_mod : (air.cols.values.limb_result_3 row 0).val % 65536 = (air.cols.values.limb_result_3 row 0).val := Nat.mod_eq_of_lt h_lr3_lt
      have hb0_mod : (air.cols.values.b_0 row 0).val % 65536 = (air.cols.values.b_0 row 0).val := Nat.mod_eq_of_lt hb0
      have hb1_mod : (air.cols.values.b_1 row 0).val % 65536 = (air.cols.values.b_1 row 0).val := Nat.mod_eq_of_lt hb1
      have hb2_mod : (air.cols.values.b_2 row 0).val % 65536 = (air.cols.values.b_2 row 0).val := Nat.mod_eq_of_lt hb2
      have hb3_mod : (air.cols.values.b_3 row 0).val % 65536 = (air.cols.values.b_3 row 0).val := Nat.mod_eq_of_lt hb3
      have hc0_mod : (air.cols.values.c_0 row 0).val % 65536 = (air.cols.values.c_0 row 0).val := Nat.mod_eq_of_lt hc0
      have hc1_mod : (air.cols.values.c_1 row 0).val % 65536 = (air.cols.values.c_1 row 0).val := Nat.mod_eq_of_lt hc1
      have hc2_mod : (air.cols.values.c_2 row 0).val % 65536 = (air.cols.values.c_2 row 0).val := Nat.mod_eq_of_lt hc2
      have hc3_mod : (air.cols.values.c_3 row 0).val % 65536 = (air.cols.values.c_3 row 0).val := Nat.mod_eq_of_lt hc3
      rw [hb0_mod, hb1_mod, hb2_mod, hb3_mod,
          h_lr0_mod, h_lr1_mod, h_lr2_mod, h_lr3_mod,
          hc0_mod, hc1_mod, hc2_mod, hc3_mod]
      -- The c.toNat mod 64 reduces to c_0.val mod 64 = k_nat.
      have h_c_sum_mod_64 :
          ((air.cols.values.c_0 row 0).val + (air.cols.values.c_1 row 0).val * 65536
            + (air.cols.values.c_2 row 0).val * 4294967296
            + (air.cols.values.c_3 row 0).val * 281474976710656) % 64 = k_nat := by
        rw [← h_c0_mod64]; omega
      rw [h_c_sum_mod_64]
      rw [Nat.shiftLeft_eq]
      -- Substitute the per-limb identities.
      rw [h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3,
          h_lr0_val, h_lr1_val, h_lr2_val, h_lr3_val]
      -- Now `2 ^ k_nat` is the only variable exponent. `interval_cases k_nat` gives 16 cases.
      clear h_c_decomp h_carry0 h_carry1 h_carry2 h_carry3
            h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_lr0_mod h_lr1_mod h_lr2_mod h_lr3_mod
            hb0_mod hb1_mod hb2_mod hb3_mod
            hc0_mod hc1_mod hc2_mod hc3_mod
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            h_lr0_bnd h_lr1_bnd h_lr2_bnd h_lr3_bnd
            h_c_sum_mod_64
      have hk_le' : k_nat ≤ 15 := hk_le
      have hk_ge' : 0 ≤ k_nat := Nat.zero_le _
      interval_cases k_nat <;> omega
    -- Case (1, 0): shift_u16_1 = 1; a_0 = 0, a_i (i≥1) = limb_result_{i-1}; total shift k+16.
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
      have ha0 : air.cols.values.a_0 row 0 = 0 := by
        rcases h_su1_a0 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su1_a1 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha2 : air.cols.values.a_2 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_su1_a2 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      have ha3 : air.cols.values.a_3 row 0 = air.cols.values.limb_result_2 row 0 := by
        rcases h_su1_a3 with h | h
        . rw [h] at hsu1; exact absurd hsu1 (by decide)
        . exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_left,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨?_, h_lr0_lt, h_lr1_lt, h_lr2_lt⟩, ?_⟩
      . simp
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift :
          (air.cols.values.c_bits_0 row 0
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
      have hs5_val : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c0_mod64 := c0_mod64 _ _ hs5_val h_c_decomp
      rw [hs5_lift] at h_c0_mod64
      apply BitVec.eq_of_toNat_eq
      simp only [U64w.toBV_toNat, U64w.toNat, Sail.BitVec.extractLsb, BitVec.extractLsb]
      have h_lr0_mod : (air.cols.values.limb_result_0 row 0).val % 65536
                     = (air.cols.values.limb_result_0 row 0).val := Nat.mod_eq_of_lt h_lr0_lt
      have h_lr1_mod : (air.cols.values.limb_result_1 row 0).val % 65536
                     = (air.cols.values.limb_result_1 row 0).val := Nat.mod_eq_of_lt h_lr1_lt
      have h_lr2_mod : (air.cols.values.limb_result_2 row 0).val % 65536
                     = (air.cols.values.limb_result_2 row 0).val := Nat.mod_eq_of_lt h_lr2_lt
      have hb0_mod : (air.cols.values.b_0 row 0).val % 65536 = (air.cols.values.b_0 row 0).val
        := Nat.mod_eq_of_lt hb0
      have hb1_mod : (air.cols.values.b_1 row 0).val % 65536 = (air.cols.values.b_1 row 0).val
        := Nat.mod_eq_of_lt hb1
      have hb2_mod : (air.cols.values.b_2 row 0).val % 65536 = (air.cols.values.b_2 row 0).val
        := Nat.mod_eq_of_lt hb2
      have hb3_mod : (air.cols.values.b_3 row 0).val % 65536 = (air.cols.values.b_3 row 0).val
        := Nat.mod_eq_of_lt hb3
      have hc0_mod : (air.cols.values.c_0 row 0).val % 65536 = (air.cols.values.c_0 row 0).val
        := Nat.mod_eq_of_lt hc0
      have hc1_mod : (air.cols.values.c_1 row 0).val % 65536 = (air.cols.values.c_1 row 0).val
        := Nat.mod_eq_of_lt hc1
      have hc2_mod : (air.cols.values.c_2 row 0).val % 65536 = (air.cols.values.c_2 row 0).val
        := Nat.mod_eq_of_lt hc2
      have hc3_mod : (air.cols.values.c_3 row 0).val % 65536 = (air.cols.values.c_3 row 0).val
        := Nat.mod_eq_of_lt hc3
      simp [BitVec.toNat_ofNat, U64w.toNat,
            hb0_mod, hb1_mod, hb2_mod, hb3_mod,
            h_lr0_mod, h_lr1_mod, h_lr2_mod,
            hc0_mod, hc1_mod, hc2_mod, hc3_mod]
      have h_c_sum_mod_64 :
          ((air.cols.values.c_0 row 0).val + (air.cols.values.c_1 row 0).val * 65536
            + (air.cols.values.c_2 row 0).val * 4294967296
            + (air.cols.values.c_3 row 0).val * 281474976710656) % 64 = k_nat + 16 := by
        rw [← h_c0_mod64]; omega
      rw [h_c_sum_mod_64, Nat.shiftLeft_eq,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3,
          h_lr0_val, h_lr1_val, h_lr2_val]
      clear h_c_decomp h_carry0 h_carry1 h_carry2 h_carry3
            h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_lr0_mod h_lr1_mod h_lr2_mod
            hb0_mod hb1_mod hb2_mod hb3_mod
            hc0_mod hc1_mod hc2_mod hc3_mod
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            h_lr0_bnd h_lr1_bnd h_lr2_bnd h_lr3_bnd
            h_c_sum_mod_64
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega
    -- Case (0, 1): shift_u16_2 = 1; a_0 = a_1 = 0, a_2 = lr_0, a_3 = lr_1; shift k+32.
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
      have ha0 : air.cols.values.a_0 row 0 = 0 := by
        rcases h_su2_a0 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = 0 := by
        rcases h_su2_a1 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha2 : air.cols.values.a_2 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su2_a2 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      have ha3 : air.cols.values.a_3 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_su2_a3 with h | h
        . rw [h] at hsu2; exact absurd hsu2 (by decide)
        . exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_left,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨?_, ?_, h_lr0_lt, h_lr1_lt⟩, ?_⟩
      . simp
      . simp
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift :
          (air.cols.values.c_bits_0 row 0
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
      have hs5_val : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 0 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c0_mod64 := c0_mod64 _ _ hs5_val h_c_decomp
      rw [hs5_lift] at h_c0_mod64
      apply BitVec.eq_of_toNat_eq
      simp only [U64w.toBV_toNat, U64w.toNat, Sail.BitVec.extractLsb, BitVec.extractLsb]
      have h_lr0_mod : (air.cols.values.limb_result_0 row 0).val % 65536
                     = (air.cols.values.limb_result_0 row 0).val := Nat.mod_eq_of_lt h_lr0_lt
      have h_lr1_mod : (air.cols.values.limb_result_1 row 0).val % 65536
                     = (air.cols.values.limb_result_1 row 0).val := Nat.mod_eq_of_lt h_lr1_lt
      have hb0_mod : (air.cols.values.b_0 row 0).val % 65536 = (air.cols.values.b_0 row 0).val
        := Nat.mod_eq_of_lt hb0
      have hb1_mod : (air.cols.values.b_1 row 0).val % 65536 = (air.cols.values.b_1 row 0).val
        := Nat.mod_eq_of_lt hb1
      have hb2_mod : (air.cols.values.b_2 row 0).val % 65536 = (air.cols.values.b_2 row 0).val
        := Nat.mod_eq_of_lt hb2
      have hb3_mod : (air.cols.values.b_3 row 0).val % 65536 = (air.cols.values.b_3 row 0).val
        := Nat.mod_eq_of_lt hb3
      have hc0_mod : (air.cols.values.c_0 row 0).val % 65536 = (air.cols.values.c_0 row 0).val
        := Nat.mod_eq_of_lt hc0
      have hc1_mod : (air.cols.values.c_1 row 0).val % 65536 = (air.cols.values.c_1 row 0).val
        := Nat.mod_eq_of_lt hc1
      have hc2_mod : (air.cols.values.c_2 row 0).val % 65536 = (air.cols.values.c_2 row 0).val
        := Nat.mod_eq_of_lt hc2
      have hc3_mod : (air.cols.values.c_3 row 0).val % 65536 = (air.cols.values.c_3 row 0).val
        := Nat.mod_eq_of_lt hc3
      simp [BitVec.toNat_ofNat, U64w.toNat,
            hb0_mod, hb1_mod, hb2_mod, hb3_mod,
            h_lr0_mod, h_lr1_mod,
            hc0_mod, hc1_mod, hc2_mod, hc3_mod]
      have h_c_sum_mod_64 :
          ((air.cols.values.c_0 row 0).val + (air.cols.values.c_1 row 0).val * 65536
            + (air.cols.values.c_2 row 0).val * 4294967296
            + (air.cols.values.c_3 row 0).val * 281474976710656) % 64 = k_nat + 32 := by
        rw [← h_c0_mod64]; omega
      rw [h_c_sum_mod_64, Nat.shiftLeft_eq,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3,
          h_lr0_val, h_lr1_val]
      clear h_c_decomp h_carry0 h_carry1 h_carry2 h_carry3
            h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_lr0_mod h_lr1_mod
            hb0_mod hb1_mod hb2_mod hb3_mod
            hc0_mod hc1_mod hc2_mod hc3_mod
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            h_lr0_bnd h_lr1_bnd h_lr2_bnd h_lr3_bnd
            h_c_sum_mod_64
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega
    -- Case (1, 1): shift_u16_3 = 1; a_0 = a_1 = a_2 = 0, a_3 = lr_0; shift k+48.
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
      have ha0 : air.cols.values.a_0 row 0 = 0 := by
        rcases h_su3_a0 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = 0 := by
        rcases h_su3_a1 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      have ha2 : air.cols.values.a_2 row 0 = 0 := by
        rcases h_su3_a2 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      have ha3 : air.cols.values.a_3 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_su3_a3 with h | h
        . rw [h] at hsu3; exact absurd hsu3 (by decide)
        . exact h
      simp only [ALUBus.Spec, RV64IM.execute_RTYPE_pure, Sail.shift_bits_left,
                 ha0, ha1, ha2, ha3]
      refine ⟨⟨?_, ?_, ?_, h_lr0_lt⟩, ?_⟩
      . simp
      . simp
      . simp
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift :
          (air.cols.values.c_bits_0 row 0
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
      have hs5_val : (air.cols.values.c_bits_0 row 0
                    + air.cols.values.c_bits_1 row 0 * 2
                    + air.cols.values.c_bits_2 row 0 * 4
                    + air.cols.values.c_bits_3 row 0 * 8
                    + 1 * 16 + 1 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c0_mod64 := c0_mod64 _ _ hs5_val h_c_decomp
      rw [hs5_lift] at h_c0_mod64
      apply BitVec.eq_of_toNat_eq
      simp only [U64w.toBV_toNat, U64w.toNat, Sail.BitVec.extractLsb, BitVec.extractLsb]
      have h_lr0_mod : (air.cols.values.limb_result_0 row 0).val % 65536
                     = (air.cols.values.limb_result_0 row 0).val := Nat.mod_eq_of_lt h_lr0_lt
      have hb0_mod : (air.cols.values.b_0 row 0).val % 65536 = (air.cols.values.b_0 row 0).val
        := Nat.mod_eq_of_lt hb0
      have hb1_mod : (air.cols.values.b_1 row 0).val % 65536 = (air.cols.values.b_1 row 0).val
        := Nat.mod_eq_of_lt hb1
      have hb2_mod : (air.cols.values.b_2 row 0).val % 65536 = (air.cols.values.b_2 row 0).val
        := Nat.mod_eq_of_lt hb2
      have hb3_mod : (air.cols.values.b_3 row 0).val % 65536 = (air.cols.values.b_3 row 0).val
        := Nat.mod_eq_of_lt hb3
      have hc0_mod : (air.cols.values.c_0 row 0).val % 65536 = (air.cols.values.c_0 row 0).val
        := Nat.mod_eq_of_lt hc0
      have hc1_mod : (air.cols.values.c_1 row 0).val % 65536 = (air.cols.values.c_1 row 0).val
        := Nat.mod_eq_of_lt hc1
      have hc2_mod : (air.cols.values.c_2 row 0).val % 65536 = (air.cols.values.c_2 row 0).val
        := Nat.mod_eq_of_lt hc2
      have hc3_mod : (air.cols.values.c_3 row 0).val % 65536 = (air.cols.values.c_3 row 0).val
        := Nat.mod_eq_of_lt hc3
      simp [BitVec.toNat_ofNat, U64w.toNat,
            hb0_mod, hb1_mod, hb2_mod, hb3_mod,
            h_lr0_mod,
            hc0_mod, hc1_mod, hc2_mod, hc3_mod]
      have h_c_sum_mod_64 :
          ((air.cols.values.c_0 row 0).val + (air.cols.values.c_1 row 0).val * 65536
            + (air.cols.values.c_2 row 0).val * 4294967296
            + (air.cols.values.c_3 row 0).val * 281474976710656) % 64 = k_nat + 48 := by
        rw [← h_c0_mod64]; omega
      rw [h_c_sum_mod_64, Nat.shiftLeft_eq,
          h_decomp_0, h_decomp_1, h_decomp_2, h_decomp_3,
          h_lr0_val]
      clear h_c_decomp h_carry0 h_carry1 h_carry2 h_carry3
            h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
            h_lr0_lt h_lr1_lt h_lr2_lt h_lr3_lt
            h_lr0_mod
            hb0_mod hb1_mod hb2_mod hb3_mod
            hc0_mod hc1_mod hc2_mod hc3_mod
            h_su0_sel h_su0_b h_su1_sel h_su1_b
            h_su2_sel h_su2_b h_su3_sel h_su3_b
            h_su0_a0 h_su0_a1 h_su0_a2 h_su0_a3
            h_su1_a0 h_su1_a1 h_su1_a2 h_su1_a3
            h_su2_a0 h_su2_a1 h_su2_a2 h_su2_a3
            h_su3_a0 h_su3_a1 h_su3_a2 h_su3_a3
            h_lr0_bnd h_lr1_bnd h_lr2_bnd h_lr3_bnd
            h_c_sum_mod_64
      have hk_le' : k_nat ≤ 15 := hk_le
      interval_cases k_nat <;> omega

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
    -- Step 1: Selector exclusivity ⇒ is_sll = 0, is_real = 1.
    obtain ⟨_, h_excl_sllw⟩ := selector_exclusivity air row h_constraints
    have h_is_sll : air.cols.values.is_sll row 0 = 0 := h_excl_sllw h_is_sllw
    have h_is_real :
      air.cols.values.is_sll row 0 + air.cols.values.is_sllw row 0 = 1
      := by rw [h_is_sll, h_is_sllw]; ring
    -- Step 2: Extract operand u16 bounds from h_ext.
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_sll, h_is_sllw] at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Step 3: Extract byte-bus assumptions from h_wf.
    --   With is_sllw = 1, both BitRange entries and the U16MSB entry are active.
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_sll, h_is_sllw] at h_wf
    obtain ⟨h_c_decomp, ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, ⟨_, h_hi3⟩, h_msb_range⟩ := h_wf
    -- Step 4: Extract all 53 constraints.
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_sll, h_is_sllw] at h_constraints
    obtain ⟨_, h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b, h_su2_sel, h_su2_b,
            h_su3_sel, h_su3_b, h_su_sum,
            h_v01, h_v012, h_v0123,
            h_carry0, h_carry1, h_carry2, h_carry3,
            h_lr0, h_lr1, h_lr2, h_lr3,
            h_sllw_a0_lr0, h_sllw_a1_lr1, h_sllw_a0_zero, h_sllw_a1_lr0,
            h_a2_msb, h_a3_msb, h_msb_b⟩ := h_constraints
    -- Step 5: Derive `v_0123 = 2^k` and `k ≤ 15`.
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: Convert byte-bus bounds to Nat form.
    rw [h16s4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [hs4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(16 - k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: Per-limb Nat decomposition.
    rw [hv] at h_carry0 h_carry1 h_carry2 h_carry3
    have h_decomp_0 := carry_lift _ _ _ k_nat hk_le hb0 h_lo0 h_hi0 h_carry0
    have h_decomp_1 := carry_lift _ _ _ k_nat hk_le hb1 h_lo1 h_hi1 h_carry1
    have h_decomp_2 := carry_lift _ _ _ k_nat hk_le hb2 h_lo2 h_hi2 h_carry2
    have h_decomp_3 := carry_lift _ _ _ k_nat hk_le hb3 h_lo3 h_hi3 h_carry3
    -- Step 8: Compute limb_result_i.val.
    rw [hv] at h_lr0 h_lr1 h_lr2 h_lr3
    have h_lr0_val := lr_val_first _ k_nat hk_le h_lo0
    have h_lr1_val := lr_val_next _ _ k_nat hk_le h_lo1 h_hi0
    rw [← h_lr0] at h_lr0_val
    rw [← h_lr1] at h_lr1_val
    -- Step 9: Bounds for limb_result_0, limb_result_1.
    have hpow_prod : (2^(16-k_nat) : ℕ) * 2^k_nat = 2^16 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : k_nat ≤ 16)]
    have hpow_le15 : (2^k_nat : ℕ) ≤ 2^15 := Nat.pow_le_pow_right (by omega) hk_le
    have h_lr0_lt : (air.cols.values.limb_result_0 row 0).val < 65536 := by
      rw [h_lr0_val]
      have : (air.cols.values.lower_limb_0 row 0).val * 2^k_nat
           < 2^(16-k_nat) * 2^k_nat :=
        Nat.mul_lt_mul_of_pos_right h_lo0 (Nat.two_pow_pos _)
      rw [hpow_prod] at this; omega
    have h_lr1_lt : (air.cols.values.limb_result_1 row 0).val < 65536 := by
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
    -- Step 10: shift_u16_2 = shift_u16_3 = 0 always (c_bits_4 ∈ {0,1} can't equal 2 or 3).
    have hsu2 : air.cols.values.shift_u16_2 row 0 = 0 := by
      rcases h_su2_sel with h | h
      . exact h
      . rcases h_cb4_b with hcb | hcb <;> rw [hcb] at h <;> exact absurd h (by decide)
    have hsu3 : air.cols.values.shift_u16_3 row 0 = 0 := by
      rcases h_su3_sel with h | h
      . exact h
      . rcases h_cb4_b with hcb | hcb <;> rw [hcb] at h <;> exact absurd h (by decide)
    -- Step 11: Case-split on (c_bits_4, c_bits_5).
    rcases h_cb5_b with hcb5 | hcb5 <;> rcases h_cb4_b with hcb4 | hcb4
    -- Case (c5=0, c4=0): shift_u16_0 = 1, a_0 = lr_0, a_1 = lr_1, shift = k_nat.
    . have hsu1 : air.cols.values.shift_u16_1 row 0 = 0 := by
        rcases h_su1_sel with h | h
        . exact h
        . rw [hcb4] at h; exact absurd h (by decide)
      have hsu0 : air.cols.values.shift_u16_0 row 0 = 1 := by
        rw [hsu1, hsu2, hsu3] at h_su_sum; linear_combination h_su_sum
      have ha0 : air.cols.values.a_0 row 0 = air.cols.values.limb_result_0 row 0 := by
        rcases h_sllw_a0_lr0 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1 : air.cols.values.a_1 row 0 = air.cols.values.limb_result_1 row 0 := by
        rcases h_sllw_a1_lr1 with h | h
        . rw [h] at hsu0; exact absurd hsu0 (by decide)
        . exact h
      have ha1_lt : (air.cols.values.a_1 row 0).val < 65536 := by rw [ha1]; exact h_lr1_lt
      -- Derive sllw_msb's relationship to a_1's MSB via U16MSBGadget.Spec.gadget_spec.
      have h_gadget_wf :
          bus_row_wf_asm (U16MSBGadget.AbsBuses 1 (air.cols.values.a_1 row 0)
                          (air.cols.values.sllw_msb.msb row 0)) := by
        simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, ByteBus.Spec]
        exact h_msb_range
      have h_gadget_cstr :
          U16MSBGadget.AbsConstraints 1 (air.cols.values.sllw_msb.msb row 0) := by
        refine ⟨by ring, ?_⟩
        rcases h_msb_b with h | h <;> rw [h] <;> ring
      have h_msb_iff := U16MSBGadget.Spec.gadget_spec 1 _ _ h_gadget_wf h_gadget_cstr rfl ha1_lt
      -- Derive c_0.val mod 32 = k_nat via c0_mod64.
      rw [hcb4, hcb5] at h_c_decomp
      have hs5_lift :
          (air.cols.values.c_bits_0 row 0 + air.cols.values.c_bits_1 row 0 * 2
            + air.cols.values.c_bits_2 row 0 * 4 + air.cols.values.c_bits_3 row 0 * 8
            + 0 * 16 + 0 * 32 : FKB).val = k_nat := by
        have heq : (air.cols.values.c_bits_0 row 0 + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4 + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 0 * 32 : FKB)
                 = (air.cols.values.c_bits_0 row 0 + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4
                  + air.cols.values.c_bits_3 row 0 * 8 : FKB) := by ring
        rw [heq, hs4_val]
      have hs5_le : (air.cols.values.c_bits_0 row 0 + air.cols.values.c_bits_1 row 0 * 2
                  + air.cols.values.c_bits_2 row 0 * 4 + air.cols.values.c_bits_3 row 0 * 8
                  + 0 * 16 + 0 * 32 : FKB).val ≤ 63 := by rw [hs5_lift]; omega
      have h_c0_mod64 := c0_mod64 _ _ hs5_le h_c_decomp
      rw [hs5_lift] at h_c0_mod64
      -- Apply ALUBus.Spec for opcode 42.
      simp only [ALUBus.Spec, RV64IM.execute_RTYPEW_pure, Sail.shift_bits_left,
                 ha0, ha1, ← h_a2_msb, ← h_a3_msb]
      refine ⟨⟨h_lr0_lt, h_lr1_lt, ?_, ?_⟩, ?_⟩
      . rcases h_msb_b with h | h <;> rw [h] <;> decide
      . rcases h_msb_b with h | h <;> rw [h] <;> decide
      -- Main BitVec identity via U32w.extend bridge.
      trans (U32w.extend
              #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                 BitVec.ofNat 16 ↑(air.cols.values.limb_result_1 row 0)] true).toBV
      . -- U64w.toBV #v[lr_0, lr_1, msb*65535, msb*65535] = (U32w.extend #v[lr_0, lr_1] true).toBV
        simp [U32w.extend, U32w.ext]
        suffices h_msb_eq :
            BitVec.ofNat 16 ↑(air.cols.values.sllw_msb.msb row 0 * 65535) =
              if U32w.negative
                  #v[BitVec.ofNat 16 ↑(air.cols.values.limb_result_0 row 0),
                     BitVec.ofNat 16 ↑(air.cols.values.limb_result_1 row 0)]
              then 65535#16 else 0#16 by
          congr
        simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
        rcases h_msb_iff with ⟨hmsb, ha_lt⟩ | ⟨hmsb, ha_ge⟩
        . rw [hmsb]
          simp
          rw [ha1] at ha_lt
          have : (air.cols.values.limb_result_1 row 0).val < 32768 := ha_lt
          omega
        . rw [hmsb]
          simp
          rw [ha1] at ha_ge
          have : 32768 ≤ (air.cols.values.limb_result_1 row 0).val := ha_ge
          omega
      . -- (U32w.extend #v[lr_0, lr_1] true).toBV = sign_extend(b.setWidth 32 << k_nat)
        simp [U32w.extend_BitVec_extend, BitVec.extend]
        congr
        apply BitVec.eq_of_toNat_eq
        simp [U32w.toNat]
        rw [Nat.mod_eq_of_lt h_lr0_lt, Nat.mod_eq_of_lt h_lr1_lt,
            Nat.mod_eq_of_lt hb0, Nat.mod_eq_of_lt hb1,
            Nat.mod_eq_of_lt hc0, Nat.mod_eq_of_lt hc1]
        have h_c_sum_mod_32 :
            ((air.cols.values.c_0 row 0).val + (air.cols.values.c_1 row 0).val * 65536) % 32
              = k_nat := by
          have heq : ((air.cols.values.c_0 row 0).val + (air.cols.values.c_1 row 0).val * 65536) % 32
              = (air.cols.values.c_0 row 0).val % 32 := by omega
          rw [heq]
          have : (air.cols.values.c_0 row 0).val % 64 = k_nat := h_c0_mod64
          omega
        rw [h_c_sum_mod_32, Nat.shiftLeft_eq,
            h_lr0_val, h_lr1_val, h_decomp_0, h_decomp_1]
        clear h_c_decomp h_carry0 h_carry1 h_carry2 h_carry3
              h_lr0 h_lr1 h_lr2 h_lr3 hv h_v01 h_v012 h_v0123
              h_lr0_lt h_lr1_lt
              h_msb_iff h_msb_b h_msb_range h_a2_msb h_a3_msb
              h_su0_sel h_su0_b h_su1_sel h_su1_b
              h_su2_sel h_su2_b h_su3_sel h_su3_b
              h_sllw_a0_lr0 h_sllw_a1_lr1 h_sllw_a0_zero h_sllw_a1_lr0
              ha0 ha1 ha1_lt
              hsu0 hsu1 hsu2 hsu3
              h_gadget_wf h_gadget_cstr
              h_c_sum_mod_32
        have hk_le' : k_nat ≤ 15 := hk_le
        interval_cases k_nat <;> omega
    . sorry
    . sorry
    . sorry

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
