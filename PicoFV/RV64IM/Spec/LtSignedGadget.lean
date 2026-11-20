import PicoFV.RV64IM.Constraints.LtSignedGadget
import PicoFV.RV64IM.Spec.U16MSBGadget
import PicoFV.RV64IM.Spec.LtWordU16Gadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# LtSignedGadget — semantic specification (parametric)

`LtSignedGadget` produces a single bit `bit` indicating either the
*signed* or *unsigned* comparison `a < b` depending on the parent's
`is_signed` flag. It works by feeding `LtWordU16Gadget` the
*msb-flipped* top limb (`x + is_signed*32768 - 65536*msb_x`) so that
unsigned comparison on the shifted limbs matches the signed comparison
on the original — the standard "XOR top bit" trick, with `msb_x`
materialized by an embedded `U16MSBGadget`.

Proof strategy:
1. Decompose `AbsBuses` and `AbsConstraints` into the three sub-gadget
   contributions (2× `U16MSBGadget` + 1× `LtWordU16Gadget`).
2. When `is_signed = 0`: the gadget's own constraints force
   `b_msb = c_msb = 0`, so the shifted top limbs equal the originals,
   and `LtWordU16Gadget.Spec.gadget_spec` gives the unsigned compare
   directly.
3. When `is_signed = 1`: `is_real = 1` (from the own constraint
   `(is_real - 1) * is_signed = 0`), `U16MSBGadget.Spec.gadget_spec`
   pins `b_msb`/`c_msb` to the actual msbs of `a_3`/`b_3`, and the
   shifted-top-limb unsigned comparison equals the signed comparison
   via the identity `shifted.toNat = original.toInt + 2^63`.
-/

namespace LtSignedGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec. -/
  lemma gadget_spec
    (is_real is_signed
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
     not_eq_inv
     comparison_limbs_0 comparison_limbs_1
     bit
     b_msb c_msb : FKB)
    (h_gadget_ext_asm :
      bus_row_ext_asm
        (LtSignedGadget.AbsBuses is_real is_signed a_3 b_3
          comparison_limbs_0 comparison_limbs_1 bit b_msb c_msb))
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (LtSignedGadget.AbsBuses is_real is_signed a_3 b_3
          comparison_limbs_0 comparison_limbs_1 bit b_msb c_msb))
    (h_gadget_constraints :
      LtSignedGadget.AbsConstraints
        is_real is_signed
        a_0 a_1 a_2 a_3
        b_0 b_1 b_2 b_3
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit
        b_msb c_msb)
    (h_is_real : is_real = 1)
    (h_a_range :
      a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536)
    (h_b_range :
      b_0.val < 65536 ∧ b_1.val < 65536 ∧ b_2.val < 65536 ∧ b_3.val < 65536)
  :
    (bit = 0 ∨ bit = 1) ∧
    (is_signed = 0 → ((bit = 1) ↔
      (U64w.toBV #v[a_0, a_1, a_2, a_3]).toNat
        < (U64w.toBV #v[b_0, b_1, b_2, b_3]).toNat)) ∧
    (is_signed = 1 → ((bit = 1) ↔
      (U64w.toBV #v[a_0, a_1, a_2, a_3]).toInt
        < (U64w.toBV #v[b_0, b_1, b_2, b_3]).toInt))
  := by
    -- Decompose AbsBuses and AbsConstraints into sub-gadget contributions
    simp [AbsBuses] at h_gadget_wf_asm h_gadget_ext_asm
    obtain ⟨⟨h_wf_msb1, h_wf_msb2⟩, h_wf_lt⟩ := h_gadget_wf_asm
    obtain ⟨⟨h_ext_msb1, h_ext_msb2⟩, h_ext_lt⟩ := h_gadget_ext_asm
    obtain ⟨h_own1, h_own2, h_own3, h_msb1, h_msb2, h_lt⟩ := h_gadget_constraints
    -- The LtWordU16Gadget constraints alone give us bit ∈ {0, 1}
    have h_bit : bit = 0 ∨ bit = 1 := by
      simp [LtWordU16Gadget.AbsConstraints, h_is_real, sub_eq_zero] at h_lt
      grind
    refine ⟨h_bit, ?_, ?_⟩
    . -- is_signed = 0: shifted operands equal originals, unsigned compare
      intro h_zero
      subst h_zero
      have hb_msb : b_msb = 0 := by grind
      have hc_msb : c_msb = 0 := by grind
      have h_lt_spec := LtWordU16Gadget.Spec.gadget_spec
        is_real a_0 a_1 a_2 (a_3 + 0 * 32768 - 65536 * b_msb)
        b_0 b_1 b_2 (b_3 + 0 * 32768 - 65536 * c_msb)
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit
        h_wf_lt h_lt h_is_real
        ⟨h_a_range.1, h_a_range.2.1, h_a_range.2.2.1, by rw [hb_msb]; simp; exact h_a_range.2.2.2⟩
        ⟨h_b_range.1, h_b_range.2.1, h_b_range.2.2.1, by rw [hc_msb]; simp; exact h_b_range.2.2.2⟩
      obtain ⟨_, h_iff⟩ := h_lt_spec
      rw [hb_msb, hc_msb] at h_iff
      simpa using h_iff
    . -- is_signed = 1: shifted top limb = msb-flipped, gives signed compare
      intro h_one
      subst h_one
      -- Get the b_msb / c_msb partition facts from U16MSBGadget.Spec
      have h_a3_lt : a_3.val < 65536 := h_a_range.2.2.2
      have h_b3_lt : b_3.val < 65536 := h_b_range.2.2.2
      have h_b_msb_part := U16MSBGadget.Spec.gadget_spec
        1 a_3 b_msb h_wf_msb1 h_msb1 rfl h_a3_lt
      have h_c_msb_part := U16MSBGadget.Spec.gadget_spec
        1 b_3 c_msb h_wf_msb2 h_msb2 rfl h_b3_lt
      -- Range hypotheses for the shifted top limbs
      have h_shifted_a3 : (a_3 + 1 * 32768 - 65536 * b_msb : FKB).val < 65536 := by
        rcases h_b_msb_part with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> grind
      have h_shifted_b3 : (b_3 + 1 * 32768 - 65536 * c_msb : FKB).val < 65536 := by
        rcases h_c_msb_part with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> grind
      -- Apply LtWordU16Gadget.Spec on the shifted operands
      have h_lt_spec := LtWordU16Gadget.Spec.gadget_spec
        is_real a_0 a_1 a_2 (a_3 + 1 * 32768 - 65536 * b_msb)
        b_0 b_1 b_2 (b_3 + 1 * 32768 - 65536 * c_msb)
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit
        h_wf_lt h_lt h_is_real
        ⟨h_a_range.1, h_a_range.2.1, h_a_range.2.2.1, h_shifted_a3⟩
        ⟨h_b_range.1, h_b_range.2.1, h_b_range.2.2.1, h_shifted_b3⟩
      obtain ⟨_, h_iff⟩ := h_lt_spec
      -- Bridge identity: shifted.toNat = original.toInt + 2^63 (as Int)
      -- Holds for both b_msb partition cases (b_msb = 0 with a_3 < 2^15, or
      -- b_msb = 1 with a_3 ≥ 2^15) because:
      --   b_msb = 0: shifted_a_3.val = a_3.val + 32768, a.msb = false,
      --     a.toInt = a.toNat. shifted.toNat = a.toNat + 2^63.
      --   b_msb = 1: shifted_a_3.val = a_3.val - 32768, a.msb = true,
      --     a.toInt = a.toNat - 2^64. shifted.toNat = a.toNat - 2^63
      --     = a.toInt + 2^64 - 2^63 = a.toInt + 2^63.
      have h_a_bridge :
        ((U64w.toBV #v[a_0, a_1, a_2,
          (a_3 + 1 * 32768 - 65536 * b_msb : FKB)]).toNat : ℤ)
        = (U64w.toBV #v[a_0, a_1, a_2, a_3]).toInt + 2^63 := by
        simp only [U64w.toBV_toNat, U64w.toBV_toInt]
        unfold U64w.toInt
        simp only [← U64w.msb_3_negative, BitVec.msb_eq_decide]
        rcases h_b_msb_part with ⟨h, h'⟩ | ⟨h, h'⟩
        all_goals
          subst h
          simp only [U64w.toNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
          repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
          grind
      have h_b_bridge :
        ((U64w.toBV #v[b_0, b_1, b_2,
          (b_3 + 1 * 32768 - 65536 * c_msb : FKB)]).toNat : ℤ)
        = (U64w.toBV #v[b_0, b_1, b_2, b_3]).toInt + 2^63 := by
        simp only [U64w.toBV_toNat, U64w.toBV_toInt]
        unfold U64w.toInt
        simp only [← U64w.msb_3_negative, BitVec.msb_eq_decide]
        rcases h_c_msb_part with ⟨h, h'⟩ | ⟨h, h'⟩
        all_goals
          subst h
          simp only [U64w.toNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
          repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
          grind
      -- Push through
      constructor <;> grind

  /-- The embedded `LtWordU16Gadget`'s flag sum is the inequality
      indicator for this gadget's own (unshifted) operands: it is
      boolean, and zero exactly when they are equal.

      `gadget_spec` lifts the gadget's `bit` through the sign
      adjustment because that adjustment preserves order; this lifts
      the flag sum through it because it is a bijection, so it
      preserves equality too. The adjusted top limb and the original
      are related by `shifted.toNat = original.toInt + 2^63`, the same
      bridge `gadget_spec` uses.

      `LtChip` needs this on its merged branch-comparison rows: the
      chip pins `a_1 = is_cmp · (Σ u16_flags − bit)`, which is the
      strict `[b < a]` exactly when `Σ u16_flags = [a ≠ b]`. -/
  lemma flags_sum_spec
    (is_real is_signed
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
     not_eq_inv
     comparison_limbs_0 comparison_limbs_1
     bit
     b_msb c_msb : FKB)
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (LtSignedGadget.AbsBuses is_real is_signed a_3 b_3
          comparison_limbs_0 comparison_limbs_1 bit b_msb c_msb))
    (h_gadget_constraints :
      LtSignedGadget.AbsConstraints
        is_real is_signed
        a_0 a_1 a_2 a_3
        b_0 b_1 b_2 b_3
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit
        b_msb c_msb)
    (h_is_real : is_real = 1)
    (h_is_signed : is_signed = 0 ∨ is_signed = 1)
    (h_a_range :
      a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536)
    (h_b_range :
      b_0.val < 65536 ∧ b_1.val < 65536 ∧ b_2.val < 65536 ∧ b_3.val < 65536)
  :
    (u16_flags_0 + u16_flags_1 + u16_flags_2 + u16_flags_3 = 0 ∨
     u16_flags_0 + u16_flags_1 + u16_flags_2 + u16_flags_3 = 1) ∧
    ((u16_flags_0 + u16_flags_1 + u16_flags_2 + u16_flags_3 = 0) ↔
      (U64w.toBV #v[a_0, a_1, a_2, a_3]).toNat
        = (U64w.toBV #v[b_0, b_1, b_2, b_3]).toNat)
  := by
    simp [AbsBuses] at h_gadget_wf_asm
    obtain ⟨⟨h_wf_msb1, h_wf_msb2⟩, _h_wf_lt⟩ := h_gadget_wf_asm
    obtain ⟨_h_own1, h_own2, h_own3, h_msb1, h_msb2, h_lt⟩ := h_gadget_constraints
    rcases h_is_signed with h_zero | h_one
    . -- Unsigned: the adjustment is the identity.
      subst h_zero
      have hb_msb : b_msb = 0 := by grind
      have hc_msb : c_msb = 0 := by grind
      have h := LtWordU16Gadget.Spec.flags_sum_spec
        is_real a_0 a_1 a_2 (a_3 + 0 * 32768 - 65536 * b_msb)
        b_0 b_1 b_2 (b_3 + 0 * 32768 - 65536 * c_msb)
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit
        h_lt h_is_real
        ⟨h_a_range.1, h_a_range.2.1, h_a_range.2.2.1,
          by rw [hb_msb]; simp; exact h_a_range.2.2.2⟩
        ⟨h_b_range.1, h_b_range.2.1, h_b_range.2.2.1,
          by rw [hc_msb]; simp; exact h_b_range.2.2.2⟩
      rw [hb_msb, hc_msb] at h
      simpa using h
    . -- Signed: bridge the msb-flipped top limb back to the original.
      subst h_one
      have h_a3_lt : a_3.val < 65536 := h_a_range.2.2.2
      have h_b3_lt : b_3.val < 65536 := h_b_range.2.2.2
      have h_b_msb_part := U16MSBGadget.Spec.gadget_spec
        1 a_3 b_msb h_wf_msb1 h_msb1 rfl h_a3_lt
      have h_c_msb_part := U16MSBGadget.Spec.gadget_spec
        1 b_3 c_msb h_wf_msb2 h_msb2 rfl h_b3_lt
      have h_shifted_a3 : (a_3 + 1 * 32768 - 65536 * b_msb : FKB).val < 65536 := by
        rcases h_b_msb_part with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> grind
      have h_shifted_b3 : (b_3 + 1 * 32768 - 65536 * c_msb : FKB).val < 65536 := by
        rcases h_c_msb_part with ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> grind
      have h := LtWordU16Gadget.Spec.flags_sum_spec
        is_real a_0 a_1 a_2 (a_3 + 1 * 32768 - 65536 * b_msb)
        b_0 b_1 b_2 (b_3 + 1 * 32768 - 65536 * c_msb)
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit
        h_lt h_is_real
        ⟨h_a_range.1, h_a_range.2.1, h_a_range.2.2.1, h_shifted_a3⟩
        ⟨h_b_range.1, h_b_range.2.1, h_b_range.2.2.1, h_shifted_b3⟩
      have h_a_bridge :
        ((U64w.toBV #v[a_0, a_1, a_2,
          (a_3 + 1 * 32768 - 65536 * b_msb : FKB)]).toNat : ℤ)
        = (U64w.toBV #v[a_0, a_1, a_2, a_3]).toInt + 2^63 := by
        simp only [U64w.toBV_toNat, U64w.toBV_toInt]
        unfold U64w.toInt
        simp only [← U64w.msb_3_negative, BitVec.msb_eq_decide]
        rcases h_b_msb_part with ⟨h, h'⟩ | ⟨h, h'⟩
        all_goals
          subst h
          simp only [U64w.toNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
          repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
          grind
      have h_b_bridge :
        ((U64w.toBV #v[b_0, b_1, b_2,
          (b_3 + 1 * 32768 - 65536 * c_msb : FKB)]).toNat : ℤ)
        = (U64w.toBV #v[b_0, b_1, b_2, b_3]).toInt + 2^63 := by
        simp only [U64w.toBV_toNat, U64w.toBV_toInt]
        unfold U64w.toInt
        simp only [← U64w.msb_3_negative, BitVec.msb_eq_decide]
        rcases h_c_msb_part with ⟨h, h'⟩ | ⟨h, h'⟩
        all_goals
          subst h
          simp only [U64w.toNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
          repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
          grind
      obtain ⟨h_sum_bool, h_iff⟩ := h
      refine ⟨h_sum_bool, ?_⟩
      rw [h_iff]
      constructor <;> intro hh
      . -- Equal adjusted operands: the bridge turns that into equal
        -- `toInt`s, and `toInt` determines the word.
        have h_int : (U64w.toBV #v[a_0, a_1, a_2, a_3]).toInt
                   = (U64w.toBV #v[b_0, b_1, b_2, b_3]).toInt := by omega
        exact congrArg BitVec.toNat (BitVec.toInt_inj.mp h_int)
      . have h_bv : (U64w.toBV #v[a_0, a_1, a_2, a_3])
                  = (U64w.toBV #v[b_0, b_1, b_2, b_3]) := BitVec.toNat_inj.mp hh
        rw [h_bv] at h_a_bridge
        omega

end LtSignedGadget.Spec
