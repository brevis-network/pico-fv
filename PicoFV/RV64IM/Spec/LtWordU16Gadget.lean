import PicoFV.RV64IM.Constraints.LtWordU16Gadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# LtWordU16Gadget — semantic specification (parametric)

`LtWordU16Gadget` produces a single bit `bit` indicating whether
`U64w.toBV a < U64w.toBV b` (unsigned). The gadget has no standalone
wrapping air — used only inside `LtSignedGadget` inside `LtChip`. This
file therefore provides only the parametric `gadget_spec`.

Proof strategy: case-split on the sum of `u16_flags`.

- **sum = 0**: all flags are 0, so the conditional limb-equality
  constraints force `a_i = b_i` for all `i`. Hence `a = b` as
  `U64w`s, and the byte-bus U16Range on `0 + bit*65536` forces
  `bit = 0` (since otherwise it'd be `≥ 65536`). The comparison
  `a < b` is false, matching `bit = 0`.

- **sum = 1**: exactly one flag is set — the most-significant
  differing limb (MSDL). Constraints 6–9 force `a_i = b_i` for
  every limb *above* the MSDL. Constraint 12 (with `not_eq_inv`)
  forces `comp_0 ≠ comp_1`, i.e., the MSDL is genuinely a differing
  limb. The byte-bus U16Range on `(comp_0 - comp_1) + bit*65536`
  pins `bit = 1 ⟺ comp_0 < comp_1` at the MSDL, which dominates the
  full-word comparison since higher limbs are equal.
-/

namespace LtWordU16Gadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec. -/
  lemma gadget_spec
    (is_real
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
     not_eq_inv
     comparison_limbs_0 comparison_limbs_1
     bit : FKB)
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (LtWordU16Gadget.AbsBuses is_real comparison_limbs_0 comparison_limbs_1 bit))
    (h_gadget_constraints :
      LtWordU16Gadget.AbsConstraints
        is_real a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3
        u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
        not_eq_inv comparison_limbs_0 comparison_limbs_1 bit)
    (h_is_real : is_real = 1)
    (h_a_range :
      a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536)
    (h_b_range :
      b_0.val < 65536 ∧ b_1.val < 65536 ∧ b_2.val < 65536 ∧ b_3.val < 65536)
  :
    (bit = 0 ∨ bit = 1) ∧
    ((bit = 1) ↔
      (U64w.toBV #v[a_0, a_1, a_2, a_3]).toNat
        < (U64w.toBV #v[b_0, b_1, b_2, b_3]).toNat)
  := by
    -- Extract byte-bus assumption
    simp [bus_row_wf_asm, AbsBuses, h_is_real, ByteBus.Spec] at h_gadget_wf_asm
    -- Simplify constraints
    simp [AbsConstraints, h_is_real, sub_eq_zero] at h_gadget_constraints
    obtain ⟨ h_f0, h_f1, h_f2, h_f3, h_sum, h_c6, h_c7, h_c8, h_c9,
             h_c10, h_c11, h_c12, h_bit ⟩ := h_gadget_constraints
    -- Reduce U64w.toBV.toNat to U64w.toNat to expose limb sums
    refine ⟨h_bit, ?_⟩
    -- Case-split on the sum of flags
    simp [U64w.toNat]
    grind

end LtWordU16Gadget.Spec
