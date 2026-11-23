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

  /-- The `u16_flags` sum is the operands' inequality indicator: it is
      boolean, and it is zero exactly when the two operands are equal.

      `gadget_spec` above says what `bit` means; this says what the flag
      sum means. `LtChip` needs both on its merged branch-comparison
      rows, where the chip pins `a_1 = is_cmp · (Σ u16_flags − bit)`
      (`alu/lt/constraints.rs:54-66`): with `bit = [a < b]` the
      difference is the strict `[b < a]` precisely because
      `Σ u16_flags = [a ≠ b]`.

      Unlike `gadget_spec` this needs no bus-side hypothesis: the flag
      sum's meaning comes from the limb-equality and `not_eq_inv`
      constraints alone. -/
  lemma flags_sum_spec
    (is_real
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
     not_eq_inv
     comparison_limbs_0 comparison_limbs_1
     bit : FKB)
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
    (u16_flags_0 + u16_flags_1 + u16_flags_2 + u16_flags_3 = 0 ∨
     u16_flags_0 + u16_flags_1 + u16_flags_2 + u16_flags_3 = 1) ∧
    ((u16_flags_0 + u16_flags_1 + u16_flags_2 + u16_flags_3 = 0) ↔
      (U64w.toBV #v[a_0, a_1, a_2, a_3]).toNat
        = (U64w.toBV #v[b_0, b_1, b_2, b_3]).toNat)
  := by
    simp [AbsConstraints, h_is_real, sub_eq_zero] at h_gadget_constraints
    obtain ⟨ h_f0, h_f1, h_f2, h_f3, h_sum, h_c6, h_c7, h_c8, h_c9,
             h_c10, h_c11, h_c12, _h_bit ⟩ := h_gadget_constraints
    refine ⟨h_sum, ?_⟩
    obtain ⟨ha_0, ha_1, ha_2, ha_3⟩ := h_a_range
    obtain ⟨hb_0, hb_1, hb_2, hb_3⟩ := h_b_range
    simp [U64w.toNat]
    constructor
    . -- A zero flag sum makes every limb-equality constraint fire.
      intro h_zero
      have e_3 : a_3 = b_3 := by clear *- h_c6 h_f3 h_zero h_f0 h_f1 h_f2; grind
      have e_2 : a_2 = b_2 := by clear *- h_c7 h_f3 h_f2 h_zero h_f0 h_f1; grind
      have e_1 : a_1 = b_1 := by clear *- h_c8 h_f3 h_f2 h_f1 h_zero h_f0; grind
      have e_0 : a_0 = b_0 := by clear *- h_c9 h_f3 h_f2 h_f1 h_f0 h_zero; grind
      rw [e_0, e_1, e_2, e_3]
    . -- Equal operands force the flag sum to zero: a sum of `1` makes
      -- `not_eq_inv` witness `comparison_limbs_0 ≠ comparison_limbs_1`,
      -- but those are the same weighted sum once the limbs agree.
      intro h_eq
      have v_0 : (a_0 : ℕ) = (b_0 : ℕ) := by omega
      have v_1 : (a_1 : ℕ) = (b_1 : ℕ) := by omega
      have v_2 : (a_2 : ℕ) = (b_2 : ℕ) := by omega
      have v_3 : (a_3 : ℕ) = (b_3 : ℕ) := by omega
      have e_0 : a_0 = b_0 := Fin.val_inj.mp v_0
      have e_1 : a_1 = b_1 := Fin.val_inj.mp v_1
      have e_2 : a_2 = b_2 := Fin.val_inj.mp v_2
      have e_3 : a_3 = b_3 := Fin.val_inj.mp v_3
      rcases h_sum with h | h
      . exact h
      . exfalso
        have h_inv : not_eq_inv * (comparison_limbs_0 - comparison_limbs_1) = 1 := by
          clear *- h_c12 h; grind
        rw [e_0, e_1, e_2, e_3] at h_c10
        have h_same : comparison_limbs_0 = comparison_limbs_1 := by
          rw [← h_c10, ← h_c11]
        rw [h_same] at h_inv
        simp at h_inv

end LtWordU16Gadget.Spec
