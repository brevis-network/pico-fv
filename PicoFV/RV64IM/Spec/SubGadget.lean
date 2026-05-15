import PicoFV.RV64IM.Constraints.SubGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SubGadget — semantic specification (parametric)

The `SubGadget.Spec` namespace below states the *parametric* semantic
content of the gadget: under the gadget's constraints and external u16
range assumptions on the operand limbs, the result word satisfies the
actual 64-bit subtraction `value = b - c` (computed in `BitVec 64`).

Since `SubGadget` is used in exactly one chip (`SubChip`), this file
provides only the pure `gadget_spec`. There is no standalone
`Valid_SubGadgetAir`, so no air-based `spec` wrapper or `ext_asrt` /
`wf_asrt` lemmas are defined here — the chip embedding the gadget
plumbs its own hypotheses through to `gadget_spec`.
-/

namespace SubGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec: stated entirely in terms of the 13
      `FKB` column values that flow through the gadget. No mention of an
      air or a row. The chip-side spec recovers the gadget's `AbsBuses`
      and `AbsConstraints` hypotheses from its own air-based hypotheses
      via `bus_row_abs` / `allHold_abs` (+ the `_append` lemmas to split
      gadget vs chip portions) and then invokes this lemma with its own
      accessors substituted for the parameters. -/
  lemma gadget_spec
    (is_real
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     value_0 value_1 value_2 value_3 : FKB)
    (_h_gadget_ext_asm :
      bus_row_ext_asm
        (SubGadget.AbsBuses is_real value_0 value_1 value_2 value_3))
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (SubGadget.AbsBuses is_real value_0 value_1 value_2 value_3))
    (h_gadget_constraints :
      SubGadget.AbsConstraints
        is_real b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
        value_0 value_1 value_2 value_3)
    (h_is_real : is_real = 1)
    (h_b_range :
      b_0.val < 65536 ∧ b_1.val < 65536 ∧
      b_2.val < 65536 ∧ b_3.val < 65536)
    (h_c_range :
      c_0.val < 65536 ∧ c_1.val < 65536 ∧
      c_2.val < 65536 ∧ c_3.val < 65536)
  :
    value_0.val < 65536 ∧
    value_1.val < 65536 ∧
    value_2.val < 65536 ∧
    value_3.val < 65536 ∧
    U64w.toBV #v[value_0, value_1, value_2, value_3]
    =
    U64w.toBV #v[b_0, b_1, b_2, b_3]
    -
    U64w.toBV #v[c_0, c_1, c_2, c_3]
  := by
    simp [bus_row_wf_asm, AbsBuses, h_is_real, ByteBus.Spec] at h_gadget_wf_asm
    simp [h_gadget_wf_asm]
    simp [AbsConstraints, h_is_real, sub_eq_zero] at h_gadget_constraints
    obtain ⟨ h0, h1, h2, h3 ⟩ := h_gadget_constraints
    apply BitVec.eq_of_toNat_eq
    simp [U64w.toNat, BitVec.toNat_sub]
    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
    obtain h0 | h0 := h0 <;> simp [h0] at h1 h2 h3
    . replace h0 : value_0 = b_0 + 65536 - c_0 := by grind
      obtain h1 | h1 := h1 <;> simp [h1] at h2 h3
      . rw [sub_eq_zero] at h1; symm at h1
        obtain h2 | h2 := h2 <;> simp [h2] at h3
        . obtain h3 | h3 := h3
          . omega
          . replace h3 : value_3 = b_3 - 1 - c_3 := by grind
            omega
        . replace h2 : value_2 = b_2 - 1 - c_2 := by grind
          obtain h3 | h3 := h3
          . replace h3 : value_3 = b_3 + 65536 - c_3 := by grind
            omega
          . replace h3 : value_3 = b_3 - c_3 := by grind
            omega
      . replace h1 : value_1 = b_1 - 1 - c_1 := by grind
        obtain h2 | h2 := h2 <;> simp [h2] at h3
        . replace h2 : value_2 = b_2 + 65536 - c_2 := by grind
          obtain h3 | h3 := h3
          . omega
          . replace h3 : value_3 = b_3 - 1 - c_3 := by grind
            omega
        . replace h2 : value_2 = b_2 - c_2 := by grind
          obtain h3 | h3 := h3
          . replace h3 : value_3 = b_3 + 65536 - c_3 := by grind
            omega
          . replace h3 : value_3 = b_3 - c_3 := by grind
            omega
    . replace h0 : value_0 = b_0 - c_0 := by grind
      obtain h1 | h1 := h1 <;> simp [h1] at h2 h3
      . replace h1 : value_1 = b_1 + 65536 - c_1 := by grind
        obtain h2 | h2 := h2 <;> simp [h2] at h3
        . obtain h3 | h3 := h3
          . omega
          . replace h3 : value_3 = b_3 - 1 - c_3 := by grind
            omega
        . replace h2 : value_2 = b_2 - 1 - c_2 := by grind
          obtain h3 | h3 := h3
          . replace h3 : value_3 = b_3 + 65536 - c_3 := by grind
            omega
          . replace h3 : value_3 = b_3 - c_3 := by grind
            omega
      . replace h1 : value_1 = b_1 - c_1 := by grind
        obtain h2 | h2 := h2 <;> simp [h2] at h3
        . replace h2 : value_2 = b_2 + 65536 - c_2 := by grind
          obtain h3 | h3 := h3
          . omega
          . replace h3 : value_3 = b_3 - 1 - c_3 := by grind
            omega
        . replace h2 : value_2 = b_2 - c_2 := by grind
          obtain h3 | h3 := h3
          . replace h3 : value_3 = b_3 + 65536 - c_3 := by grind
            omega
          . replace h3 : value_3 = b_3 - c_3 := by grind
            omega

end SubGadget.Spec
