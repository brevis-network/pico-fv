import PicoFV.RV64IM.Constraints.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# U16MSBGadget — semantic specification (parametric)

`U16MSBGadget` pins its `msb` column to bit-15 of an externally-
supplied `value`, *provided* the parent guarantees `value < 65536`.
The gadget has no standalone wrapping air — it's always embedded in
a parent gadget or chip — so this file provides only the parametric
`gadget_spec`.

The conclusion exposes both the boolean status of `msb` and the
implied range partition of `value`:

- `msb = 0 ∧ value.val < 32768` (bit-15 of `value` is 0), or
- `msb = 1 ∧ 32768 ≤ value.val` (bit-15 of `value` is 1).

Together with the parent's `value.val < 65536` hypothesis, this fully
determines the sign-extension behavior expected by ADDW/SUBW/MULW
and by signed comparisons (SLT, MULH, MULHSU, ShiftRightChip's `b_msb`).
-/

namespace U16MSBGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec: given the constraints, the byte-bus
      consistency entry's wf-assumption, `is_real = 1`, and
      `value.val < 65536` (supplied externally — typically from a
      parent's U16Range on `value` itself), conclude that `msb` is
      exactly bit-15 of `value`. -/
  lemma gadget_spec
    (is_real value msb : FKB)
    (h_gadget_wf_asm :
      bus_row_wf_asm (U16MSBGadget.AbsBuses is_real value msb))
    (h_gadget_constraints :
      U16MSBGadget.AbsConstraints is_real msb)
    (h_is_real : is_real = 1)
    (h_value_range : value.val < 65536)
  :
    (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)
  := by
    simp [bus_row_wf_asm, U16MSBGadget.AbsBuses, h_is_real, ByteBus.Spec]
      at h_gadget_wf_asm
    grind [U16MSBGadget.AbsConstraints]

end U16MSBGadget.Spec
