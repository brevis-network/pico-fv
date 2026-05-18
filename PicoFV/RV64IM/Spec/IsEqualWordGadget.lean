import PicoFV.RV64IM.Constraints.IsEqualWordGadget
import PicoFV.RV64IM.Spec.IsZeroWordGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# IsEqualWordGadget — semantic specification (parametric)

`IsEqualWordGadget` produces a single bit `result` that equals `1` iff
the two input 4-limb words are equal limbwise in `FKB`. Reduces to
`IsZeroWordGadget` on the differences.

All 10 internal witness columns are exposed as explicit parameters,
matching the rest of the gadget Specs.
-/

namespace IsEqualWordGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec. -/
  lemma gadget_spec
    (is_real
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     inverse_0 inverse_1 inverse_2 inverse_3
     result_0 result_1 result_2 result_3
     is_lower_half_zero is_upper_half_zero
     result : FKB)
    (h_gadget_constraints :
      IsEqualWordGadget.AbsConstraints is_real
        a_0 a_1 a_2 a_3
        b_0 b_1 b_2 b_3
        inverse_0 inverse_1 inverse_2 inverse_3
        result_0 result_1 result_2 result_3
        is_lower_half_zero is_upper_half_zero result)
    (h_is_real : is_real = 1)
  :
    (result = 0 ∨ result = 1) ∧
    ((result = 1) ↔
      (a_0 = b_0 ∧ a_1 = b_1 ∧ a_2 = b_2 ∧ a_3 = b_3))
  := by
    obtain ⟨_h_real, h_iszw⟩ := h_gadget_constraints
    have h_spec := IsZeroWordGadget.Spec.gadget_spec
      is_real
      (a_0 - b_0) (a_1 - b_1) (a_2 - b_2) (a_3 - b_3)
      inverse_0 inverse_1 inverse_2 inverse_3
      result_0 result_1 result_2 result_3
      is_lower_half_zero is_upper_half_zero result
      h_iszw h_is_real
    clear h_iszw _h_real h_is_real
    grind

end IsEqualWordGadget.Spec
