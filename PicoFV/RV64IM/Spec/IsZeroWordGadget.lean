import PicoFV.RV64IM.Constraints.IsZeroWordGadget
import PicoFV.RV64IM.Spec.IsZeroGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# IsZeroWordGadget — semantic specification (parametric)

`IsZeroWordGadget` produces a single bit `result` that equals `1` iff
all four u16 limbs of the input word are simultaneously zero (in
`FKB`). No range hypotheses are required — the gadget tests field
equality with `0`, not "the word represents the integer 0".

Proof: invoke `IsZeroGadget.Spec.gadget_spec` four times to obtain
`result_i ∈ {0, 1}` and `result_i = 1 ↔ input_i = 0` for each limb,
then chain through the AND-tree product definitions and let `grind`
finish.

All 10 internal witness columns (4 × `inverse_i`, 4 × per-limb
`result_i`, plus `is_lower_half_zero` and `is_upper_half_zero`) are
exposed as explicit parameters, matching the rest of the gadget Specs.
-/

namespace IsZeroWordGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec. -/
  lemma gadget_spec
    (is_real
     input_0 input_1 input_2 input_3
     inverse_0 inverse_1 inverse_2 inverse_3
     result_0 result_1 result_2 result_3
     is_lower_half_zero is_upper_half_zero
     result : FKB)
    (h_gadget_constraints :
      IsZeroWordGadget.AbsConstraints is_real
        input_0 input_1 input_2 input_3
        inverse_0 inverse_1 inverse_2 inverse_3
        result_0 result_1 result_2 result_3
        is_lower_half_zero is_upper_half_zero result)
    (h_is_real : is_real = 1)
  :
    (result = 0 ∨ result = 1) ∧
    ((result = 1) ↔
      (input_0 = 0 ∧ input_1 = 0 ∧ input_2 = 0 ∧ input_3 = 0))
  := by
    obtain ⟨h0, h1, h2, h3, _h_real, _h_lo, _h_up, _h_res,
             h_lo_def, h_up_def, h_res_def⟩ := h_gadget_constraints
    have h_spec_0 := IsZeroGadget.Spec.gadget_spec
      is_real input_0 inverse_0 result_0 h0 h_is_real
    have h_spec_1 := IsZeroGadget.Spec.gadget_spec
      is_real input_1 inverse_1 result_1 h1 h_is_real
    have h_spec_2 := IsZeroGadget.Spec.gadget_spec
      is_real input_2 inverse_2 result_2 h2 h_is_real
    have h_spec_3 := IsZeroGadget.Spec.gadget_spec
      is_real input_3 inverse_3 result_3 h3 h_is_real
    simp [h_is_real] at h_lo_def h_up_def h_res_def
    clear h0 h1 h2 h3 _h_real _h_lo _h_up _h_res h_is_real
    grind

end IsZeroWordGadget.Spec
