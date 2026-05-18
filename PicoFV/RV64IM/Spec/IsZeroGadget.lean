import PicoFV.RV64IM.Constraints.IsZeroGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# IsZeroGadget — semantic specification (parametric)

`IsZeroGadget` produces a single bit `result` that equals `1` iff
`input = 0`, when `is_real = 1`. The gadget has no bus interactions
and no range assumption — equality is checked at the field level.

Proof: `is_real = 1` collapses the three gated constraints to
- (a) `result = 1 - inverse · input`
- (b) `result ∈ {0, 1}`
- (c) `result · input = 0`

(b) gives the boolean conclusion directly. For the equivalence:
- `result = 1`: by (c), `input = 0`.
- `input = 0`: by (a), `result = 1`.

The witness column `inverse` is exposed as an explicit parameter,
matching the rest of the gadget Specs in this directory
(`U16MSBGadget`, `LtWordU16Gadget`, `LtSignedGadget`,
`U16ToU8GadgetSafe`). Callers in chip Specs pass the chip's own
`inverse` column accessor.
-/

namespace IsZeroGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec. -/
  lemma gadget_spec
    (is_real input inverse result : FKB)
    (h_gadget_constraints :
      IsZeroGadget.AbsConstraints is_real input inverse result)
    (h_is_real : is_real = 1)
  :
    (result = 0 ∨ result = 1) ∧
    ((result = 1) ↔ (input = 0))
  := by
    simp [IsZeroGadget.AbsConstraints, h_is_real] at h_gadget_constraints
    grind

end IsZeroGadget.Spec
