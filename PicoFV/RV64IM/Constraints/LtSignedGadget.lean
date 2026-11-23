import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.LtSignedGadget
import PicoFV.RV64IM.Airs.LtSignedGadget
import PicoFV.RV64IM.Constraints.LtWordU16Gadget
import PicoFV.RV64IM.Constraints.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# LtSignedGadget — abstract constraints & buses

`LtSignedGadget`'s Pico Rust source is
`vm/src/chips/gadgets/lt_signed.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The gadget extends
`LtWordU16Gadget` with the standard signed-via-unsigned-compare trick:
the top u16 limb of each operand is XOR'd with `0x8000` when
`is_signed = 1`, expressed arithmetically as
`a_3 + is_signed*32768 - 65536*b_msb` (where `b_msb` is the msb of
`a_3`, materialized by an embedded `U16MSBGadget`). After this flip,
the unsigned comparison done by `LtWordU16Gadget` on the shifted limbs
matches the signed comparison on the original.

Layout (in the standalone extraction; 20 columns total):
| Cols   | Role                                              |
|--------|---------------------------------------------------|
| 0..3   | `a_0..a_3` (operand 1, supplied by parent)        |
| 4..7   | `b_0..b_3` (operand 2, supplied by parent)        |
| 8..15  | `LtWordU16Gadget` columns                         |
| 16     | `b_msb`  (msb of `a_3`, U16MSBGadget #1)          |
| 17     | `c_msb`  (msb of `b_3`, U16MSBGadget #2)          |
| 18     | `is_signed` (parent flag — selects signed vs unsigned) |
| 19     | `is_real` (parent's activation flag)              |

The 24 algebraic constraints decompose as:
- 15 from `LtWordU16Gadget` (invoked with the **shifted** top limbs)
- 2 each from the two `U16MSBGadget` instances (using `is_signed` as
  the `is_real` selector — so the msb consistency only fires for SLT)
- 3 substantive own constraints (plus 2 bool duplicates absorbed by
  the sub-gadgets' bools):
    * `is_signed ⟹ is_real`              (signed compares are only real rows)
    * `¬is_signed ⟹ b_msb = 0`           (msb columns are zeroed for unsigned)
    * `¬is_signed ⟹ c_msb = 0`

The 3 byte-bus entries decompose as:
- 1 from each `U16MSBGadget` (the `2*v - msb*65536` consistency check
  for `a_3` and `b_3`, gated by `+is_signed`)
- 1 from `LtWordU16Gadget` (the `Δ + bit*65536` comparison entry,
  gated by `+is_real`)
-/

namespace LtSignedGadget

  open RV64IM_Interactions

  /-- Algebraic constraints emitted by Pico's `LtSignedGadget`,
      parametric in the 20 column values it touches. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real is_signed
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
     not_eq_inv
     comparison_limbs_0 comparison_limbs_1
     bit
     b_msb c_msb : F)
  : Prop :=
    -- LtSignedGadget's substantive own constraints
    ((is_real - 1) * is_signed = 0) ∧
    ((is_signed - 1) * b_msb = 0) ∧
    ((is_signed - 1) * c_msb = 0) ∧
    -- The two embedded U16MSBGadget instances (using `is_signed` as
    -- the gating `is_real`)
    U16MSBGadget.AbsConstraints is_signed b_msb ∧
    U16MSBGadget.AbsConstraints is_signed c_msb ∧
    -- The embedded LtWordU16Gadget, invoked with the msb-flipped top
    -- limbs `(a_3 + is_signed*32768 - 65536*b_msb)` and similar for b_3
    LtWordU16Gadget.AbsConstraints
      is_real
      a_0 a_1 a_2 (a_3 + is_signed * 32768 - 65536 * b_msb)
      b_0 b_1 b_2 (b_3 + is_signed * 32768 - 65536 * c_msb)
      u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
      not_eq_inv
      comparison_limbs_0 comparison_limbs_1
      bit

  /-- Bus entries emitted by Pico's `LtSignedGadget`: 2 byte-bus msb
      consistency entries (from each `U16MSBGadget`, gated by
      `+is_signed`) plus 1 byte-bus comparison entry (from
      `LtWordU16Gadget`, gated by `+is_real`). -/
  def AbsBuses
    (is_real is_signed
     a_3 b_3
     comparison_limbs_0 comparison_limbs_1
     bit
     b_msb c_msb : FKB)
  : BusRow :=
    U16MSBGadget.AbsBuses is_signed a_3 b_msb
    ++ U16MSBGadget.AbsBuses is_signed b_3 c_msb
    ++ LtWordU16Gadget.AbsBuses is_real comparison_limbs_0 comparison_limbs_1 bit

end LtSignedGadget
