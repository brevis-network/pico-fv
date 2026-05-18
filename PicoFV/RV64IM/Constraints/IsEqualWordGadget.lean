import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.IsEqualWordGadget
import PicoFV.RV64IM.Airs.IsEqualWordGadget
import PicoFV.RV64IM.Constraints.IsZeroWordGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# IsEqualWordGadget — abstract constraints & buses

`IsEqualWordGadget`'s Pico Rust source is
`vm/src/chips/gadgets/is_equal_word.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. Tests whether two 4-limb
(u16-limb) 64-bit words are equal at the field level. Reduces directly
to `IsZeroWordGadget` applied to the per-limb differences `a_i - b_i`.

## Standalone layout (20 columns total in the extraction)

| Cols   | Role                                              |
|--------|---------------------------------------------------|
| 0..3   | `a_0..a_3` (first operand)                        |
| 4..7   | `b_0..b_3` (second operand)                       |
| 8..15  | 4 × `IsZeroGadget` columns (`inverse_i`, `result_i`) on differences |
| 16     | `is_lower_half_zero`                              |
| 17     | `is_upper_half_zero`                              |
| 18     | `result` (the word-equality indicator)            |
| 19     | `is_real`                                         |

## Algebraic constraints (20)

The first one is `IsEqualWordGadget::eval`'s own `assert_bool(is_real)`;
the remaining 19 are exactly `IsZeroWordGadget.AbsConstraints`
applied to the limb-wise differences. (The embedded
`IsZeroWordGadget::eval` *also* contains an `assert_bool(is_real)`,
so the extraction includes the `is_real` bool check twice — once from
each gadget's own emission.)

Bus interactions: *none*.
-/

namespace IsEqualWordGadget

  open RV64IM_Interactions

  /-- Algebraic facts the Pico `IsEqualWordGadget` asserts on a row.
      The first conjunct is `IsEqualWordGadget::eval`'s own
      `assert_bool(is_real)` (un-gated); the rest is the inner
      `IsZeroWordGadget.AbsConstraints` invoked on the per-limb
      differences `a_i - b_i`. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     inverse_0 inverse_1 inverse_2 inverse_3
     result_0 result_1 result_2 result_3
     is_lower_half_zero is_upper_half_zero
     result : F)
  : Prop :=
    -- IsEqualWordGadget's own `assert_bool(is_real)`
    (is_real * (is_real - 1) = 0) ∧
    -- IsZeroWordGadget on the limb differences
    IsZeroWordGadget.AbsConstraints is_real
      (a_0 - b_0) (a_1 - b_1) (a_2 - b_2) (a_3 - b_3)
      inverse_0 inverse_1 inverse_2 inverse_3
      result_0 result_1 result_2 result_3
      is_lower_half_zero is_upper_half_zero result

  /-- The Pico `IsEqualWordGadget` contributes no bus entries. -/
  def AbsBuses
    (_is_real
     _a_0 _a_1 _a_2 _a_3
     _b_0 _b_1 _b_2 _b_3
     _inverse_0 _inverse_1 _inverse_2 _inverse_3
     _result_0 _result_1 _result_2 _result_3
     _is_lower_half_zero _is_upper_half_zero
     _result : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := [],
      State := [],
      Memory := []
    }

end IsEqualWordGadget
