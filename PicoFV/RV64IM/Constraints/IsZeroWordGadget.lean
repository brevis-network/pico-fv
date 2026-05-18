import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.IsZeroWordGadget
import PicoFV.RV64IM.Airs.IsZeroWordGadget
import PicoFV.RV64IM.Constraints.IsZeroGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# IsZeroWordGadget — abstract constraints & buses

`IsZeroWordGadget`'s Pico Rust source is
`vm/src/chips/gadgets/is_zero_word.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. Tests whether a 4-limb
(u16-limb) 64-bit word equals `0` at the field level — *no* range
checks are done on the input.

Composition: four independent `IsZeroGadget` instances on the
individual u16 limbs (giving per-limb `result_i`), then a 2-level
multiplicative AND tree to combine them into a single `result`:

```
is_lower_half_zero = result_0 · result_1   (bottom 32 bits all zero)
is_upper_half_zero = result_2 · result_3   (top 32 bits all zero)
result             = is_lower_half_zero · is_upper_half_zero
```

The product structure plus the booleanity of every intermediate (each
explicitly `assert_bool`-ed under `is_real`) makes `result = 1` iff
every `result_i = 1`, iff every `input_i = 0`.

## Standalone layout (16 columns total in the extraction)

| Cols  | Role                                              |
|-------|---------------------------------------------------|
| 0..3  | `input_0..input_3` (u16 limbs, supplied)          |
| 4..11 | 4 × `IsZeroGadget` columns (`inverse_i`, `result_i`) |
| 12    | `is_lower_half_zero`                              |
| 13    | `is_upper_half_zero`                              |
| 14    | `result` (the word-zero indicator)                |
| 15    | `is_real` (selector)                              |

## Algebraic constraints (19)

- 4 × 3 = 12 from the embedded `IsZeroGadget`s (each gated by `is_real`).
- c12: `is_real · (is_real - 1) = 0` — `is_real ∈ {0, 1}` (own
  `assert_bool(is_real)` in `IsZeroWordGadget::eval`; the embedded
  `IsZeroGadget::eval`s do *not* assert this themselves).
- c13–c15: `is_real · (X · (X - 1)) = 0` for `X ∈ {is_lower_half_zero,
  is_upper_half_zero, result}` — booleanity of each AND-tree node.
- c16: `is_real · (is_lower_half_zero - result_0 · result_1) = 0`.
- c17: `is_real · (is_upper_half_zero - result_2 · result_3) = 0`.
- c18: `is_real · (result - is_lower_half_zero · is_upper_half_zero) = 0`.

Bus interactions: *none* (matches the empty bus row in the extraction).

This file therefore provides only the *parametric* `AbsConstraints`
and (empty) `AbsBuses` predicates.
-/

namespace IsZeroWordGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `IsZeroWordGadget`
      asserts on a row, expressed parametrically in the 11 owned column
      values plus the parent-supplied 4 input limbs and `is_real`. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     input_0 input_1 input_2 input_3
     inverse_0 inverse_1 inverse_2 inverse_3
     result_0 result_1 result_2 result_3
     is_lower_half_zero is_upper_half_zero
     result : F)
  : Prop :=
    -- 4 × IsZeroGadget on the four input limbs
    IsZeroGadget.AbsConstraints is_real input_0 inverse_0 result_0 ∧
    IsZeroGadget.AbsConstraints is_real input_1 inverse_1 result_1 ∧
    IsZeroGadget.AbsConstraints is_real input_2 inverse_2 result_2 ∧
    IsZeroGadget.AbsConstraints is_real input_3 inverse_3 result_3 ∧
    -- Own `assert_bool(is_real)` (un-gated)
    (is_real * (is_real - 1) = 0) ∧
    -- Booleanity of the AND-tree nodes (gated by is_real)
    (is_real * (is_lower_half_zero * (is_lower_half_zero - 1)) = 0) ∧
    (is_real * (is_upper_half_zero * (is_upper_half_zero - 1)) = 0) ∧
    (is_real * (result * (result - 1)) = 0) ∧
    -- AND-tree definitions
    (is_real * (is_lower_half_zero - result_0 * result_1) = 0) ∧
    (is_real * (is_upper_half_zero - result_2 * result_3) = 0) ∧
    (is_real * (result - is_lower_half_zero * is_upper_half_zero) = 0)

  /-- The Pico `IsZeroWordGadget` contributes no bus entries. -/
  def AbsBuses
    (_is_real
     _input_0 _input_1 _input_2 _input_3
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

end IsZeroWordGadget
