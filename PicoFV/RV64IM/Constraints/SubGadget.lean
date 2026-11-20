import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.SubGadget
import PicoFV.RV64IM.Airs.SubGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SubGadget — abstract constraints & buses

`SubGadget`'s Pico Rust source is `vm/src/chips/gadgets/sub.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. Per-limb subtraction with
borrow is encoded as 4 borrow-boolean checks and 4 u16 range checks on
the result limbs.

Same shape as `AddGadget` but with borrow logic. The borrow expression
for limb `i` is

```
borrow_i = ((b_i + 65535 - c_i - value_i) + prev_borrow) * inv(2^16)
```

with `prev_borrow_{-1} = 1` (the initial "carry-in" needed because Pico
encodes `b - c` as `b + (¬c) + 1` using one's-complement of `c` extended
to 16 bits).

Unlike `AddGadget`, `SubGadget` has no standalone wrapping Air, so this
file only provides the *parametric* `AbsConstraints` and `AbsBuses`
predicates — consumed by chips that embed the gadget (e.g. `SubChip`).
-/

namespace SubGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `SubGadget` asserts on
      a row, expressed parametrically in the 13 column values. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     value_0 value_1 value_2 value_3 : F)
  : Prop :=
    let borrow_0 := ((b_0 + 65536 - 1 - c_0 - value_0) + 1) * 2130673921
    let borrow_1 := ((b_1 + 65536 - 1 - c_1 - value_1) + borrow_0) * 2130673921
    let borrow_2 := ((b_2 + 65536 - 1 - c_2 - value_2) + borrow_1) * 2130673921
    let borrow_3 := ((b_3 + 65536 - 1 - c_3 - value_3) + borrow_2) * 2130673921
    (is_real * (is_real - 1) = 0) ∧
    (is_real * (borrow_0 * (borrow_0 - 1)) = 0) ∧
    (is_real * (borrow_1 * (borrow_1 - 1)) = 0) ∧
    (is_real * (borrow_2 * (borrow_2 - 1)) = 0) ∧
    (is_real * (borrow_3 * (borrow_3 - 1)) = 0)

  /-- The bus entries the Pico `SubGadget` contributes per row. Same
      4-entry U16Range layout as `AddGadget.AbsBuses` (the gadget's only
      bus emissions are u16 range checks on `value_0..3`, gated by
      `-is_real`). -/
  def AbsBuses
    (is_real value_0 value_1 value_2 value_3 : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real), #v[8, value_0, 0, 0, 0]),
        ((is_real), #v[8, value_1, 0, 0, 0]),
        ((is_real), #v[8, value_2, 0, 0, 0]),
        ((is_real), #v[8, value_3, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

end SubGadget
