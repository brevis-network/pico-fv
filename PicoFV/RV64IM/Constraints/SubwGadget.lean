import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.SubwGadget
import PicoFV.RV64IM.Airs.SubwGadget
import PicoFV.RV64IM.Constraints.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SubwGadget — abstract constraints & buses

`SubwGadget`'s Pico Rust source is `vm/src/chips/gadgets/subw.rs` at
commit `22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The gadget computes
the low 32 bits of `b - c` as two u16 limbs `value_0`, `value_1`, and
captures the MSB of `value_1` in a separate boolean column `msb`. The
high two limbs of the full 64-bit SUBW result are reconstructed by the
parent chip via sign-extension `msb * 65535` (so `0x0000` or `0xFFFF`).

The 5 algebraic constraints emitted by the gadget are:

- `is_real ∈ {0, 1}`                                                   (twice — once
  from `SubwGadget::eval` and once from the embedded `U16MSBGadget::eval`)
- 2 × per-limb borrow-boolean checks of the form
  `is_real * borrow_i * (borrow_i - 1) = 0`, where the limb-`i` borrow is
  reconstructed as
  `borrow_i = ((b_i + 65535 - c_i - value_i) + prev_borrow) * inv(2^16)`
  with `inv(2^16) ≡ 2130673921 (mod KB_prime)` and `prev_borrow_{-1} = 1`
  (the initial "carry-in" of `b + (¬c) + 1`).
- `msb ∈ {0, 1}`

The 3 ByteBus entries are:
- U16Range on `value_0`
- U16Range on `value_1`
- U16Range on `2 * value_1 - msb * 65536` — pins `msb` to the actual
  bit-15 of `value_1`.

Unlike `AddGadget`, `SubwGadget` has no standalone wrapping Air, so this
file only provides the *parametric* `AbsConstraints` and `AbsBuses`
predicates — consumed by the single chip that embeds the gadget
(`SubwChip`).
-/

namespace SubwGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `SubwGadget` asserts
      on a row, expressed parametrically in the 8 column values that
      flow through the gadget. Only the low 32 bits of `b` and `c` are
      consumed (limbs 0..1). The msb-related part is factored into
      `U16MSBGadget.AbsConstraints` (the embedded MSB sub-gadget). -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     b_0 b_1
     c_0 c_1
     value_0 value_1
     msb : F)
  : Prop :=
    let borrow_0 := ((b_0 + 65536 - 1 - c_0 - value_0) + 1) * 2130673921
    let borrow_1 := ((b_1 + 65536 - 1 - c_1 - value_1) + borrow_0) * 2130673921
    (is_real * (is_real - 1) = 0) ∧
    (is_real * (borrow_0 * (borrow_0 - 1)) = 0) ∧
    (is_real * (borrow_1 * (borrow_1 - 1)) = 0) ∧
    U16MSBGadget.AbsConstraints is_real msb

  /-- The bus entries the Pico `SubwGadget` contributes per row. The
      gadget itself emits 2 byte-bus `U16Range`s (on `value_0` and
      `value_1`); the third entry — `U16Range` on `2*value_1 -
      msb*65536`, pinning `msb` to bit-15 of `value_1` — is
      contributed by the embedded `U16MSBGadget`. -/
  def AbsBuses
    (is_real value_0 value_1 msb : FKB)
  : BusRow :=
    ({
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        (-(is_real), #v[8, value_0, 0, 0, 0]),
        (-(is_real), #v[8, value_1, 0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)
    ++ U16MSBGadget.AbsBuses is_real value_1 msb

end SubwGadget
