import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.AddwGadget
import PicoFV.RV64IM.Airs.AddwGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddwGadget — abstract constraints & buses

`AddwGadget`'s Pico Rust source is `vm/src/chips/gadgets/addw.rs` at
commit `22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The gadget computes
the low 32 bits of `b + c` as two u16 limbs `value_0`, `value_1`, and
captures the MSB of `value_1` in a separate boolean column `msb`. The
high two limbs of the full 64-bit ADDW result are reconstructed by the
parent chip via sign-extension `msb * 65535` (so `0x0000` or `0xFFFF`).

The 5 algebraic constraints emitted by the gadget are:

- `is_real ∈ {0, 1}`                                                   (twice — once
  from `AddwGadget::eval` and once from the embedded `U16MSBGadget::eval`)
- 2 × per-limb carry-boolean checks of the form
  `is_real * carry_i * (carry_i - 1) = 0`, where the limb-`i` carry is
  reconstructed as
  `carry_i = ((b_i + c_i - value_i) + carry_{i-1}) * inv(2^16)`
  with `inv(2^16) ≡ 2130673921 (mod KB_prime)` and `carry_{-1} = 0`.
- `msb ∈ {0, 1}`

The 3 ByteBus entries are:
- U16Range on `value_0`
- U16Range on `value_1`
- U16Range on `2 * value_1 - msb * 65536` — pins `msb` to the actual
  bit-15 of `value_1` (the resulting expression is a valid u16 iff
  `msb` matches `value_1`'s top bit).

Unlike `AddGadget`, `AddwGadget` has no standalone wrapping Air, so this
file only provides the *parametric* `AbsConstraints` and `AbsBuses`
predicates — consumed by the single chip that embeds the gadget
(`AddwChip`).
-/

namespace AddwGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `AddwGadget` asserts
      on a row, expressed parametrically in the 8 column values that
      flow through the gadget. Only the low 32 bits of `b` and `c` are
      consumed (limbs 0..1). -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     b_0 b_1
     c_0 c_1
     value_0 value_1
     msb : F)
  : Prop :=
    let carry_0 := ((b_0 + c_0 - value_0) + 0) * 2130673921
    let carry_1 := ((b_1 + c_1 - value_1) + carry_0) * 2130673921
    (is_real * (is_real - 1) = 0) ∧
    (is_real * (carry_0 * (carry_0 - 1)) = 0) ∧
    (is_real * (carry_1 * (carry_1 - 1)) = 0) ∧
    (is_real * (is_real - 1) = 0) ∧
    (msb * (msb - 1) = 0)

  /-- The bus entries the Pico `AddwGadget` contributes per row.
      3 byte-bus entries gated by `-is_real`:
      - U16Range on `value_0`,
      - U16Range on `value_1`,
      - U16Range on `2 * value_1 - msb * 65536` (pins `msb` to the actual
        high bit of `value_1`). -/
  def AbsBuses
    (is_real value_0 value_1 msb : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        (-(is_real), #v[8, value_0, 0, 0, 0]),
        (-(is_real), #v[8, value_1, 0, 0, 0]),
        (-(is_real), #v[8, 2 * value_1 - msb * 65536, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

end AddwGadget
