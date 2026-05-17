import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.U16MSBGadget
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# U16MSBGadget — abstract constraints & buses

`U16MSBGadget`'s Pico Rust source is `vm/src/chips/gadgets/msb.rs` at
commit `22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. A single-column
gadget that captures the most significant bit of a u16 value supplied
by the parent context.

The gadget touches 3 column values per row: the externally-supplied
`value` (the u16 being tested), the gadget's own `msb` column, and
the externally-supplied `is_real` gating selector.

Algebraic constraints (2):
- `is_real * (is_real - 1) = 0`     — `is_real ∈ {0, 1}`
- `msb * (msb - 1) = 0`             — `msb ∈ {0, 1}`

Bus interactions (1):
- ByteBus `U16Range` on `2 * value - msb * 65536`, gated by `-is_real`.
  Combined with `value < 65536` (which the parent must supply), this
  forces `msb` to be exactly bit-15 of `value`.

`U16MSBGadget` is the most reused gadget in RV64IM — 12 instantiations
across 7 hosts (AddwGadget, SubwGadget, LtSignedGadget × 2, MulGadget,
DivRemChip × 4, SLLChip, ShiftRightChip × 2). It has no standalone
wrapping Air, so this file only provides the *parametric*
`AbsConstraints` and `AbsBuses` — consumed by every host.
-/

namespace U16MSBGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `U16MSBGadget`
      asserts on a row, expressed parametrically in the 2 column
      values it owns plus the parent's `is_real` and `value`. The
      `value` is not constrained here (it's just used in the bus
      entry) — that's why it doesn't appear in this predicate. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real msb : F)
  : Prop :=
    (is_real * (is_real - 1) = 0) ∧
    (msb * (msb - 1) = 0)

  /-- The single bus entry the Pico `U16MSBGadget` contributes per
      row: a `ByteBus` U16Range on `2 * value - msb * 65536`, gated by
      `-is_real`. -/
  def AbsBuses
    (is_real value msb : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        (-(is_real), #v[8, 2 * value - msb * 65536, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

end U16MSBGadget
