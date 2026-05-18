import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.U16ToU8GadgetSafe
import PicoFV.RV64IM.Airs.U16ToU8GadgetSafe

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# U16ToU8GadgetSafe — abstract constraints & buses

`U16ToU8Gadget::eval_u16_to_u8_safe`'s Pico Rust source is
`vm/src/chips/gadgets/u16_to_u8.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The "safe" variant of the
u16 → u8 byte-split gadget: takes a 4-limb u16 word `a` and an
already-allocated `low_bytes` 4-column witness, and emits 4 byte-bus
range checks tying `low_bytes_i` and the implied high byte
`(a_i - low_bytes_i) · 256⁻¹` to the byte table.

The gadget owns 4 columns (`low_bytes_0..low_bytes_3`) shared with the
`Unsafe` variant; the difference is purely in the bus contribution.

## Algebraic constraints

*None.* The gadget produces 0 algebraic constraints.

## Bus interactions (4 entries, all `ByteBus`)

For each `i ∈ [0, 3]`:
```
(-is_real, U8Pair{a = low_bytes_i, b = (a_i - low_bytes_i) · 2122383361})
```
where `2122383361 = 256⁻¹ mod FKB`. The `U8Pair` opcode `(4, 7)`
range-checks both bytes simultaneously, so 4 bus entries cover all
8 bytes of the u64. With both bytes in `[0, 255]` and the field
identity `low + 256 · high = a_i`, this pins `(low_bytes_i,
high_byte_i)` to the canonical u8 decomposition of `a_i` (provided
`a_i.val < 65536`, which the parent must supply).

This file therefore provides only the parametric (empty)
`AbsConstraints` and the 4-entry `AbsBuses`.
-/

namespace U16ToU8GadgetSafe

  open RV64IM_Interactions

  /-- `U16ToU8GadgetSafe` contributes no algebraic constraints. -/
  def AbsConstraints
    {F : Type} [Field F]
    (_is_real
     _a_0 _a_1 _a_2 _a_3
     _low_bytes_0 _low_bytes_1 _low_bytes_2 _low_bytes_3 : F)
  : Prop :=
    True

  /-- The 4 byte-bus entries the Pico safe variant emits per row, one
      per limb. Each is a `U8Pair` (byte-bus opcode 7) range check on
      `(low_bytes_i, (a_i - low_bytes_i) · 256⁻¹)`, gated by
      `-is_real`. -/
  def AbsBuses
    (is_real
     a_0 a_1 a_2 a_3
     low_bytes_0 low_bytes_1 low_bytes_2 low_bytes_3 : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        (-(is_real), #v[7, 0, 0, low_bytes_0, (a_0 - low_bytes_0) * 2122383361]),
        (-(is_real), #v[7, 0, 0, low_bytes_1, (a_1 - low_bytes_1) * 2122383361]),
        (-(is_real), #v[7, 0, 0, low_bytes_2, (a_2 - low_bytes_2) * 2122383361]),
        (-(is_real), #v[7, 0, 0, low_bytes_3, (a_3 - low_bytes_3) * 2122383361])
      ],
      State := [],
      Memory := []
    }

end U16ToU8GadgetSafe
