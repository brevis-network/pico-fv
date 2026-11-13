import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.LtWordU16Gadget
import PicoFV.RV64IM.Airs.LtWordU16Gadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# LtWordU16Gadget — abstract constraints & buses

`LtWordU16Gadget`'s Pico Rust source is
`vm/src/chips/gadgets/lt_word_u16.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The gadget performs an
*unsigned* 64-bit comparison `a < b` by finding the most-significant
differing u16 limb (MSDL) and emitting a single bit indicating the
direction of inequality.

Layout (in the standalone extraction; 17 columns total):
| Cols   | Role                                                       |
|--------|------------------------------------------------------------|
| 0..3   | `a_0..a_3` (input operand a, supplied by parent)           |
| 4..7   | `b_0..b_3` (input operand b, supplied by parent)           |
| 8..11  | `u16_flags_0..3` (one-hot indicator of the MSDL)           |
| 12     | `not_eq_inv` (inverse witness that the MSDL truly differs) |
| 13     | `comparison_limbs_0` = Σ a_i · u16_flags_i (limb of a at MSDL) |
| 14     | `comparison_limbs_1` = Σ b_i · u16_flags_i (limb of b at MSDL) |
| 15     | `bit` (the LT result)                                      |
| 16     | `is_real` (parent's activation flag)                       |

The 15 algebraic constraints (in extraction order) are:
- c0: `is_real ∈ {0, 1}`
- c1..4: `u16_flags_i ∈ {0, 1}` (4 constraints)
- c5: `(Σ u16_flags) ∈ {0, 1}` — one-hot
- c6..9: for each limb i, `(is_real - Σ_{j ≥ i} u16_flags_j) * (a_i - b_i) = 0`
  — if no flag is set in positions ≥ i (i.e., MSDL is below i), then `a_i = b_i`
- c10: `comparison_limbs_0 = Σ a_i · u16_flags_i`
- c11: `comparison_limbs_1 = Σ b_i · u16_flags_i`
- c12: `(-Σ u16_flags) * (not_eq_inv · (comp_0 - comp_1) - is_real) = 0`
  — when any flag is set, `not_eq_inv` is the multiplicative inverse of
    `comp_0 - comp_1`, witnessing that the MSDL truly is a differing limb
- c13: `is_real ∈ {0, 1}` (duplicate of c0)
- c14: `bit ∈ {0, 1}`

The 1 ByteBus entry is `U16Range` on `(comp_0 - comp_1) + bit * 65536`,
gated by `+is_real`. The standard Δ + bit·2¹⁶ trick: combined with the
constraints above, it forces `bit = 1 ⟺ comp_0 < comp_1`.

The gadget has no standalone wrapping Air — used only by `LtSignedGadget`
inside `LtChip`. This file therefore provides only the *parametric*
`AbsConstraints` and `AbsBuses` predicates.
-/

namespace LtWordU16Gadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `LtWordU16Gadget`
      asserts on a row, expressed parametrically in the 13 column
      values it touches (4 a-limbs + 4 b-limbs + 4 flags + not_eq_inv +
      2 comparison_limbs + bit + is_real). -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     u16_flags_0 u16_flags_1 u16_flags_2 u16_flags_3
     not_eq_inv
     comparison_limbs_0 comparison_limbs_1
     bit : F)
  : Prop :=
    (is_real * (is_real - 1) = 0) ∧
    (u16_flags_0 * (u16_flags_0 - 1) = 0) ∧
    (u16_flags_1 * (u16_flags_1 - 1) = 0) ∧
    (u16_flags_2 * (u16_flags_2 - 1) = 0) ∧
    (u16_flags_3 * (u16_flags_3 - 1) = 0) ∧
    ((((u16_flags_0 + u16_flags_1) + u16_flags_2) + u16_flags_3) *
       ((((u16_flags_0 + u16_flags_1) + u16_flags_2) + u16_flags_3) - 1) = 0) ∧
    ((is_real - (0 + u16_flags_3)) * (a_3 - b_3) = 0) ∧
    ((is_real - ((0 + u16_flags_3) + u16_flags_2)) * (a_2 - b_2) = 0) ∧
    ((is_real - (((0 + u16_flags_3) + u16_flags_2) + u16_flags_1)) * (a_1 - b_1) = 0) ∧
    ((is_real - ((((0 + u16_flags_3) + u16_flags_2) + u16_flags_1) + u16_flags_0)) * (a_0 - b_0) = 0) ∧
    ((((0 + a_3 * u16_flags_3) + a_2 * u16_flags_2) + a_1 * u16_flags_1) + a_0 * u16_flags_0
       - comparison_limbs_0 = 0) ∧
    ((((0 + b_3 * u16_flags_3) + b_2 * u16_flags_2) + b_1 * u16_flags_1) + b_0 * u16_flags_0
       - comparison_limbs_1 = 0) ∧
    ((1 - (((u16_flags_0 + u16_flags_1) + u16_flags_2) + u16_flags_3) - 1) *
       (not_eq_inv * (comparison_limbs_0 - comparison_limbs_1) - is_real) = 0) ∧
    (is_real * (is_real - 1) = 0) ∧
    (bit * (bit - 1) = 0)

  /-- The single bus entry the Pico `LtWordU16Gadget` contributes per
      row: a `ByteBus` U16Range on `(comp_0 - comp_1) + bit * 65536`,
      gated by `+is_real`. -/
  def AbsBuses
    (is_real comparison_limbs_0 comparison_limbs_1 bit : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real),
          #v[8, (comparison_limbs_0 - comparison_limbs_1) + bit * 65536, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

end LtWordU16Gadget
