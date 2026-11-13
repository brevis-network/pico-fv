import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.MulChip
import PicoFV.RV64IM.Airs.MulChip
import PicoFV.RV64IM.Constraints.MulGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MulChip — abstract constraints & buses

`MulChip`'s Pico Rust source is
`vm/src/chips/chips/alu/mul/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The chip wraps
`MulGadget` and adds:

- 5 selector-bool checks on `is_mul`, `is_mulh`, `is_mulhu`,
  `is_mulhsu`, `is_mulw` (one each — the gadget already asserts these
  internally, so this is a duplicate set);
- an at-most-one check on the sum-of-selectors `is_real`
  (`is_real · (is_real − 1) = 0` after substituting
  `is_real = sum_of_selectors`);
- the chip-level `looked_alu` ALU bus entry with the selector-encoded
  opcode `is_mul · 30 + is_mulh · 31 + is_mulhu · 32 + is_mulhsu · 33
  + is_mulw · 48`.

## Chip layout (62 columns, matching `MulValueCols`)

| Cols    | Field path (under `air.cols.values`)           |
|---------|------------------------------------------------|
| 0..3    | `a_0..a_3` (output Word)                       |
| 4..7    | `b_0..b_3` (input 1)                           |
| 8..11   | `c_0..c_3` (input 2)                           |
| 12..27  | `mul_gadget.carry_0..15`                       |
| 28..43  | `mul_gadget.product_0..15`                     |
| 44..47  | `mul_gadget.b_lower_byte.low_bytes_0..3`       |
| 48..51  | `mul_gadget.c_lower_byte.low_bytes_0..3`       |
| 52      | `mul_gadget.b_msb`                             |
| 53      | `mul_gadget.c_msb`                             |
| 54      | `mul_gadget.product_msb.msb`                   |
| 55      | `mul_gadget.b_sign_extend`                     |
| 56      | `mul_gadget.c_sign_extend`                     |
| 57..61  | `is_mul`, `is_mulh`, `is_mulhu`, `is_mulhsu`, `is_mulw` |

## Algebraic constraints (51 total)

- **c0..c44**: `MulGadget`'s 45 constraints, with the chip's
  `is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw`
  substituted in for the gadget's `is_real` parameter, and the
  chip's column accessors substituted for the gadget's column
  parameters.
- **c45..c49**: 5 chip-own `assert_bool` checks on each selector
  (duplicates of the gadget's selector bools).
- **c50**: chip-own at-most-one check
  `(is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw) · ((sum) − 1) = 0`.

## Bus interactions (36 total)

- 35 `ByteBus` entries from `MulGadget.AbsBuses`.
- 1 chip-own `ALUBus` entry with `is_real` multiplicity and the
  selector-encoded opcode.
-/

namespace MulChip

  open RV64IM_Interactions

  /-- The chip's per-row `BusRow`, factored as
      `MulGadget.AbsBuses ++ <chip ALU entry>`. -/
  def AbsBuses
    (is_mul is_mulh is_mulhu is_mulhsu is_mulw
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
     b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
     c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
     b_msb c_msb product_msb
     _b_sign_extend _c_sign_extend : FKB)
  : BusRow :=
    let is_real := is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw
    MulGadget.AbsBuses is_real is_mulw a_1
      b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
      carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
      carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
      product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
      product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
      b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
      c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
      b_msb c_msb product_msb
    ++
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(is_real),
          #v[ is_mul * 30 + is_mulh * 31 + is_mulhu * 32 + is_mulhsu * 33 + is_mulw * 48,
              a_0, a_1, a_2, a_3,
              b_0, b_1, b_2, b_3,
              c_0, c_1, c_2, c_3 ])
      ],
      Byte := [],
      State := [],
      Memory := []
    } : BusRow)

end MulChip

namespace MulChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    /-- Chip-level algebraic facts, factored through
        `MulGadget.AbsConstraints` (with `is_real = sum_of_selectors`
        substituted in) plus the 5 chip-own selector bools and the
        at-most-one constraint. -/
    @[constraint_and_interaction_simplification]
    def AbsConstraints
      (air : Valid_MulChip F ExtF) (row : ℕ)
    : Prop :=
      let is_mul    := air.cols.values.is_mul    row 0
      let is_mulh   := air.cols.values.is_mulh   row 0
      let is_mulhu  := air.cols.values.is_mulhu  row 0
      let is_mulhsu := air.cols.values.is_mulhsu row 0
      let is_mulw   := air.cols.values.is_mulw   row 0
      let is_real   := is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw
      MulGadget.AbsConstraints
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
        (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
        (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
        (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
        (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
        (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
        (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
        (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
        (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
        (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
        (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
        (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
        (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
        (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
        (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
        (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
        (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
        (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
        (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
        (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
        (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
        (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
        (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
        (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
        (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
        (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
        (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
        (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
        (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
        (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
        (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
        (air.cols.values.mul_gadget.b_msb row 0)
        (air.cols.values.mul_gadget.c_msb row 0)
        (air.cols.values.mul_gadget.product_msb.msb row 0)
        (air.cols.values.mul_gadget.b_sign_extend row 0)
        (air.cols.values.mul_gadget.c_sign_extend row 0)
      ∧ (is_mul * (is_mul - 1) = 0)
      ∧ (is_mulh * (is_mulh - 1) = 0)
      ∧ (is_mulhu * (is_mulhu - 1) = 0)
      ∧ (is_mulhsu * (is_mulhsu - 1) = 0)
      ∧ (is_mulw * (is_mulw - 1) = 0)
      ∧ (is_real * (is_real - 1) = 0)

    section row_buses

      /-- Raw byte+ALU bus entries emitted by the chip per row,
          parametrised by the air accessors. -/
      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_MulChip FKB ExtF) (row : ℕ)
      : List (FKB × List FKB) :=
        let is_mul    := air.cols.values.is_mul    row 0
        let is_mulh   := air.cols.values.is_mulh   row 0
        let is_mulhu  := air.cols.values.is_mulhu  row 0
        let is_mulhsu := air.cols.values.is_mulhsu row 0
        let is_mulw   := air.cols.values.is_mulw   row 0
        let is_real   := is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw
        let b_low_0   := air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0
        let b_low_1   := air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0
        let b_low_2   := air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0
        let b_low_3   := air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0
        let c_low_0   := air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0
        let c_low_1   := air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0
        let c_low_2   := air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0
        let c_low_3   := air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0
        let b_msb     := air.cols.values.mul_gadget.b_msb row 0
        let c_msb     := air.cols.values.mul_gadget.c_msb row 0
        let prd_msb   := air.cols.values.mul_gadget.product_msb.msb row 0
        let a_1       := air.cols.values.a_1 row 0
        let b_0       := air.cols.values.b_0 row 0
        let b_1       := air.cols.values.b_1 row 0
        let b_2       := air.cols.values.b_2 row 0
        let b_3       := air.cols.values.b_3 row 0
        let c_0       := air.cols.values.c_0 row 0
        let c_1       := air.cols.values.c_1 row 0
        let c_2       := air.cols.values.c_2 row 0
        let c_3       := air.cols.values.c_3 row 0
        [ -- U16ToU8Safe on b (4 entries)
          ((is_real), [5, 7, 0, 0, b_low_0, (b_0 - b_low_0) * 2122383361]),
          ((is_real), [5, 7, 0, 0, b_low_1, (b_1 - b_low_1) * 2122383361]),
          ((is_real), [5, 7, 0, 0, b_low_2, (b_2 - b_low_2) * 2122383361]),
          ((is_real), [5, 7, 0, 0, b_low_3, (b_3 - b_low_3) * 2122383361]),
          -- U16ToU8Safe on c (4 entries)
          ((is_real), [5, 7, 0, 0, c_low_0, (c_0 - c_low_0) * 2122383361]),
          ((is_real), [5, 7, 0, 0, c_low_1, (c_1 - c_low_1) * 2122383361]),
          ((is_real), [5, 7, 0, 0, c_low_2, (c_2 - c_low_2) * 2122383361]),
          ((is_real), [5, 7, 0, 0, c_low_3, (c_3 - c_low_3) * 2122383361]),
          -- MSB byte lookups
          ((is_real), [5, 6, b_msb, 0, (b_3 - b_low_3) * 2122383361, 0]),
          ((is_real), [5, 6, c_msb, 0, (c_3 - c_low_3) * 2122383361, 0]),
          -- U16MSB on a_1 (product top word's MSB), gated by +is_mulw
          ((is_mulw), [5, 8, 2 * a_1 - prd_msb * 65536, 0, 0, 0]),
          -- 16 × U16Range on carry
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_0 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_1 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_2 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_3 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_4 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_5 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_6 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_7 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_8 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_9 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_10 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_11 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_12 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_13 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_14 row 0, 0, 0, 0]),
          ((is_real), [5, 8, air.cols.values.mul_gadget.carry_15 row 0, 0, 0, 0]),
          -- 8 × U8Pair on product[2i], product[2i+1]
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_0 row 0,
            air.cols.values.mul_gadget.product_1 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_2 row 0,
            air.cols.values.mul_gadget.product_3 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_4 row 0,
            air.cols.values.mul_gadget.product_5 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_6 row 0,
            air.cols.values.mul_gadget.product_7 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_8 row 0,
            air.cols.values.mul_gadget.product_9 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_10 row 0,
            air.cols.values.mul_gadget.product_11 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_12 row 0,
            air.cols.values.mul_gadget.product_13 row 0]),
          ((is_real), [5, 7, 0, 0,
            air.cols.values.mul_gadget.product_14 row 0,
            air.cols.values.mul_gadget.product_15 row 0]),
          -- Chip-own ALU bus entry
          (-(is_real), [4,
            is_mul * 30 + is_mulh * 31 + is_mulhu * 32 + is_mulhsu * 33 + is_mulw * 48,
            air.cols.values.a_0 row 0,
            air.cols.values.a_1 row 0,
            air.cols.values.a_2 row 0,
            air.cols.values.a_3 row 0,
            b_0, b_1, b_2, b_3,
            c_0, c_1, c_2, c_3])
        ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_MulChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_MulChip FKB ExtF) (row : ℕ)
    : Prop :=
      constrain_interactions air ∧ AbsConstraints air row

    set_option maxRecDepth 4_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_MulChip FKB ExtF) (row : ℕ)
    :
      MulChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      unfold Extraction.allHold allHold_simplified
      simp [
        pico_encapsulation,
        extracted_constraint_definition,
        constraint_and_interaction_simplification,
        MulGadget.AbsConstraints,
        and_assoc
      ]

  end constraint_simplification

end MulChip.ConstraintsAndBuses

namespace MulChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `MulChip` row. Defined directly as
      `MulChip.AbsBuses` applied to the chip's accessors. -/
  def bus_row (air : Valid_MulChip FKB ExtF) (row : ℕ) : BusRow :=
    MulChip.AbsBuses
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulhu row 0) (air.cols.values.is_mulhsu row 0)
      (air.cols.values.is_mulw row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)

  set_option maxRecDepth 4_000_000 in
  @[simp]
  lemma bus_row_equiv (air : Valid_MulChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (MulChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    dsimp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      MulChip.AbsBuses,
      MulGadget.AbsBuses,
      U16ToU8GadgetSafe.AbsBuses,
      pico_encapsulation,
    ]

end MulChip.Interactions

namespace MulChip.Interpretations

  open RV64IM_Interactions
  open MulChip.ConstraintsAndBuses
  open MulChip.Interactions

  /-- The chip's `Extraction.allHold` extracts (modulo the bus piece)
      exactly the chip's `AbsConstraints`. -/
  lemma allHold_abs
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_constraints : MulChip.Extraction.allHold air row)
  :
    AbsConstraints air row
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    exact h_constraints.2

  /-- All five selectors are boolean, and at most one is `1`. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_constraints : MulChip.Extraction.allHold air row)
  :
    (air.cols.values.is_mul row 0 = 0 ∨ air.cols.values.is_mul row 0 = 1) ∧
    (air.cols.values.is_mulh row 0 = 0 ∨ air.cols.values.is_mulh row 0 = 1) ∧
    (air.cols.values.is_mulhu row 0 = 0 ∨ air.cols.values.is_mulhu row 0 = 1) ∧
    (air.cols.values.is_mulhsu row 0 = 0 ∨ air.cols.values.is_mulhsu row 0 = 1) ∧
    (air.cols.values.is_mulw row 0 = 0 ∨ air.cols.values.is_mulw row 0 = 1) ∧
    ((air.cols.values.is_mul row 0 +
      air.cols.values.is_mulh row 0 +
      air.cols.values.is_mulhu row 0 +
      air.cols.values.is_mulhsu row 0 +
      air.cols.values.is_mulw row 0 = 0) ∨
     (air.cols.values.is_mul row 0 +
      air.cols.values.is_mulh row 0 +
      air.cols.values.is_mulhu row 0 +
      air.cols.values.is_mulhsu row 0 +
      air.cols.values.is_mulw row 0 = 1))
  := by
    have h := allHold_abs air row h_constraints
    simp only [AbsConstraints] at h
    obtain ⟨_, h_mul, h_mulh, h_mulhu, h_mulhsu, h_mulw, h_sum⟩ := h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    . exact (mul_eq_zero.mp h_mul).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp h_mulh).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp h_mulhu).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp h_mulhsu).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp h_mulw).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp h_sum).imp id sub_eq_zero.mp

  /-- At most one selector is active: if any of `is_mul` / `is_mulh` /
      `is_mulhu` / `is_mulhsu` / `is_mulw` is `1`, the other four are
      `0`. Follows from `selector_breakdown`: each is binary and their
      sum is at most `1`, so the active selector forces the others to
      zero. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_constraints : MulChip.Extraction.allHold air row)
  :
    (air.cols.values.is_mul row 0 = 1 →
      air.cols.values.is_mulh   row 0 = 0 ∧
      air.cols.values.is_mulhu  row 0 = 0 ∧
      air.cols.values.is_mulhsu row 0 = 0 ∧
      air.cols.values.is_mulw   row 0 = 0) ∧
    (air.cols.values.is_mulh row 0 = 1 →
      air.cols.values.is_mul    row 0 = 0 ∧
      air.cols.values.is_mulhu  row 0 = 0 ∧
      air.cols.values.is_mulhsu row 0 = 0 ∧
      air.cols.values.is_mulw   row 0 = 0) ∧
    (air.cols.values.is_mulhu row 0 = 1 →
      air.cols.values.is_mul    row 0 = 0 ∧
      air.cols.values.is_mulh   row 0 = 0 ∧
      air.cols.values.is_mulhsu row 0 = 0 ∧
      air.cols.values.is_mulw   row 0 = 0) ∧
    (air.cols.values.is_mulhsu row 0 = 1 →
      air.cols.values.is_mul    row 0 = 0 ∧
      air.cols.values.is_mulh   row 0 = 0 ∧
      air.cols.values.is_mulhu  row 0 = 0 ∧
      air.cols.values.is_mulw   row 0 = 0) ∧
    (air.cols.values.is_mulw row 0 = 1 →
      air.cols.values.is_mul    row 0 = 0 ∧
      air.cols.values.is_mulh   row 0 = 0 ∧
      air.cols.values.is_mulhu  row 0 = 0 ∧
      air.cols.values.is_mulhsu row 0 = 0)
  := by
    have h_selectors := selector_breakdown air row h_constraints
    clear *- h_selectors
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

  /-- The chip's per-row `BusRow` is exactly `MulChip.AbsBuses`
      instantiated at the chip's accessors. -/
  lemma bus_row_abs
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
  :
    MulChip.Interactions.bus_row air row =
    MulChip.AbsBuses
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulhu row 0) (air.cols.values.is_mulhsu row 0)
      (air.cols.values.is_mulw row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)
  := by rfl

end MulChip.Interpretations
