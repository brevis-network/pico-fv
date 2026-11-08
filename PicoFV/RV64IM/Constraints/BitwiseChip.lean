import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.BitwiseChip
import PicoFV.RV64IM.Airs.BitwiseChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# BitwiseChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and
the list of bus interactions emitted by `BitwiseChip::eval`
(`vm/src/chips/chips/alu/bitwise/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_BitwiseChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.BitwiseChip`.

The chip layout (matching `BitwiseValueCols<F>`) is:
| Cols  | Field path (under `air.cols.values`)                  | Description |
|-------|-------------------------------------------------------|-------------|
| 0..3  | `b_0..3`                                              | first input `b` (u16 limbs) |
| 4..7  | `c_0..3`                                              | second input `c` (u16 limbs) |
| 8..11 | `bitwise.b_low_bytes.low_bytes_0..3`                  | low byte of each limb of `b` |
| 12..15| `bitwise.c_low_bytes.low_bytes_0..3`                  | low byte of each limb of `c` |
| 16..23| `bitwise.bitwise.result_0..7`                         | byte-level result (8 bytes) |
| 24    | `is_xor`                                              | XOR selector |
| 25    | `is_or`                                               | OR selector |
| 26    | `is_and`                                              | AND selector |

The high byte of each limb is not a column; it's computed inline as
`(limb_i - low_byte_i) * inv(256)` (with `inv(256) ≡ 2122383361
(mod KB_prime)`).

The 5 algebraic constraints emitted by the chip are:
- `is_xor + is_or + is_and ∈ {0, 1}`                                (twice: c0 + c4;
  the first is the chip's own `assert_bool(is_real)`, the second is
  `BitWiseU16Gadget::eval`'s `assert_bool(is_real)` on the same sum.)
- `is_xor ∈ {0, 1}`, `is_or ∈ {0, 1}`, `is_and ∈ {0, 1}`            (c1, c2, c3)

The bus interactions are:
- 8 ByteBus entries (opcode `is_xor*2 + is_or*1 + is_and*0`, sub-op
  `result_byte_j`) — one bitwise byte lookup per byte of the 64-bit
  result, gated by `+(is_xor + is_or + is_and)`. The byte operands
  alternate between explicit low bytes and inline high bytes
  `(limb - low_byte) * inv(256)`.
- 1 ALU entry (opcode 4, sub-op `is_xor*2 + is_or*3 + is_and*4` ∈
  {2 (XOR), 3 (OR), 4 (AND)}) — issued only when the sum-selector is
  1; carries the recomposed u16 result limbs `result_{2i} +
  result_{2i+1} * 256` along with `b_0..3` and `c_0..3`.
-/

namespace BitwiseChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_real = is_xor + is_or + is_and is boolean.
      -- Comes from `BitwiseChip::eval`'s own `assert_bool(is_real)`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_BitwiseChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_real row 0) * ((air.cols.values.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_BitwiseChip F ExtF) (row : ℕ)
      : BitwiseChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 1-3: individual selector booleans.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_BitwiseChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_xor row 0) * ((air.cols.values.is_xor row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_BitwiseChip F ExtF) (row : ℕ)
      : BitwiseChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_BitwiseChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_or row 0) * ((air.cols.values.is_or row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_BitwiseChip F ExtF) (row : ℕ)
      : BitwiseChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_BitwiseChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_and row 0) * ((air.cols.values.is_and row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_BitwiseChip F ExtF) (row : ℕ)
      : BitwiseChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 4: is_real boolean (duplicate of constraint 0).
      -- Comes from `BitWiseU16Gadget::eval`'s `assert_bool(is_real)` with
      -- `is_real = is_xor + is_or + is_and`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_BitwiseChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_real row 0) * ((air.cols.values.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_BitwiseChip F ExtF) (row : ℕ)
      : BitwiseChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 5 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_BitwiseChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row
        ]

    end row_constraints

    /-- All 27 column values of a `BitwiseChip` row. -/
    def row (air : Valid_BitwiseChip FKB ExtF) (r : ℕ) : Vector FKB 27 :=
      #v[ air.cols.values.b_0 r 0, air.cols.values.b_1 r 0,
          air.cols.values.b_2 r 0, air.cols.values.b_3 r 0,
          air.cols.values.c_0 r 0, air.cols.values.c_1 r 0,
          air.cols.values.c_2 r 0, air.cols.values.c_3 r 0,
          air.cols.values.bitwise.b_low_bytes.low_bytes_0 r 0,
          air.cols.values.bitwise.b_low_bytes.low_bytes_1 r 0,
          air.cols.values.bitwise.b_low_bytes.low_bytes_2 r 0,
          air.cols.values.bitwise.b_low_bytes.low_bytes_3 r 0,
          air.cols.values.bitwise.c_low_bytes.low_bytes_0 r 0,
          air.cols.values.bitwise.c_low_bytes.low_bytes_1 r 0,
          air.cols.values.bitwise.c_low_bytes.low_bytes_2 r 0,
          air.cols.values.bitwise.c_low_bytes.low_bytes_3 r 0,
          air.cols.values.bitwise.bitwise.result_0 r 0,
          air.cols.values.bitwise.bitwise.result_1 r 0,
          air.cols.values.bitwise.bitwise.result_2 r 0,
          air.cols.values.bitwise.bitwise.result_3 r 0,
          air.cols.values.bitwise.bitwise.result_4 r 0,
          air.cols.values.bitwise.bitwise.result_5 r 0,
          air.cols.values.bitwise.bitwise.result_6 r 0,
          air.cols.values.bitwise.bitwise.result_7 r 0,
          air.cols.values.is_xor r 0,
          air.cols.values.is_or r 0,
          air.cols.values.is_and r 0 ]

    section row_buses

      -- =====================================================================
      -- Bus interactions emitted by `BitwiseChip::eval` (per row):
      -- 8 ByteBus entries (opcode 5 prefix, byte-op = is_xor*2 + is_or):
      --   for each limb i ∈ {0,1,2,3}, two entries:
      --     - low byte: bitwise(b_low_byte_i, c_low_byte_i) = result_{2i}
      --     - high byte: bitwise((b_i - b_low_byte_i)*inv(256),
      --                          (c_i - c_low_byte_i)*inv(256))
      --                  = result_{2i+1}
      --   all gated by `+(is_xor + is_or + is_and)`.
      -- 1 ALU entry (opcode 5 prefix, op = is_xor*2 + is_or*3 + is_and*4):
      --   gated by `-(is_xor + is_or + is_and)`. Carries the recomposed
      --   u16 result limbs `result_{2i} + result_{2i+1}*256` (i=0..3)
      --   and the operand limbs `b_0..3`, `c_0..3`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_BitwiseChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        let op : FKB :=
          (air.cols.values.is_xor row 0) * 2
            + (air.cols.values.is_or row 0) * 1
            + (air.cols.values.is_and row 0) * 0
        let mult : FKB := air.cols.values.is_real row 0
        [
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_0 row 0), 0,
            (air.cols.values.bitwise.b_low_bytes.low_bytes_0 row 0),
            (air.cols.values.bitwise.c_low_bytes.low_bytes_0 row 0)]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_1 row 0), 0,
            ((air.cols.values.b_0 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_0 row 0)) * 2122383361,
            ((air.cols.values.c_0 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_0 row 0)) * 2122383361]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_2 row 0), 0,
            (air.cols.values.bitwise.b_low_bytes.low_bytes_1 row 0),
            (air.cols.values.bitwise.c_low_bytes.low_bytes_1 row 0)]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_3 row 0), 0,
            ((air.cols.values.b_1 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_1 row 0)) * 2122383361,
            ((air.cols.values.c_1 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_1 row 0)) * 2122383361]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_4 row 0), 0,
            (air.cols.values.bitwise.b_low_bytes.low_bytes_2 row 0),
            (air.cols.values.bitwise.c_low_bytes.low_bytes_2 row 0)]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_5 row 0), 0,
            ((air.cols.values.b_2 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_2 row 0)) * 2122383361,
            ((air.cols.values.c_2 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_2 row 0)) * 2122383361]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_6 row 0), 0,
            (air.cols.values.bitwise.b_low_bytes.low_bytes_3 row 0),
            (air.cols.values.bitwise.c_low_bytes.low_bytes_3 row 0)]),
          (mult, [5, op, (air.cols.values.bitwise.bitwise.result_7 row 0), 0,
            ((air.cols.values.b_3 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_3 row 0)) * 2122383361,
            ((air.cols.values.c_3 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_3 row 0)) * 2122383361]),
          (-(mult), [4,
            (air.cols.values.is_xor row 0) * 2
              + (air.cols.values.is_or row 0) * 3
              + (air.cols.values.is_and row 0) * 4,
            (air.cols.values.bitwise.bitwise.result_0 row 0) + (air.cols.values.bitwise.bitwise.result_1 row 0) * 256,
            (air.cols.values.bitwise.bitwise.result_2 row 0) + (air.cols.values.bitwise.bitwise.result_3 row 0) * 256,
            (air.cols.values.bitwise.bitwise.result_4 row 0) + (air.cols.values.bitwise.bitwise.result_5 row 0) * 256,
            (air.cols.values.bitwise.bitwise.result_6 row 0) + (air.cols.values.bitwise.bitwise.result_7 row 0) * 256,
            (air.cols.values.b_0 row 0), (air.cols.values.b_1 row 0),
            (air.cols.values.b_2 row 0), (air.cols.values.b_3 row 0),
            (air.cols.values.c_0 row 0), (air.cols.values.c_1 row 0),
            (air.cols.values.c_2 row 0), (air.cols.values.c_3 row 0)])
        ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_BitwiseChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_BitwiseChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_BitwiseChip FKB ExtF)
      (row : ℕ)
    :
      BitwiseChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end BitwiseChip.ConstraintsAndBuses

namespace BitwiseChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `BitwiseChip` row: 8 byte-bus entries (one
      per byte of the 64-bit result) plus 1 ALU entry. -/
  def bus_row (air : Valid_BitwiseChip FKB ExtF) (row : ℕ) : BusRow :=
    let op : FKB :=
      (air.cols.values.is_xor row 0) * 2
        + (air.cols.values.is_or row 0) * 1
        + (air.cols.values.is_and row 0) * 0
    let mult : FKB := air.cols.values.is_real row 0
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(mult),
          #v[
            (air.cols.values.is_xor row 0) * 2
              + (air.cols.values.is_or row 0) * 3
              + (air.cols.values.is_and row 0) * 4,
            (air.cols.values.bitwise.bitwise.result_0 row 0) + (air.cols.values.bitwise.bitwise.result_1 row 0) * 256,
            (air.cols.values.bitwise.bitwise.result_2 row 0) + (air.cols.values.bitwise.bitwise.result_3 row 0) * 256,
            (air.cols.values.bitwise.bitwise.result_4 row 0) + (air.cols.values.bitwise.bitwise.result_5 row 0) * 256,
            (air.cols.values.bitwise.bitwise.result_6 row 0) + (air.cols.values.bitwise.bitwise.result_7 row 0) * 256,
            (air.cols.values.b_0 row 0), (air.cols.values.b_1 row 0),
            (air.cols.values.b_2 row 0), (air.cols.values.b_3 row 0),
            (air.cols.values.c_0 row 0), (air.cols.values.c_1 row 0),
            (air.cols.values.c_2 row 0), (air.cols.values.c_3 row 0) ])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_0 row 0), 0,
          (air.cols.values.bitwise.b_low_bytes.low_bytes_0 row 0),
          (air.cols.values.bitwise.c_low_bytes.low_bytes_0 row 0)]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_1 row 0), 0,
          ((air.cols.values.b_0 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_0 row 0)) * 2122383361,
          ((air.cols.values.c_0 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_0 row 0)) * 2122383361]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_2 row 0), 0,
          (air.cols.values.bitwise.b_low_bytes.low_bytes_1 row 0),
          (air.cols.values.bitwise.c_low_bytes.low_bytes_1 row 0)]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_3 row 0), 0,
          ((air.cols.values.b_1 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_1 row 0)) * 2122383361,
          ((air.cols.values.c_1 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_1 row 0)) * 2122383361]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_4 row 0), 0,
          (air.cols.values.bitwise.b_low_bytes.low_bytes_2 row 0),
          (air.cols.values.bitwise.c_low_bytes.low_bytes_2 row 0)]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_5 row 0), 0,
          ((air.cols.values.b_2 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_2 row 0)) * 2122383361,
          ((air.cols.values.c_2 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_2 row 0)) * 2122383361]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_6 row 0), 0,
          (air.cols.values.bitwise.b_low_bytes.low_bytes_3 row 0),
          (air.cols.values.bitwise.c_low_bytes.low_bytes_3 row 0)]),
        (mult, #v[op, (air.cols.values.bitwise.bitwise.result_7 row 0), 0,
          ((air.cols.values.b_3 row 0) - (air.cols.values.bitwise.b_low_bytes.low_bytes_3 row 0)) * 2122383361,
          ((air.cols.values.c_3 row 0) - (air.cols.values.bitwise.c_low_bytes.low_bytes_3 row 0)) * 2122383361])
      ],
      State := [],
      Memory := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_BitwiseChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (BitwiseChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end BitwiseChip.Interactions

namespace BitwiseChip.Interpretations

  open RV64IM_Interactions
  open BitwiseChip.ConstraintsAndBuses
  open BitwiseChip.Interactions

  /-- Each selector is binary and their sum is 0 or 1. The fourth
      conjunct is the unfolded form of `is_real`, more useful to
      downstream case-splits than the named accessor. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (h_constraints : BitwiseChip.Extraction.allHold air row)
  :
    (air.cols.values.is_xor row 0 = 0 ∨ air.cols.values.is_xor row 0 = 1) ∧
    (air.cols.values.is_or row 0 = 0 ∨ air.cols.values.is_or row 0 = 1) ∧
    (air.cols.values.is_and row 0 = 0 ∨ air.cols.values.is_and row 0 = 1) ∧
    ((air.cols.values.is_xor row 0 + air.cols.values.is_or row 0) + air.cols.values.is_and row 0 = 0 ∨
     (air.cols.values.is_xor row 0 + air.cols.values.is_or row 0) + air.cols.values.is_and row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          Valid_BitwiseValueCols.is_real] at h_constraints
    grind

  /-- At most one selector is active: if any of `is_xor` / `is_or` /
      `is_and` is `1`, the other two are `0`. Follows from
      `selector_breakdown`: each is binary and their sum is at most 1,
      so the active selector forces the others to zero. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (h_constraints : BitwiseChip.Extraction.allHold air row)
  :
    (air.cols.values.is_xor row 0 = 1 →
      air.cols.values.is_or row 0 = 0 ∧ air.cols.values.is_and row 0 = 0) ∧
    (air.cols.values.is_or row 0 = 1 →
      air.cols.values.is_xor row 0 = 0 ∧ air.cols.values.is_and row 0 = 0) ∧
    (air.cols.values.is_and row 0 = 1 →
      air.cols.values.is_xor row 0 = 0 ∧ air.cols.values.is_or row 0 = 0)
  := by
    have h_selectors := selector_breakdown air row h_constraints
    clear *- h_selectors
    grind

end BitwiseChip.Interpretations
