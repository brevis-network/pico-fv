import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.Extraction.CodeRangeGadget
import PicoFV.RV64IM.Airs.CodeRangeGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# CodeRangeGadget — constraints and bus messages

Citations read at Pico v3.2.0.

`CodeRangeCols::eval` (`vm/src/chips/gadgets/code_range.rs`) emits 4 constraints and 3 bus messages, extracted in
`PicoFV.RV64IM.Extraction.CodeRangeGadget`. This file restates them on the named columns of
`Valid_CodeRangeGadgetAir`, with an `_equiv` lemma per constraint.

The wrapper's layout (`extractor/src/gadgets.rs`, `Gadget::CodeRange`):

| columns | name | meaning |
|---------|------|---------|
| 0, 1  | `addr_0`, `addr_1` | the write's address, two 16-bit pieces (caller's input) |
| 2     | `store_width` | `width`, the number of bytes written (caller's input) |
| 3, 4  | `gadget.code_start_0`, `_1` | the code's first byte, two pieces |
| 5, 6  | `gadget.code_end_0`, `_1` | one past the code's last byte, two pieces |
| 7     | `gadget.below` | 1 when the write lies below the code, 0 when above it |
| 8     | `gadget.borrow` | the borrow out of the distance's low piece: 0, 1 or 2 |
| 9, 10 | `gadget.distance_0`, `_1` | the distance from the write to the code, two pieces |
| 11    | `is_store` | the caller's flag: the row is a store (caller's input) |

The 4 constraints:
- `below ∈ {0, 1}`;
- `borrow ∈ {0, 1, 2}`;
- when `is_store`, `distance_0 = low + 2^16 borrow`, where `low` is
  `code_start_0 - addr_0 - store_width` below the code and `addr_0 - code_end_0` above it;
- when `is_store`, `distance_1 = high - borrow`, where `high` is `code_start_1 - addr_1` below the
  code and `addr_1 - code_end_1` above it.

The 3 bus messages, each with multiplicity `is_store`:
- the code-range lookup `[code_start_0, code_start_1, code_end_0, code_end_1]` on the Program
  tag (`CodeRangeBusEntry`), which the Program table answers;
- a `U16Range` check of `distance_0` and one of `distance_1` on the byte bus.
-/

namespace CodeRangeGadget

  /-- The gadget's constraints on one row, on its column values and the caller's inputs. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_store addr_0 addr_1 store_width
     code_start_0 code_start_1 code_end_0 code_end_1
     below borrow distance_0 distance_1 : F)
  : Prop :=
    (below * (below - 1) = 0) ∧
    (borrow * (borrow - 1) * (borrow - 2) = 0) ∧
    (is_store * (distance_0 -
      ((below * ((0 + code_start_0 - addr_0) - store_width) + (1 - below) * (addr_0 - code_end_0)) +
        65536 * borrow)) = 0) ∧
    (is_store * (distance_1 -
      ((below * (0 + code_start_1 - addr_1) + (1 - below) * (addr_1 - code_end_1)) -
        borrow)) = 0)

  /-- The gadget's bus messages on one row: the code-range lookup and the two `U16Range` checks
      of the distance, each with multiplicity `is_store`. A chip that embeds the gadget adds these
      to its own row. -/
  def AbsBuses
    (is_store code_start_0 code_start_1 code_end_0 code_end_1 distance_0 distance_1 : FKB)
  : RV64IM_Interactions.BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map RV64IM_Interactions.ByteBusEntry.deserialise [
        (is_store, #v[8, distance_0, 0, 0, 0]),
        (is_store, #v[8, distance_1, 0, 0, 0])
      ],
      State := [],
      Memory := [],
      CodeRange := [
        RV64IM_Interactions.CodeRangeBusEntry.deserialise
          (is_store, #v[code_start_0, code_start_1, code_end_0, code_end_1])
      ]
    }

end CodeRangeGadget

namespace CodeRangeGadget.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- Constraint 0: `below ∈ {0, 1}`.
      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.gadget.below row 0) * ((air.cols.gadget.below row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ)
      : CodeRangeGadget.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 1: `borrow ∈ {0, 1, 2}`.
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.gadget.borrow row 0) * ((air.cols.gadget.borrow row 0) - 1)) *
          ((air.cols.gadget.borrow row 0) - 2)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ)
      : CodeRangeGadget.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 2: the distance's low piece, when `is_store`.
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_store row 0) * ((air.cols.gadget.distance_0 row 0) -
          ((((air.cols.gadget.below row 0) *
              (((0 + (air.cols.gadget.code_start_0 row 0)) - (air.cols.addr_0 row 0)) -
                (air.cols.store_width row 0))) +
            ((1 - (air.cols.gadget.below row 0)) *
              ((air.cols.addr_0 row 0) - (air.cols.gadget.code_end_0 row 0)))) +
          (65536 * (air.cols.gadget.borrow row 0))))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ)
      : CodeRangeGadget.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 3: the distance's high piece, when `is_store`.
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_store row 0) * ((air.cols.gadget.distance_1 row 0) -
          ((((air.cols.gadget.below row 0) *
              ((0 + (air.cols.gadget.code_start_1 row 0)) - (air.cols.addr_1 row 0))) +
            ((1 - (air.cols.gadget.below row 0)) *
              ((air.cols.addr_1 row 0) - (air.cols.gadget.code_end_1 row 0)))) -
          (air.cols.gadget.borrow row 0)))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ)
      : CodeRangeGadget.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_CodeRangeGadgetAir F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row
        ]

    end row_constraints

    section row_buses

      -- The code-range lookup (Program tag 2, 4 fields) and the two `U16Range` checks
      -- (Byte tag 5, opcode 8), each with multiplicity `is_store`.
      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_CodeRangeGadgetAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ ((air.cols.is_store row 0),
            [2, (air.cols.gadget.code_start_0 row 0), (air.cols.gadget.code_start_1 row 0),
              (air.cols.gadget.code_end_0 row 0), (air.cols.gadget.code_end_1 row 0)]),
          ((air.cols.is_store row 0), [5, 8, (air.cols.gadget.distance_0 row 0), 0, 0, 0]),
          ((air.cols.is_store row 0), [5, 8, (air.cols.gadget.distance_1 row 0), 0, 0, 0]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_CodeRangeGadgetAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_CodeRangeGadgetAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_CodeRangeGadgetAir FKB ExtF)
      (row : ℕ)
    :
      CodeRangeGadget.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end CodeRangeGadget.ConstraintsAndBuses

namespace CodeRangeGadget.Interactions

  /-- The standalone gadget air's messages on one row, sorted: exactly the gadget's own. -/
  def bus_row (air : Valid_CodeRangeGadgetAir FKB ExtF) (row : ℕ) : RV64IM_Interactions.BusRow :=
    CodeRangeGadget.AbsBuses
      (air.cols.is_store row 0)
      (air.cols.gadget.code_start_0 row 0) (air.cols.gadget.code_start_1 row 0)
      (air.cols.gadget.code_end_0 row 0) (air.cols.gadget.code_end_1 row 0)
      (air.cols.gadget.distance_0 row 0) (air.cols.gadget.distance_1 row 0)

  /-- Sorting the row's raw messages gives `bus_row`: the 4-field message is kept as a
      code-range lookup. -/
  @[simp]
  lemma bus_row_equiv (air : Valid_CodeRangeGadgetAir FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (CodeRangeGadget.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      RV64IM_Interactions.deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      CodeRangeGadget.AbsBuses,
      pico_encapsulation,
    ]

end CodeRangeGadget.Interactions

namespace CodeRangeGadget.Interpretations

  open CodeRangeGadget.ConstraintsAndBuses
  open CodeRangeGadget.Interactions

  /-- The extracted constraints give `AbsConstraints` on the row's column values. -/
  lemma allHold_abs
    [Field ExtF]
    (air : Valid_CodeRangeGadgetAir FKB ExtF)
    (row : ℕ)
    (h_constraints : CodeRangeGadget.Extraction.allHold air row)
  :
    CodeRangeGadget.AbsConstraints
      (air.cols.is_store row 0)
      (air.cols.addr_0 row 0) (air.cols.addr_1 row 0) (air.cols.store_width row 0)
      (air.cols.gadget.code_start_0 row 0) (air.cols.gadget.code_start_1 row 0)
      (air.cols.gadget.code_end_0 row 0) (air.cols.gadget.code_end_1 row 0)
      (air.cols.gadget.below row 0) (air.cols.gadget.borrow row 0)
      (air.cols.gadget.distance_0 row 0) (air.cols.gadget.distance_1 row 0)
  := by
    simp only [allHold_iff_allHold_simplified, allHold_simplified, row_constraint_list,
      List.forall_cons, List.Forall] at h_constraints
    obtain ⟨ _, h0, h1, h2, h3 ⟩ := h_constraints
    exact ⟨ h0, h1, h2, h3 ⟩

  /-- The standalone gadget air's bus row is `AbsBuses` on the row's column values. -/
  lemma bus_row_abs
    [Field ExtF]
    (air : Valid_CodeRangeGadgetAir FKB ExtF)
    (row : ℕ)
  :
    CodeRangeGadget.Interactions.bus_row air row =
    CodeRangeGadget.AbsBuses
      (air.cols.is_store row 0)
      (air.cols.gadget.code_start_0 row 0) (air.cols.gadget.code_start_1 row 0)
      (air.cols.gadget.code_end_0 row 0) (air.cols.gadget.code_end_1 row 0)
      (air.cols.gadget.distance_0 row 0) (air.cols.gadget.distance_1 row 0)
  := by
    rfl

end CodeRangeGadget.Interpretations
