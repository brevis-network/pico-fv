import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.AddChip
import PicoFV.RV64IM.Airs.AddChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and the
list of bus interactions emitted by `AddChip::eval`
(`vm/src/chips/chips/alu/add/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_AddChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.AddChip`.

The chip layout (matching `AddValueCols<F>`) is:
| Cols  | Field path (under `air.cols.values`)              | Description |
|-------|---------------------------------------------------|-------------|
| 0..3  | `add_operation.value_0..3`                        | gadget's 4 × u16 limbs of `value` (result) |
| 4..7  | `operand_1_0..3`                                  | first input `b` (limb 0..3) |
| 8..11 | `operand_2_0..3`                                  | second input `c` (limb 0..3) |
| 12    | `is_add`                                          | activation flag |

The 5+1 algebraic constraints emitted by the chip are:

- `is_add ∈ {0, 1}`                                                (twice: c0 + c5)
- 4 × per-limb carry-boolean checks of the form
  `is_add * carry_i * (carry_i - 1) = 0`, where the limb-`i` carry is
  reconstructed as
  `carry_i = ((operand_1_i + operand_2_i - value_i) + carry_{i-1}) * inv(2^16)`
  with `inv(2^16) ≡ 2130673921 (mod KB_prime)` and `carry_{-1} = 0`.

The bus interactions are:
- 4 ByteBus entries (opcode 4, sub-op 8) — u16 range-check each `value_i`.
- 1 ALU entry (opcode 3, sub-op 0 = `Opcode::ADD`) — issued only when
  `is_add = 1` and carries `(value, operand_1, operand_2)`.
-/

namespace AddChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_add is boolean.
      -- Comes from the `builder.assert_bool(is_real)` line at the top of
      -- `AddGadget::eval`, invoked by `AddChip::eval` with `is_real = is_add`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_AddChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_add row 0) * ((air.cols.values.is_add row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_AddChip F ExtF) (row : ℕ)
      : AddChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 1-4: per-limb carry-boolean checks.
      -- For limb i, the carry is
      --   carry_i = ((operand_1_i + operand_2_i - value_i) + carry_{i-1}) * inv(2^16)
      -- and the constraint is `is_add * carry_i * (carry_i - 1) = 0`.
      -- =====================================================================

      -- Limb 0: carry_0 = ((operand_1_0 + operand_2_0 - value_0) + 0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_AddChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_add row 0) * ((((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921) * ((((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_AddChip F ExtF) (row : ℕ)
      : AddChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 1: carry_1 = ((operand_1_1 + operand_2_1 - value_1) + carry_0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_AddChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_add row 0) * ((((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.add_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921) * ((((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.add_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_AddChip F ExtF) (row : ℕ)
      : AddChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 2: carry_2 = ((operand_1_2 + operand_2_2 - value_2) + carry_1) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_AddChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_add row 0) * ((((((air.cols.values.operand_1_2 row 0) + (air.cols.values.operand_2_2 row 0)) - (air.cols.values.add_operation.value_2 row 0)) + (((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.add_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921) * ((((((air.cols.values.operand_1_2 row 0) + (air.cols.values.operand_2_2 row 0)) - (air.cols.values.add_operation.value_2 row 0)) + (((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.add_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_AddChip F ExtF) (row : ℕ)
      : AddChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 3: carry_3 = ((operand_1_3 + operand_2_3 - value_3) + carry_2) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_AddChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_add row 0) * ((((((air.cols.values.operand_1_3 row 0) + (air.cols.values.operand_2_3 row 0)) - (air.cols.values.add_operation.value_3 row 0)) + (((((air.cols.values.operand_1_2 row 0) + (air.cols.values.operand_2_2 row 0)) - (air.cols.values.add_operation.value_2 row 0)) + (((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.add_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921)) * 2130673921) * ((((((air.cols.values.operand_1_3 row 0) + (air.cols.values.operand_2_3 row 0)) - (air.cols.values.add_operation.value_3 row 0)) + (((((air.cols.values.operand_1_2 row 0) + (air.cols.values.operand_2_2 row 0)) - (air.cols.values.add_operation.value_2 row 0)) + (((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.add_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.add_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_AddChip F ExtF) (row : ℕ)
      : AddChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 5: is_add is boolean (chip-level duplicate).
      -- `AddChip::eval` issues `assert_bool(is_add)` separately from the
      -- gadget's own `assert_bool(is_real)`, so the extracted constraint list
      -- contains the same boolean check twice.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_AddChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_add row 0) * ((air.cols.values.is_add row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_AddChip F ExtF) (row : ℕ)
      : AddChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 6 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_AddChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row,
          constraint_5 air row
        ]

    end row_constraints

    /-- All 13 column values of an `AddChip` row, in the layout order
        defined by `AddValueCols`. -/
    def row (air : Valid_AddChip FKB ExtF) (r : ℕ) : Vector FKB 13 :=
      #v[ air.cols.values.add_operation.value_0 r 0,
          air.cols.values.add_operation.value_1 r 0,
          air.cols.values.add_operation.value_2 r 0,
          air.cols.values.add_operation.value_3 r 0,
          air.cols.values.operand_1_0 r 0,
          air.cols.values.operand_1_1 r 0,
          air.cols.values.operand_1_2 r 0,
          air.cols.values.operand_1_3 r 0,
          air.cols.values.operand_2_0 r 0,
          air.cols.values.operand_2_1 r 0,
          air.cols.values.operand_2_2 r 0,
          air.cols.values.operand_2_3 r 0,
          air.cols.values.is_add r 0 ]

    section row_buses

      -- =====================================================================
      -- Bus interactions emitted by `AddChip::eval` (per row):
      -- 4 ByteBus entries (opcode 4, sub-op 8): u16 range-check `value_i`,
      --   gated by `-is_add`.
      -- 1 ALU entry (opcode 3, sub-op 0 = Opcode::ADD): carry the operation,
      --   gated by `+is_add`. Format: [3, opcode_field=0,
      --                                 value_0..3 (a),
      --                                 operand_1_0..3 (b),
      --                                 operand_2_0..3 (c)].
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_AddChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ (-(air.cols.values.is_add row 0), [4, 8, (air.cols.values.add_operation.value_0 row 0), 0, 0, 0]),
          (-(air.cols.values.is_add row 0), [4, 8, (air.cols.values.add_operation.value_1 row 0), 0, 0, 0]),
          (-(air.cols.values.is_add row 0), [4, 8, (air.cols.values.add_operation.value_2 row 0), 0, 0, 0]),
          (-(air.cols.values.is_add row 0), [4, 8, (air.cols.values.add_operation.value_3 row 0), 0, 0, 0]),
          ((air.cols.values.is_add row 0),
            [3, 0,
              (air.cols.values.add_operation.value_0 row 0),
              (air.cols.values.add_operation.value_1 row 0),
              (air.cols.values.add_operation.value_2 row 0),
              (air.cols.values.add_operation.value_3 row 0),
              (air.cols.values.operand_1_0 row 0),
              (air.cols.values.operand_1_1 row 0),
              (air.cols.values.operand_1_2 row 0),
              (air.cols.values.operand_1_3 row 0),
              (air.cols.values.operand_2_0 row 0),
              (air.cols.values.operand_2_1 row 0),
              (air.cols.values.operand_2_2 row 0),
              (air.cols.values.operand_2_3 row 0)]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_AddChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_AddChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_AddChip FKB ExtF)
      (row : ℕ)
    :
      AddChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        AddChip.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold AddChip.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end AddChip.ConstraintsAndBuses

namespace AddChip.Interactions

  open RV64IM_Interactions

  /-- The four `ByteBus` and one `ALUBus` rows emitted per `AddChip` row,
      packaged as a typed `BusRow`. Mirrors `raw_bus_row` but typed through
      the bus-entry deserialisers. -/
  def bus_row (air : Valid_AddChip FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((air.cols.values.is_add row 0),
          #v[ 0,
              (air.cols.values.add_operation.value_0 row 0),
              (air.cols.values.add_operation.value_1 row 0),
              (air.cols.values.add_operation.value_2 row 0),
              (air.cols.values.add_operation.value_3 row 0),
              (air.cols.values.operand_1_0 row 0),
              (air.cols.values.operand_1_1 row 0),
              (air.cols.values.operand_1_2 row 0),
              (air.cols.values.operand_1_3 row 0),
              (air.cols.values.operand_2_0 row 0),
              (air.cols.values.operand_2_1 row 0),
              (air.cols.values.operand_2_2 row 0),
              (air.cols.values.operand_2_3 row 0) ])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-(air.cols.values.is_add row 0), #v[8, (air.cols.values.add_operation.value_0 row 0), 0, 0, 0]),
        (-(air.cols.values.is_add row 0), #v[8, (air.cols.values.add_operation.value_1 row 0), 0, 0, 0]),
        (-(air.cols.values.is_add row 0), #v[8, (air.cols.values.add_operation.value_2 row 0), 0, 0, 0]),
        (-(air.cols.values.is_add row 0), #v[8, (air.cols.values.add_operation.value_3 row 0), 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_AddChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (AddChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end AddChip.Interactions

namespace AddChip.Interpretations

  open RV64IM_Interactions
  open AddChip.ConstraintsAndBuses
  open AddChip.Interactions

  -- =======================================================================
  -- Interpretation lemmas: derive semantic properties from raw constraints.
  -- =======================================================================

  /-- `is_add` is forced to `{0, 1}` by `constraint_0` (and redundantly by
      `constraint_5`). -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_AddChip FKB ExtF)
    (row : ℕ)
    (h_constraints : AddChip.Extraction.allHold air row)
  :
    air.cols.values.is_add row 0 = 0 ∨ air.cols.values.is_add row 0 = 1
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

end AddChip.Interpretations
