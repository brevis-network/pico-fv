import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.SubChip
import PicoFV.RV64IM.Airs.SubChip
import PicoFV.RV64IM.Constraints.SubGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SubChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and the
list of bus interactions emitted by `SubChip::eval`
(`vm/src/chips/chips/alu/sub/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_SubChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.SubChip`.

The chip layout (matching `SubValueCols<F>`) is:
| Cols  | Field path (under `air.cols.values`)              | Description |
|-------|---------------------------------------------------|-------------|
| 0..3  | `sub_operation.value_0..3`                        | gadget's 4 × u16 limbs of `value` (result) |
| 4..7  | `operand_1_0..3`                                  | first input `b` (minuend, limb 0..3) |
| 8..11 | `operand_2_0..3`                                  | second input `c` (subtrahend, limb 0..3) |
| 12    | `is_sub`                                          | activation flag |

The 5+1 algebraic constraints emitted by the chip are:

- `is_sub ∈ {0, 1}`                                                (twice: c0 + c5)
- 4 × per-limb borrow-boolean checks of the form
  `is_sub * borrow_i * (borrow_i - 1) = 0`, where the limb-`i` borrow is
  reconstructed as
  `borrow_i = ((operand_1_i + 65535 - operand_2_i - value_i) + prev_borrow) * inv(2^16)`
  with `inv(2^16) ≡ 2130673921 (mod KB_prime)` and `prev_borrow_{-1} = 1`
  (the initial "carry-in" of `b + (¬c) + 1`).

The bus interactions are:
- 4 ByteBus entries (opcode 5, sub-op 8) — u16 range-check each `value_i`.
- 1 ALU entry (opcode 4, sub-op 1 = `Opcode::SUB`) — issued only when
  `is_sub = 1` and carries `(value, operand_1, operand_2)`.
-/

namespace SubChip

  open RV64IM_Interactions

  /-- The bus entries the chip contributes per row, packaged as a typed
      `BusRow`. Built compositionally from `SubGadget.AbsBuses` (the four
      `ByteBus` u16-range entries on `value_i`) concatenated with the
      chip-specific `ALUBus` entry for `Opcode::SUB`. -/
  def AbsBuses
    (is_sub
     operand_1_0 operand_1_1 operand_1_2 operand_1_3
     operand_2_0 operand_2_1 operand_2_2 operand_2_3
     value_0 value_1 value_2 value_3 : FKB)
  : BusRow :=
    SubGadget.AbsBuses is_sub value_0 value_1 value_2 value_3
    ++
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(is_sub),
          #v[ 1,
              value_0, value_1, value_2, value_3,
              operand_1_0, operand_1_1, operand_1_2, operand_1_3,
              operand_2_0, operand_2_1, operand_2_2, operand_2_3 ])
      ],
      Byte := [],
      State := [],
      Memory := []
    } : BusRow)

end SubChip

namespace SubChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_sub is boolean.
      -- Comes from the `builder.assert_bool(is_real)` line at the top of
      -- `SubGadget::eval`, invoked by `SubChip::eval` with `is_real = is_sub`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_SubChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sub row 0) * ((air.cols.values.is_sub row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_SubChip F ExtF) (row : ℕ)
      : SubChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 1-4: per-limb borrow-boolean checks.
      -- For limb i, the borrow is
      --   borrow_i = ((operand_1_i + 65535 - operand_2_i - value_i) + prev_borrow) * inv(2^16)
      -- and the constraint is `is_sub * borrow_i * (borrow_i - 1) = 0`,
      -- with `prev_borrow_{-1} = 1` (the +1 of `b + (¬c) + 1`).
      -- =====================================================================

      -- Limb 0: borrow_0 = ((operand_1_0 + 65535 - operand_2_0 - value_0) + 1) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_SubChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sub row 0) * ((((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921) * ((((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_SubChip F ExtF) (row : ℕ)
      : SubChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 1: borrow_1 = ((operand_1_1 + 65535 - operand_2_1 - value_1) + borrow_0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_SubChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sub row 0) * ((((((((air.cols.values.operand_1_1 row 0) + 65536) - 1) - (air.cols.values.operand_2_1 row 0)) - (air.cols.values.sub_operation.value_1 row 0)) + (((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921)) * 2130673921) * ((((((((air.cols.values.operand_1_1 row 0) + 65536) - 1) - (air.cols.values.operand_2_1 row 0)) - (air.cols.values.sub_operation.value_1 row 0)) + (((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_SubChip F ExtF) (row : ℕ)
      : SubChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 2: borrow_2 = ((operand_1_2 + 65535 - operand_2_2 - value_2) + borrow_1) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_SubChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sub row 0) * ((((((((air.cols.values.operand_1_2 row 0) + 65536) - 1) - (air.cols.values.operand_2_2 row 0)) - (air.cols.values.sub_operation.value_2 row 0)) + (((((((air.cols.values.operand_1_1 row 0) + 65536) - 1) - (air.cols.values.operand_2_1 row 0)) - (air.cols.values.sub_operation.value_1 row 0)) + (((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921)) * 2130673921)) * 2130673921) * ((((((((air.cols.values.operand_1_2 row 0) + 65536) - 1) - (air.cols.values.operand_2_2 row 0)) - (air.cols.values.sub_operation.value_2 row 0)) + (((((((air.cols.values.operand_1_1 row 0) + 65536) - 1) - (air.cols.values.operand_2_1 row 0)) - (air.cols.values.sub_operation.value_1 row 0)) + (((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_SubChip F ExtF) (row : ℕ)
      : SubChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 3: borrow_3 = ((operand_1_3 + 65535 - operand_2_3 - value_3) + borrow_2) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_SubChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sub row 0) * ((((((((air.cols.values.operand_1_3 row 0) + 65536) - 1) - (air.cols.values.operand_2_3 row 0)) - (air.cols.values.sub_operation.value_3 row 0)) + (((((((air.cols.values.operand_1_2 row 0) + 65536) - 1) - (air.cols.values.operand_2_2 row 0)) - (air.cols.values.sub_operation.value_2 row 0)) + (((((((air.cols.values.operand_1_1 row 0) + 65536) - 1) - (air.cols.values.operand_2_1 row 0)) - (air.cols.values.sub_operation.value_1 row 0)) + (((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921)) * 2130673921)) * 2130673921)) * 2130673921) * ((((((((air.cols.values.operand_1_3 row 0) + 65536) - 1) - (air.cols.values.operand_2_3 row 0)) - (air.cols.values.sub_operation.value_3 row 0)) + (((((((air.cols.values.operand_1_2 row 0) + 65536) - 1) - (air.cols.values.operand_2_2 row 0)) - (air.cols.values.sub_operation.value_2 row 0)) + (((((((air.cols.values.operand_1_1 row 0) + 65536) - 1) - (air.cols.values.operand_2_1 row 0)) - (air.cols.values.sub_operation.value_1 row 0)) + (((((((air.cols.values.operand_1_0 row 0) + 65536) - 1) - (air.cols.values.operand_2_0 row 0)) - (air.cols.values.sub_operation.value_0 row 0)) + 1) * 2130673921)) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_SubChip F ExtF) (row : ℕ)
      : SubChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 5: is_sub is boolean (chip-level duplicate).
      -- `SubChip::eval` issues `assert_bool(is_sub)` separately from the
      -- gadget's own `assert_bool(is_real)`, so the extracted constraint list
      -- contains the same boolean check twice.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_SubChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sub row 0) * ((air.cols.values.is_sub row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_SubChip F ExtF) (row : ℕ)
      : SubChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 6 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_SubChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row,
          constraint_5 air row
        ]

    end row_constraints

    /-- All 13 column values of a `SubChip` row, in the layout order
        defined by `SubValueCols`. -/
    def row (air : Valid_SubChip FKB ExtF) (r : ℕ) : Vector FKB 13 :=
      #v[ air.cols.values.sub_operation.value_0 r 0,
          air.cols.values.sub_operation.value_1 r 0,
          air.cols.values.sub_operation.value_2 r 0,
          air.cols.values.sub_operation.value_3 r 0,
          air.cols.values.operand_1_0 r 0,
          air.cols.values.operand_1_1 r 0,
          air.cols.values.operand_1_2 r 0,
          air.cols.values.operand_1_3 r 0,
          air.cols.values.operand_2_0 r 0,
          air.cols.values.operand_2_1 r 0,
          air.cols.values.operand_2_2 r 0,
          air.cols.values.operand_2_3 r 0,
          air.cols.values.is_sub r 0 ]

    section row_buses

      -- =====================================================================
      -- Bus interactions emitted by `SubChip::eval` (per row):
      -- 4 ByteBus entries (opcode 5, sub-op 8): u16 range-check `value_i`,
      --   gated by `+is_sub`.
      -- 1 ALU entry (opcode 4, sub-op 1 = Opcode::SUB): carry the operation,
      --   gated by `-is_sub`. Format: [4, opcode_field=1,
      --                                 value_0..3 (a),
      --                                 operand_1_0..3 (b),
      --                                 operand_2_0..3 (c)].
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_SubChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ ((air.cols.values.is_sub row 0), [5, 8, (air.cols.values.sub_operation.value_0 row 0), 0, 0, 0]),
          ((air.cols.values.is_sub row 0), [5, 8, (air.cols.values.sub_operation.value_1 row 0), 0, 0, 0]),
          ((air.cols.values.is_sub row 0), [5, 8, (air.cols.values.sub_operation.value_2 row 0), 0, 0, 0]),
          ((air.cols.values.is_sub row 0), [5, 8, (air.cols.values.sub_operation.value_3 row 0), 0, 0, 0]),
          (-(air.cols.values.is_sub row 0),
            [4, 1,
              (air.cols.values.sub_operation.value_0 row 0),
              (air.cols.values.sub_operation.value_1 row 0),
              (air.cols.values.sub_operation.value_2 row 0),
              (air.cols.values.sub_operation.value_3 row 0),
              (air.cols.values.operand_1_0 row 0),
              (air.cols.values.operand_1_1 row 0),
              (air.cols.values.operand_1_2 row 0),
              (air.cols.values.operand_1_3 row 0),
              (air.cols.values.operand_2_0 row 0),
              (air.cols.values.operand_2_1 row 0),
              (air.cols.values.operand_2_2 row 0),
              (air.cols.values.operand_2_3 row 0)]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_SubChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    -- =====================================================================
    -- Identification: constraints 0..4 conjoin to `SubGadget.AbsConstraints`
    -- instantiated at the chip's accessors, with the substitution
    -- `is_real ↦ is_sub`, `b_i ↦ operand_1_i`, `c_i ↦ operand_2_i`,
    -- `value_i ↦ sub_operation.value_i`. Constraint 5 (the chip-level
    -- duplicate `assert_bool(is_sub)`) is *not* part of the gadget.
    -- =====================================================================

    omit [Field ExtF] in
    @[simp]
    lemma constraint_subset_iff_gadget_00 (air : Valid_SubChip F ExtF) (row : ℕ)
    : (constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row
        ∧ constraint_3 air row ∧ constraint_4 air row)
      ↔
      SubGadget.AbsConstraints
        (air.cols.values.is_sub row 0)
        (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
        (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
        (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
        (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
        (air.cols.values.sub_operation.value_0 row 0)
        (air.cols.values.sub_operation.value_1 row 0)
        (air.cols.values.sub_operation.value_2 row 0)
        (air.cols.values.sub_operation.value_3 row 0)
    := by
      simp [
        SubGadget.AbsConstraints,
        constraint_and_interaction_simplification
      ]

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_SubChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_SubChip FKB ExtF)
      (row : ℕ)
    :
      SubChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end SubChip.ConstraintsAndBuses

namespace SubChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `SubChip` row. Defined directly as
      `SubChip.AbsBuses` applied to the chip's accessors, making
      `bus_row_abs` definitionally true. -/
  def bus_row (air : Valid_SubChip FKB ExtF) (row : ℕ) : BusRow :=
    SubChip.AbsBuses
      (air.cols.values.is_sub row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.sub_operation.value_0 row 0)
      (air.cols.values.sub_operation.value_1 row 0)
      (air.cols.values.sub_operation.value_2 row 0)
      (air.cols.values.sub_operation.value_3 row 0)

  @[simp]
  lemma bus_row_equiv (air : Valid_SubChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (SubChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      SubChip.AbsBuses,
      SubGadget.AbsBuses,
      pico_encapsulation,
    ]

end SubChip.Interactions

namespace SubChip.Interpretations

  open RV64IM_Interactions
  open SubChip.ConstraintsAndBuses
  open SubChip.Interactions

  -- =======================================================================
  -- Interpretation lemmas: derive semantic properties from raw constraints.
  -- =======================================================================

  /-- `is_sub` is forced to `{0, 1}` by `constraint_0` (and redundantly by
      `constraint_5`). -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_SubChip FKB ExtF)
    (row : ℕ)
    (h_constraints : SubChip.Extraction.allHold air row)
  :
    air.cols.values.is_sub row 0 = 0 ∨ air.cols.values.is_sub row 0 = 1
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

  /-- Abstracting the gadget used. Follows the template
      `allHold → preceding ∧ AbsConstraints ∧ following`:

      * Preceding (chip-specific constraints emitted *before* the
        gadget's contribution): none for `SubChip`.
      * `SubGadget.AbsConstraints` instantiated at the chip's accessors
        (`is_real ↦ is_sub`, `b_i ↦ operand_1_i`, `c_i ↦ operand_2_i`,
        `value_i ↦ sub_operation.value_i`) — covers constraints 0..4.
      * Following (chip-specific constraints emitted *after* the
        gadget's contribution): the chip's `constraint_5`, which is
        `SubChip::eval`'s separate `assert_bool(is_sub)` on top of the
        gadget's own boolean check on `is_real`. -/
  lemma allHold_abs
    [Field ExtF]
    (air : Valid_SubChip FKB ExtF)
    (row : ℕ)
    (h_constraints : SubChip.Extraction.allHold air row)
  :
    SubGadget.AbsConstraints
      (air.cols.values.is_sub row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.sub_operation.value_0 row 0)
      (air.cols.values.sub_operation.value_1 row 0)
      (air.cols.values.sub_operation.value_2 row 0)
      (air.cols.values.sub_operation.value_3 row 0)
    ∧ constraint_5 air row
  := by
    simp [
      SubGadget.AbsConstraints,
      constraint_and_interaction_simplification
    ] at h_constraints ⊢
    aesop

  /-- The chip's per-row `BusRow` is exactly `SubChip.AbsBuses` instantiated
      at the chip's accessors. By `SubChip.AbsBuses`'s definition this in
      turn decomposes as `SubGadget.AbsBuses (...) ++ <chip ALU entry>`,
      making the gadget's contribution explicit. -/
  lemma bus_row_abs
    [Field ExtF]
    (air : Valid_SubChip FKB ExtF)
    (row : ℕ)
  :
    SubChip.Interactions.bus_row air row =
    SubChip.AbsBuses
      (air.cols.values.is_sub row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.sub_operation.value_0 row 0)
      (air.cols.values.sub_operation.value_1 row 0)
      (air.cols.values.sub_operation.value_2 row 0)
      (air.cols.values.sub_operation.value_3 row 0)
  := by rfl

end SubChip.Interpretations
