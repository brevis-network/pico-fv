import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.AddwChip
import PicoFV.RV64IM.Airs.AddwChip
import PicoFV.RV64IM.Constraints.AddwGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddwChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and the
list of bus interactions emitted by `AddwChip::eval`
(`vm/src/chips/chips/alu/addw/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_AddwChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.AddwChip`.

The chip layout (matching `AddwValueCols<F>`) is:
| Cols  | Field path (under `air.cols.values`)              | Description |
|-------|---------------------------------------------------|-------------|
| 0..1  | `addw_operation.value_0..1`                       | gadget's 2 × u16 limbs of low 32-bit `value` |
| 2     | `addw_operation.msb.msb`                          | bit-15 of `value_1` (used for sign extension) |
| 3..6  | `operand_1_0..3`                                  | first input `b` (full 64-bit, limb 0..3) |
| 7..10 | `operand_2_0..3`                                  | second input `c` (full 64-bit, limb 0..3) |
| 11    | `is_addw`                                         | activation flag |

The 5+1 algebraic constraints emitted by the chip are:

- `is_addw ∈ {0, 1}`                                                (three times: c0 + c3 + c5;
  the first comes from `AddwGadget::eval`'s own `assert_bool(is_real)`,
  the second from the embedded `U16MSBGadget::eval`'s own
  `assert_bool(is_real)`, and the third from `AddwChip::eval`'s
  separate `assert_bool(is_addw)`.)
- 2 × per-limb carry-boolean checks of the form
  `is_addw * carry_i * (carry_i - 1) = 0`, where the limb-`i` carry is
  reconstructed as
  `carry_i = ((operand_1_i + operand_2_i - value_i) + carry_{i-1}) * inv(2^16)`
  with `inv(2^16) ≡ 2130673921 (mod KB_prime)` and `carry_{-1} = 0`.
- `msb ∈ {0, 1}`.

The bus interactions are:
- 3 ByteBus entries (opcode 5, sub-op 8) — u16 range-check
  `value_0`, `value_1`, and `2 * value_1 - msb * 65536` (this third
  one pins `msb` to bit-15 of `value_1`).
- 1 ALU entry (opcode 4, sub-op 40 = `Opcode::ADDW`) — issued only
  when `is_addw = 1` and carries
  `(value_0, value_1, msb*65535, msb*65535, operand_1, operand_2)`.
  The high-two result limbs are filled in by the chip directly as
  `msb * 65535` (= 0x0000 if `msb = 0`, = 0xFFFF if `msb = 1`), giving
  the sign-extension pattern expected by `execute_RTYPEW_pure`.
-/

namespace AddwChip

  open RV64IM_Interactions

  /-- The bus entries the chip contributes per row, packaged as a typed
      `BusRow`. Built compositionally from `AddwGadget.AbsBuses` (the
      three `ByteBus` entries on `value_0`, `value_1`, and the MSB
      consistency check) concatenated with the chip-specific `ALUBus`
      entry for `Opcode::ADDW`. -/
  def AbsBuses
    (is_addw
     operand_1_0 operand_1_1 operand_1_2 operand_1_3
     operand_2_0 operand_2_1 operand_2_2 operand_2_3
     value_0 value_1 msb : FKB)
  : BusRow :=
    AddwGadget.AbsBuses is_addw value_0 value_1 msb
    ++
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(is_addw),
          #v[ 40,
              value_0, value_1, msb * 65535, msb * 65535,
              operand_1_0, operand_1_1, operand_1_2, operand_1_3,
              operand_2_0, operand_2_1, operand_2_2, operand_2_3 ])
      ],
      Byte := [],
      State := [],
      Memory := []
    } : BusRow)

end AddwChip

namespace AddwChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_addw is boolean (from `AddwGadget::eval`'s own
      -- `assert_bool(is_real)`).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_AddwChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_addw row 0) * ((air.cols.values.is_addw row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_AddwChip F ExtF) (row : ℕ)
      : AddwChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 1-2: per-limb carry-boolean checks (low 32 bits only).
      -- For limb i, the carry is
      --   carry_i = ((operand_1_i + operand_2_i - value_i) + carry_{i-1}) * inv(2^16)
      -- and the constraint is `is_addw * carry_i * (carry_i - 1) = 0`.
      -- =====================================================================

      -- Limb 0: carry_0 = ((operand_1_0 + operand_2_0 - value_0) + 0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_AddwChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_addw row 0) * ((((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.addw_operation.value_0 row 0)) + 0) * 2130673921) * ((((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.addw_operation.value_0 row 0)) + 0) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_AddwChip F ExtF) (row : ℕ)
      : AddwChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 1: carry_1 = ((operand_1_1 + operand_2_1 - value_1) + carry_0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_AddwChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_addw row 0) * ((((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.addw_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.addw_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921) * ((((((air.cols.values.operand_1_1 row 0) + (air.cols.values.operand_2_1 row 0)) - (air.cols.values.addw_operation.value_1 row 0)) + (((((air.cols.values.operand_1_0 row 0) + (air.cols.values.operand_2_0 row 0)) - (air.cols.values.addw_operation.value_0 row 0)) + 0) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_AddwChip F ExtF) (row : ℕ)
      : AddwChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 3: is_addw is boolean (from the embedded
      -- `U16MSBGadget::eval`'s own `assert_bool(is_real)`, applied to
      -- the same `is_real = is_addw`).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_AddwChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_addw row 0) * ((air.cols.values.is_addw row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_AddwChip F ExtF) (row : ℕ)
      : AddwChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 4: msb is boolean.
      -- Comes from `U16MSBGadget::eval`'s `assert_bool(msb)`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_AddwChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.addw_operation.msb.msb row 0) * ((air.cols.values.addw_operation.msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_AddwChip F ExtF) (row : ℕ)
      : AddwChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 5: is_addw is boolean (chip-level duplicate).
      -- `AddwChip::eval` issues `assert_bool(is_addw)` separately from
      -- the two gadget-emitted boolean checks, so the extracted
      -- constraint list contains a third copy.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_AddwChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_addw row 0) * ((air.cols.values.is_addw row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_AddwChip F ExtF) (row : ℕ)
      : AddwChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 6 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_AddwChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row,
          constraint_5 air row
        ]

    end row_constraints

    /-- All 12 column values of an `AddwChip` row, in the layout order
        defined by `AddwValueCols`. -/
    def row (air : Valid_AddwChip FKB ExtF) (r : ℕ) : Vector FKB 12 :=
      #v[ air.cols.values.addw_operation.value_0 r 0,
          air.cols.values.addw_operation.value_1 r 0,
          air.cols.values.addw_operation.msb.msb r 0,
          air.cols.values.operand_1_0 r 0,
          air.cols.values.operand_1_1 r 0,
          air.cols.values.operand_1_2 r 0,
          air.cols.values.operand_1_3 r 0,
          air.cols.values.operand_2_0 r 0,
          air.cols.values.operand_2_1 r 0,
          air.cols.values.operand_2_2 r 0,
          air.cols.values.operand_2_3 r 0,
          air.cols.values.is_addw r 0 ]

    section row_buses

      -- =====================================================================
      -- Bus interactions emitted by `AddwChip::eval` (per row):
      -- 3 ByteBus entries (opcode 5, sub-op 8): u16 range-check
      --   `value_0`, `value_1`, and `2 * value_1 - msb * 65536`, all
      --   gated by `+is_addw`.
      -- 1 ALU entry (opcode 4, sub-op 40 = Opcode::ADDW): carry the
      --   operation, gated by `-is_addw`. Format: [4, opcode_field=40,
      --                                            value_0, value_1,
      --                                            msb*65535, msb*65535,
      --                                            operand_1_0..3 (b),
      --                                            operand_2_0..3 (c)].
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_AddwChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ ((air.cols.values.is_addw row 0),
            [5, 8, (air.cols.values.addw_operation.value_0 row 0), 0, 0, 0]),
          ((air.cols.values.is_addw row 0),
            [5, 8, (air.cols.values.addw_operation.value_1 row 0), 0, 0, 0]),
          ((air.cols.values.is_addw row 0),
            [5, 8,
              2 * (air.cols.values.addw_operation.value_1 row 0)
                - (air.cols.values.addw_operation.msb.msb row 0) * 65536,
              0, 0, 0]),
          (-(air.cols.values.is_addw row 0),
            [4, 40,
              (air.cols.values.addw_operation.value_0 row 0),
              (air.cols.values.addw_operation.value_1 row 0),
              (air.cols.values.addw_operation.msb.msb row 0) * 65535,
              (air.cols.values.addw_operation.msb.msb row 0) * 65535,
              (air.cols.values.operand_1_0 row 0),
              (air.cols.values.operand_1_1 row 0),
              (air.cols.values.operand_1_2 row 0),
              (air.cols.values.operand_1_3 row 0),
              (air.cols.values.operand_2_0 row 0),
              (air.cols.values.operand_2_1 row 0),
              (air.cols.values.operand_2_2 row 0),
              (air.cols.values.operand_2_3 row 0)]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_AddwChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    -- =====================================================================
    -- Identification: constraints 0..4 conjoin to `AddwGadget.AbsConstraints`
    -- instantiated at the chip's accessors, with the substitution
    -- `is_real ↦ is_addw`, `b_i ↦ operand_1_i`, `c_i ↦ operand_2_i`,
    -- `value_i ↦ addw_operation.value_i`, `msb ↦ addw_operation.msb.msb`.
    -- Constraint 5 (the chip-level duplicate `assert_bool(is_addw)`) is
    -- *not* part of the gadget.
    -- =====================================================================

    omit [Field ExtF] in
    @[simp]
    lemma constraint_subset_iff_gadget_00 (air : Valid_AddwChip F ExtF) (row : ℕ)
    : (constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row
        ∧ constraint_3 air row ∧ constraint_4 air row)
      ↔
      AddwGadget.AbsConstraints
        (air.cols.values.is_addw row 0)
        (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
        (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
        (air.cols.values.addw_operation.value_0 row 0)
        (air.cols.values.addw_operation.value_1 row 0)
        (air.cols.values.addw_operation.msb.msb row 0)
    := by
      simp [
        AddwGadget.AbsConstraints,
        U16MSBGadget.AbsConstraints,
        constraint_and_interaction_simplification
      ]

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_AddwChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_AddwChip FKB ExtF)
      (row : ℕ)
    :
      AddwChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end AddwChip.ConstraintsAndBuses

namespace AddwChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `AddwChip` row. Defined directly as
      `AddwChip.AbsBuses` applied to the chip's accessors, making
      `bus_row_abs` definitionally true. -/
  def bus_row (air : Valid_AddwChip FKB ExtF) (row : ℕ) : BusRow :=
    AddwChip.AbsBuses
      (air.cols.values.is_addw row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.addw_operation.value_0 row 0)
      (air.cols.values.addw_operation.value_1 row 0)
      (air.cols.values.addw_operation.msb.msb row 0)

  @[simp]
  lemma bus_row_equiv (air : Valid_AddwChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (AddwChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    dsimp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      AddwChip.AbsBuses,
      AddwGadget.AbsBuses,
      U16MSBGadget.AbsBuses,
      pico_encapsulation,
    ]

end AddwChip.Interactions

namespace AddwChip.Interpretations

  open RV64IM_Interactions
  open AddwChip.ConstraintsAndBuses
  open AddwChip.Interactions

  -- =======================================================================
  -- Interpretation lemmas: derive semantic properties from raw constraints.
  -- =======================================================================

  /-- `is_addw` is forced to `{0, 1}` by `constraint_0` (and redundantly
      by `constraint_3` and `constraint_5`). -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_AddwChip FKB ExtF)
    (row : ℕ)
    (h_constraints : AddwChip.Extraction.allHold air row)
  :
    air.cols.values.is_addw row 0 = 0 ∨ air.cols.values.is_addw row 0 = 1
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

  /-- Abstracting the gadget used. Follows the template
      `allHold → preceding ∧ AbsConstraints ∧ following`:

      * Preceding: none for `AddwChip`.
      * `AddwGadget.AbsConstraints` instantiated at the chip's accessors
        (`is_real ↦ is_addw`, `b_i ↦ operand_1_i`, `c_i ↦ operand_2_i`,
        `value_i ↦ addw_operation.value_i`,
        `msb ↦ addw_operation.msb.msb`) — covers constraints 0..4.
      * Following: the chip's `constraint_5`, which is `AddwChip::eval`'s
        separate `assert_bool(is_addw)` on top of the two
        gadget-emitted boolean checks. -/
  lemma allHold_abs
    [Field ExtF]
    (air : Valid_AddwChip FKB ExtF)
    (row : ℕ)
    (h_constraints : AddwChip.Extraction.allHold air row)
  :
    AddwGadget.AbsConstraints
      (air.cols.values.is_addw row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.addw_operation.value_0 row 0)
      (air.cols.values.addw_operation.value_1 row 0)
      (air.cols.values.addw_operation.msb.msb row 0)
    ∧ constraint_5 air row
  := by
    simp [
      AddwGadget.AbsConstraints,
      U16MSBGadget.AbsConstraints,
      constraint_and_interaction_simplification
    ] at h_constraints ⊢
    aesop

  /-- The chip's per-row `BusRow` is exactly `AddwChip.AbsBuses` instantiated
      at the chip's accessors. By `AddwChip.AbsBuses`'s definition this in
      turn decomposes as `AddwGadget.AbsBuses (...) ++ <chip ALU entry>`,
      making the gadget's contribution explicit. -/
  lemma bus_row_abs
    [Field ExtF]
    (air : Valid_AddwChip FKB ExtF)
    (row : ℕ)
  :
    AddwChip.Interactions.bus_row air row =
    AddwChip.AbsBuses
      (air.cols.values.is_addw row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.addw_operation.value_0 row 0)
      (air.cols.values.addw_operation.value_1 row 0)
      (air.cols.values.addw_operation.msb.msb row 0)
  := by rfl

end AddwChip.Interpretations
