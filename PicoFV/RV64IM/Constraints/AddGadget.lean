import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.AddGadget
import PicoFV.RV64IM.Airs.AddGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddGadget — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each of the 5
constraints and the 4 byte-bus interactions emitted by `AddGadget::eval`
(`vm/src/chips/gadgets/add.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_AddGadgetAir`'s named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.AddGadget`.

The wrapping air's `AddGadgetExtractionCols` layout is:
| Cols  | Field path                | Description |
|-------|---------------------------|-------------|
| 0..3  | `b_0..3`                  | operand `b` (4 × u16 limbs) |
| 4..7  | `c_0..3`                  | operand `c` (4 × u16 limbs) |
| 8..11 | `gadget.value_0..3`       | result `value = b + c` (4 × u16 limbs) |
| 12    | `is_real`                 | activation flag |

The 5 algebraic constraints are:
- `is_real ∈ {0, 1}`
- 4 × per-limb carry-boolean checks of the form
  `is_real * carry_i * (carry_i - 1) = 0`, where the limb-`i` carry is
  reconstructed as
  `carry_i = ((b_i + c_i - value_i) + carry_{i-1}) * inv(2^16)`
  with `inv(2^16) ≡ 2130673921 (mod KB_prime)` and `carry_{-1} = 0`.

The 4 bus interactions are u16 range-checks of each `value_i` on the byte
bus (opcode 4, sub-op 8 = `U16Range`), gated by `-is_real`.
-/

namespace AddGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `AddGadget` asserts on a
      row, expressed parametrically in the 13 column values. This is a
      *circuit-side* statement — it describes only what the gadget's
      polynomial constraints check, with no claim about the resulting
      arithmetic meaning. The downstream semantic statement that
      `value = b + c` (with appropriate u16 bounds) lives in a separate
      `AddGadget.Spec` / equivalence proof.

      Any chip that embeds an `AddGadget` should be able to derive
      `AbsConstraints` (instantiated at its own accessors) from `allHold` —
      see `AddGadget.Interpretations.allHold_abs` and its analog in each
      consuming chip. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     value_0 value_1 value_2 value_3 : F)
  : Prop :=
    let carry_0 := ((b_0 + c_0 - value_0) + 0) * 2130673921
    let carry_1 := ((b_1 + c_1 - value_1) + carry_0) * 2130673921
    let carry_2 := ((b_2 + c_2 - value_2) + carry_1) * 2130673921
    let carry_3 := ((b_3 + c_3 - value_3) + carry_2) * 2130673921
    (is_real * (is_real - 1) = 0) ∧
    (is_real * (carry_0 * (carry_0 - 1)) = 0) ∧
    (is_real * (carry_1 * (carry_1 - 1)) = 0) ∧
    (is_real * (carry_2 * (carry_2 - 1)) = 0) ∧
    (is_real * (carry_3 * (carry_3 - 1)) = 0)

  /-- The bus entries the Pico `AddGadget` contributes per row, packaged
      as a typed `BusRow`. Parametrised by just the column values that
      flow into the entries (`is_real` and the four `value_i` limbs).

      Compositionality. A chip embedding the gadget will have its own
      per-row `BusRow` built as `AbsBuses` (instantiated at the chip's
      accessors) extended with the chip's own bus entries on each of the
      `Program/ALU/Byte/State/Memory` lists. The standalone
      `Valid_AddGadgetAir` has nothing else to add — see
      `Interactions.bus_row_eq_abs`. -/
  def AbsBuses
    (is_real value_0 value_1 value_2 value_3 : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        (-(is_real), #v[8, value_0, 0, 0, 0]),
        (-(is_real), #v[8, value_1, 0, 0, 0]),
        (-(is_real), #v[8, value_2, 0, 0, 0]),
        (-(is_real), #v[8, value_3, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

end AddGadget

namespace AddGadget.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_real ∈ {0, 1}.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_AddGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((air.cols.is_real row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_AddGadgetAir F ExtF) (row : ℕ)
      : AddGadget.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 1-4: per-limb carry-boolean checks.
      -- =====================================================================

      -- Limb 0: carry_0 = ((b_0 + c_0 - value_0) + 0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_AddGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921) * ((((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_AddGadgetAir F ExtF) (row : ℕ)
      : AddGadget.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 1: carry_1 = ((b_1 + c_1 - value_1) + carry_0) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_AddGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((((((air.cols.b_1 row 0) + (air.cols.c_1 row 0)) - (air.cols.gadget.value_1 row 0)) + (((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921)) * 2130673921) * ((((((air.cols.b_1 row 0) + (air.cols.c_1 row 0)) - (air.cols.gadget.value_1 row 0)) + (((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_AddGadgetAir F ExtF) (row : ℕ)
      : AddGadget.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 2: carry_2 = ((b_2 + c_2 - value_2) + carry_1) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_AddGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((((((air.cols.b_2 row 0) + (air.cols.c_2 row 0)) - (air.cols.gadget.value_2 row 0)) + (((((air.cols.b_1 row 0) + (air.cols.c_1 row 0)) - (air.cols.gadget.value_1 row 0)) + (((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921) * ((((((air.cols.b_2 row 0) + (air.cols.c_2 row 0)) - (air.cols.gadget.value_2 row 0)) + (((((air.cols.b_1 row 0) + (air.cols.c_1 row 0)) - (air.cols.gadget.value_1 row 0)) + (((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_AddGadgetAir F ExtF) (row : ℕ)
      : AddGadget.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Limb 3: carry_3 = ((b_3 + c_3 - value_3) + carry_2) * inv(2^16)
      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_AddGadgetAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_real row 0) * ((((((air.cols.b_3 row 0) + (air.cols.c_3 row 0)) - (air.cols.gadget.value_3 row 0)) + (((((air.cols.b_2 row 0) + (air.cols.c_2 row 0)) - (air.cols.gadget.value_2 row 0)) + (((((air.cols.b_1 row 0) + (air.cols.c_1 row 0)) - (air.cols.gadget.value_1 row 0)) + (((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921)) * 2130673921) * ((((((air.cols.b_3 row 0) + (air.cols.c_3 row 0)) - (air.cols.gadget.value_3 row 0)) + (((((air.cols.b_2 row 0) + (air.cols.c_2 row 0)) - (air.cols.gadget.value_2 row 0)) + (((((air.cols.b_1 row 0) + (air.cols.c_1 row 0)) - (air.cols.gadget.value_1 row 0)) + (((((air.cols.b_0 row 0) + (air.cols.c_0 row 0)) - (air.cols.gadget.value_0 row 0)) + 0) * 2130673921)) * 2130673921)) * 2130673921)) * 2130673921) - 1))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_AddGadgetAir F ExtF) (row : ℕ)
      : AddGadget.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 5 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_AddGadgetAir F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row
        ]

    end row_constraints

    /-- All 13 column values of an `AddGadgetExtractionCols` row, in layout
        order. -/
    def row (air : Valid_AddGadgetAir FKB ExtF) (r : ℕ) : Vector FKB 13 :=
      #v[ air.cols.b_0 r 0,
          air.cols.b_1 r 0,
          air.cols.b_2 r 0,
          air.cols.b_3 r 0,
          air.cols.c_0 r 0,
          air.cols.c_1 r 0,
          air.cols.c_2 r 0,
          air.cols.c_3 r 0,
          air.cols.gadget.value_0 r 0,
          air.cols.gadget.value_1 r 0,
          air.cols.gadget.value_2 r 0,
          air.cols.gadget.value_3 r 0,
          air.cols.is_real r 0 ]

    section row_buses

      -- =====================================================================
      -- Bus interactions emitted by `AddGadget::eval` (per row):
      -- 4 ByteBus entries (opcode 4, sub-op 8 = U16Range): u16 range-check
      -- each `value_i`, gated by `-is_real`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_AddGadgetAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ (-(air.cols.is_real row 0), [4, 8, (air.cols.gadget.value_0 row 0), 0, 0, 0]),
          (-(air.cols.is_real row 0), [4, 8, (air.cols.gadget.value_1 row 0), 0, 0, 0]),
          (-(air.cols.is_real row 0), [4, 8, (air.cols.gadget.value_2 row 0), 0, 0, 0]),
          (-(air.cols.is_real row 0), [4, 8, (air.cols.gadget.value_3 row 0), 0, 0, 0]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_AddGadgetAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_AddGadgetAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_AddGadgetAir FKB ExtF)
      (row : ℕ)
    :
      AddGadget.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end AddGadget.ConstraintsAndBuses

namespace AddGadget.Interactions

  open RV64IM_Interactions

  /-- The bus row emitted per `AddGadget` row, packaged as a typed
      `BusRow`. Identical (by `rfl`) to `AbsBuses` instantiated at the
      air's accessors, since the standalone gadget air contributes
      nothing beyond the gadget's own entries. -/
  def bus_row (air : Valid_AddGadgetAir FKB ExtF) (row : ℕ) : BusRow :=
    AddGadget.AbsBuses
      (air.cols.is_real row 0)
      (air.cols.gadget.value_0 row 0)
      (air.cols.gadget.value_1 row 0)
      (air.cols.gadget.value_2 row 0)
      (air.cols.gadget.value_3 row 0)

  @[simp]
  lemma bus_row_equiv (air : Valid_AddGadgetAir FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (AddGadget.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      AddGadget.AbsBuses,
      pico_encapsulation,
    ]

end AddGadget.Interactions

namespace AddGadget.Interpretations

  open AddGadget.ConstraintsAndBuses
  open AddGadget.Interactions

  /-- `is_real` is forced to `{0, 1}` by `constraint_0`. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_AddGadgetAir FKB ExtF)
    (row : ℕ)
    (h_constraints : AddGadget.Extraction.allHold air row)
  :
    air.cols.is_real row 0 = 0 ∨ air.cols.is_real row 0 = 1
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

  /-- Abstracting the gadgets used -/
  lemma allHold_abs
    [Field ExtF]
    (air : Valid_AddGadgetAir FKB ExtF)
    (row : ℕ)
    (h_constraints : AddGadget.Extraction.allHold air row)
  :
    AddGadget.AbsConstraints
      (air.cols.is_real row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0)
      (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0)
      (air.cols.c_2 row 0) (air.cols.c_3 row 0)
      (air.cols.gadget.value_0 row 0) (air.cols.gadget.value_1 row 0)
      (air.cols.gadget.value_2 row 0) (air.cols.gadget.value_3 row 0)
  := by
    simp [
      AddGadget.AbsConstraints,
      constraint_and_interaction_simplification
    ] at h_constraints ⊢
    aesop

  /-- The per-row bus contribution of the standalone gadget air, viewed
      as a typed `BusRow`, is exactly `AbsBuses` applied to the row's
      cell values. A chip embedding the gadget will state the same with
      its own `Program/ALU/Byte/State/Memory` entries extending each list
      of `AbsBuses`; the standalone gadget has nothing else to add, so
      the relation is equality. -/
  lemma bus_row_abs
    [Field ExtF]
    (air : Valid_AddGadgetAir FKB ExtF)
    (row : ℕ)
  :
    AddGadget.Interactions.bus_row air row =
    AddGadget.AbsBuses
      (air.cols.is_real row 0)
      (air.cols.gadget.value_0 row 0)
      (air.cols.gadget.value_1 row 0)
      (air.cols.gadget.value_2 row 0)
      (air.cols.gadget.value_3 row 0)
  := by
    rfl

end AddGadget.Interpretations
