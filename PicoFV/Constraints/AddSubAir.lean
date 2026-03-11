import PicoFV.RVSail.RV32IM.Operations
import PicoFV.Extraction.AddSubAir
import PicoFV.Airs.AddSubAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace AddSubAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((((air.cols.operand_1_0 row 0) + (air.cols.operand_2_0 row 0)) - (air.cols.add_value_0 row 0)) * ((((air.cols.operand_1_0 row 0) + (air.cols.operand_2_0 row 0)) - (air.cols.add_value_0 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((((air.cols.operand_1_1 row 0) + (air.cols.operand_2_1 row 0)) - (air.cols.add_value_1 row 0)) + (air.cols.add_carry_0 row 0)) * (((((air.cols.operand_1_1 row 0) + (air.cols.operand_2_1 row 0)) - (air.cols.add_value_1 row 0)) + (air.cols.add_carry_0 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((((air.cols.operand_1_2 row 0) + (air.cols.operand_2_2 row 0)) - (air.cols.add_value_2 row 0)) + (air.cols.add_carry_1 row 0)) * (((((air.cols.operand_1_2 row 0) + (air.cols.operand_2_2 row 0)) - (air.cols.add_value_2 row 0)) + (air.cols.add_carry_1 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((((air.cols.operand_1_3 row 0) + (air.cols.operand_2_3 row 0)) - (air.cols.add_value_3 row 0)) + (air.cols.add_carry_2 row 0)) * (((((air.cols.operand_1_3 row 0) + (air.cols.operand_2_3 row 0)) - (air.cols.add_value_3 row 0)) + (air.cols.add_carry_2 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((air.cols.add_carry_0 row 0) * ((((air.cols.operand_1_0 row 0) + (air.cols.operand_2_0 row 0)) - (air.cols.add_value_0 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((air.cols.add_carry_1 row 0) * (((((air.cols.operand_1_1 row 0) + (air.cols.operand_2_1 row 0)) - (air.cols.add_value_1 row 0)) + (air.cols.add_carry_0 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((air.cols.add_carry_2 row 0) * (((((air.cols.operand_1_2 row 0) + (air.cols.operand_2_2 row 0)) - (air.cols.add_value_2 row 0)) + (air.cols.add_carry_1 row 0)) - 256))) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((air.cols.add_carry_0 row 0) - 1) * (((air.cols.operand_1_0 row 0) + (air.cols.operand_2_0 row 0)) - (air.cols.add_value_0 row 0)))) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((air.cols.add_carry_1 row 0) - 1) * ((((air.cols.operand_1_1 row 0) + (air.cols.operand_2_1 row 0)) - (air.cols.add_value_1 row 0)) + (air.cols.add_carry_0 row 0)))) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((air.cols.add_carry_2 row 0) - 1) * ((((air.cols.operand_1_2 row 0) + (air.cols.operand_2_2 row 0)) - (air.cols.add_value_2 row 0)) + (air.cols.add_carry_1 row 0)))) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((air.cols.add_carry_0 row 0) * ((air.cols.add_carry_0 row 0) - 1))) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((air.cols.add_carry_1 row 0) * ((air.cols.add_carry_1 row 0) - 1))) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * ((air.cols.add_carry_2 row 0) * ((air.cols.add_carry_2 row 0) - 1))) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) - 1))) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_add row 0) * ((air.cols.is_add row 0) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_sub row 0) * ((air.cols.is_sub row 0) - 1)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_AddSubAir F ExtF) (row : ℕ) : Prop :=
        (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) * (((air.cols.is_add row 0) + (air.cols.is_sub row 0)) - 1)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_AddSubAir F ExtF) (row : ℕ)
      : AddSubAir.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_AddSubAir F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row,
          constraint_5 air row,
          constraint_6 air row,
          constraint_7 air row,
          constraint_8 air row,
          constraint_9 air row,
          constraint_10 air row,
          constraint_11 air row,
          constraint_12 air row,
          constraint_13 air row,
          constraint_14 air row,
          constraint_15 air row,
          constraint_16 air row
        ]

    end row_constraints

    section row_buses

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_AddSubAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), [4, 7, 0, 0, (air.cols.operand_1_0 row 0), (air.cols.operand_1_1 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), [4, 7, 0, 0, (air.cols.operand_1_2 row 0), (air.cols.operand_1_3 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), [4, 7, 0, 0, (air.cols.operand_2_0 row 0), (air.cols.operand_2_1 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), [4, 7, 0, 0, (air.cols.operand_2_2 row 0), (air.cols.operand_2_3 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), [4, 7, 0, 0, (air.cols.add_value_0 row 0), (air.cols.add_value_1 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), [4, 7, 0, 0, (air.cols.add_value_2 row 0), (air.cols.add_value_3 row 0)]),
        ((air.cols.is_add row 0), [3, (((air.cols.is_add row 0) * 0) + ((air.cols.is_sub row 0) * 1)), (air.cols.add_value_0 row 0), (air.cols.add_value_1 row 0), (air.cols.add_value_2 row 0), (air.cols.add_value_3 row 0), (air.cols.operand_1_0 row 0), (air.cols.operand_1_1 row 0), (air.cols.operand_1_2 row 0), (air.cols.operand_1_3 row 0), (air.cols.operand_2_0 row 0), (air.cols.operand_2_1 row 0), (air.cols.operand_2_2 row 0), (air.cols.operand_2_3 row 0)]),
        ((air.cols.is_sub row 0), [3, (((air.cols.is_add row 0) * 0) + ((air.cols.is_sub row 0) * 1)), (air.cols.operand_1_0 row 0), (air.cols.operand_1_1 row 0), (air.cols.operand_1_2 row 0), (air.cols.operand_1_3 row 0), (air.cols.add_value_0 row 0), (air.cols.add_value_1 row 0), (air.cols.add_value_2 row 0), (air.cols.add_value_3 row 0), (air.cols.operand_2_0 row 0), (air.cols.operand_2_1 row 0), (air.cols.operand_2_2 row 0), (air.cols.operand_2_3 row 0)])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_AddSubAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_AddSubAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_AddSubAir FKB ExtF)
      (row : ℕ)
    :
      AddSubAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        AddSubAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold AddSubAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end AddSubAir.ConstraintsAndBuses

namespace AddSubAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_AddSubAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((air.cols.is_add row 0), #v[(((air.cols.is_add row 0) * 0) + ((air.cols.is_sub row 0) * 1)), (air.cols.add_value_0 row 0), (air.cols.add_value_1 row 0), (air.cols.add_value_2 row 0), (air.cols.add_value_3 row 0), (air.cols.operand_1_0 row 0), (air.cols.operand_1_1 row 0), (air.cols.operand_1_2 row 0), (air.cols.operand_1_3 row 0), (air.cols.operand_2_0 row 0), (air.cols.operand_2_1 row 0), (air.cols.operand_2_2 row 0), (air.cols.operand_2_3 row 0)]),
        ((air.cols.is_sub row 0), #v[(((air.cols.is_add row 0) * 0) + ((air.cols.is_sub row 0) * 1)), (air.cols.operand_1_0 row 0), (air.cols.operand_1_1 row 0), (air.cols.operand_1_2 row 0), (air.cols.operand_1_3 row 0), (air.cols.add_value_0 row 0), (air.cols.add_value_1 row 0), (air.cols.add_value_2 row 0), (air.cols.add_value_3 row 0), (air.cols.operand_2_0 row 0), (air.cols.operand_2_1 row 0), (air.cols.operand_2_2 row 0), (air.cols.operand_2_3 row 0)])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), #v[7, 0, 0, (air.cols.operand_1_0 row 0), (air.cols.operand_1_1 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), #v[7, 0, 0, (air.cols.operand_1_2 row 0), (air.cols.operand_1_3 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), #v[7, 0, 0, (air.cols.operand_2_0 row 0), (air.cols.operand_2_1 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), #v[7, 0, 0, (air.cols.operand_2_2 row 0), (air.cols.operand_2_3 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), #v[7, 0, 0, (air.cols.add_value_0 row 0), (air.cols.add_value_1 row 0)]),
        (-(((air.cols.is_add row 0) + (air.cols.is_sub row 0))), #v[7, 0, 0, (air.cols.add_value_2 row 0), (air.cols.add_value_3 row 0)])
      ],
      State := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_AddSubAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (AddSubAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end AddSubAir.Interactions

namespace AddSubAir.Interpretations

  open RV32IM_Interactions
  open AddSubAir.ConstraintsAndBuses
  open AddSubAir.Interactions

  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_AddSubAir FKB ExtF)
    (row : ℕ)
    (h_constraints : AddSubAir.Extraction.allHold air row)
  :
    (air.cols.is_add row 0 = 0 ∨ air.cols.is_add row 0 = 1) ∧
    (air.cols.is_sub row 0 = 0 ∨ air.cols.is_sub row 0 = 1) ∧
    (air.cols.is_add row 0 + air.cols.is_sub row 0 = 0) ∨ (air.cols.is_add row 0 + air.cols.is_sub row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

end AddSubAir.Interpretations
