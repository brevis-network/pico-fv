import PicoFV.RVSail.RV32IM.Operations
import PicoFV.Extraction.BitwiseAir
import PicoFV.Airs.BitwiseAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace BitwiseAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_BitwiseAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_xor row 0) * ((air.cols.is_xor row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_BitwiseAir F ExtF) (row : ℕ)
      : BitwiseAir.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_BitwiseAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_or row 0) * ((air.cols.is_or row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_BitwiseAir F ExtF) (row : ℕ)
      : BitwiseAir.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_BitwiseAir F ExtF) (row : ℕ) : Prop :=
        ((air.cols.is_and row 0) * ((air.cols.is_and row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_BitwiseAir F ExtF) (row : ℕ)
      : BitwiseAir.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_BitwiseAir F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0)) * ((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0)) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_BitwiseAir F ExtF) (row : ℕ)
      : BitwiseAir.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_BitwiseAir F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row
        ]

    end row_constraints

    section row_buses

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_BitwiseAir FKB ExtF) (row : ℕ) : List (FKB × List FKB) := [(-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), [4, ((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_0 row 0), 0, (air.cols.b_0 row 0), (air.cols.c_0 row 0)]),
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), [4, ((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_1 row 0), 0, (air.cols.b_1 row 0), (air.cols.c_1 row 0)]),
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), [4, ((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_2 row 0), 0, (air.cols.b_2 row 0), (air.cols.c_2 row 0)]),
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), [4, ((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_3 row 0), 0, (air.cols.b_3 row 0), (air.cols.c_3 row 0)]),
        ((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0)), [3, ((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 3)) + ((air.cols.is_and row 0) * 4)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_BitwiseAir FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_BitwiseAir FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_BitwiseAir FKB ExtF)
      (row : ℕ)
    :
      BitwiseAir.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row) ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        BitwiseAir.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold BitwiseAir.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end BitwiseAir.ConstraintsAndBuses

namespace BitwiseAir.Interactions

  open RV32IM_Interactions

  def bus_row (air : Valid_BitwiseAir FKB ExtF) (row : ℕ) : BusRow :=
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0)), #v[((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 3)) + ((air.cols.is_and row 0) * 4)), (air.cols.a_0 row 0), (air.cols.a_1 row 0), (air.cols.a_2 row 0), (air.cols.a_3 row 0), (air.cols.b_0 row 0), (air.cols.b_1 row 0), (air.cols.b_2 row 0), (air.cols.b_3 row 0), (air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), #v[((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_0 row 0), 0, (air.cols.b_0 row 0), (air.cols.c_0 row 0)]),
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), #v[((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_1 row 0), 0, (air.cols.b_1 row 0), (air.cols.c_1 row 0)]),
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), #v[((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_2 row 0), 0, (air.cols.b_2 row 0), (air.cols.c_2 row 0)]),
        (-((((air.cols.is_xor row 0) + (air.cols.is_or row 0)) + (air.cols.is_and row 0))), #v[((((air.cols.is_xor row 0) * 2) + ((air.cols.is_or row 0) * 1)) + ((air.cols.is_and row 0) * 0)), (air.cols.a_3 row 0), 0, (air.cols.b_3 row 0), (air.cols.c_3 row 0)])
      ],
      State := []
    }

  @[simp]
  lemma bus_row_equiv (air : Valid_BitwiseAir FKB ExtF) (row : ℕ) :
    RV32IM_Interactions.deserialise_bus_row (BitwiseAir.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      pico_encapsulation,
    ]

end BitwiseAir.Interactions
