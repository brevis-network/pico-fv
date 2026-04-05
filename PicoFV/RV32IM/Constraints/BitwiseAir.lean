import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.Extraction.BitwiseAir
import PicoFV.RV32IM.Airs.BitwiseAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace BitwiseAir.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- ==========================================================================
      -- Constraints 0-2: is_xor, is_or, is_and are each boolean (x * (x - 1) = 0).
      -- Constraint 3: is_real = is_xor + is_or + is_and is boolean,
      -- ensuring at most one selector is active per row.
      -- ==========================================================================

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

      -- ===========================================
      -- Collected constraint list for a single row.
      -- ===========================================

      @[simp]
      def row_constraint_list (air : Valid_BitwiseAir F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row
        ]

    end row_constraints

    /-- All 15 column values of a BitwiseAir row. -/
    def row (air : Valid_BitwiseAir FKB ExtF) (r : ℕ) : Vector FKB 15 :=
      #v[ air.cols.a_0 r 0, air.cols.a_1 r 0, air.cols.a_2 r 0, air.cols.a_3 r 0,
          air.cols.b_0 r 0, air.cols.b_1 r 0, air.cols.b_2 r 0, air.cols.b_3 r 0,
          air.cols.c_0 r 0, air.cols.c_1 r 0, air.cols.c_2 r 0, air.cols.c_3 r 0,
          air.cols.is_xor r 0, air.cols.is_or r 0, air.cols.is_and r 0 ]

    section row_buses

      -- =============================================================================
      -- Bus interactions:
      -- 4 ByteBus entries (one per byte of a, b, c), with opcode = is_xor*2 + is_or*1
      --   encoding the bitwise operation for byte-level lookup.
      -- 1 ALU entry with opcode = is_xor*2 + is_or*3 + is_and*4,
      --   carrying the full 4-byte words a, b, c.
      -- =============================================================================

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
      State := [],
      Memory := []
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

-- ==========================================================
-- Interpretation lemmas: selector breakdown.
-- ==========================================================

namespace BitwiseAir.Interpretations

  open BitwiseAir.ConstraintsAndBuses
  open BitwiseAir.Interactions

  /-- Each selector is binary and their sum is 0 or 1. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_BitwiseAir FKB ExtF)
    (row : ℕ)
    (h_constraints : BitwiseAir.Extraction.allHold air row)
  :
    (air.cols.is_xor row 0 = 0 ∨ air.cols.is_xor row 0 = 1) ∧
    (air.cols.is_or row 0 = 0 ∨ air.cols.is_or row 0 = 1) ∧
    (air.cols.is_and row 0 = 0 ∨ air.cols.is_and row 0 = 1) ∧
    ((air.cols.is_xor row 0 + air.cols.is_or row 0) + air.cols.is_and row 0 = 0 ∨
     (air.cols.is_xor row 0 + air.cols.is_or row 0) + air.cols.is_and row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

end BitwiseAir.Interpretations
