--Extracted from pico commit "2acc7c1828fb4ec1bed5963511bb370870c5b608" by extractor/. Do not edit.
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace U16ToU8GadgetSafe.Extraction
--Num constraints: 0
--Constraints---
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [
  -- Looking Byte (Regional)
  ((Circuit.main c (column := 8) (row := row) (rotation := 0)), [5, 7, 0, 0, (Circuit.main c (column := 4) (row := row) (rotation := 0)), (((Circuit.main c (column := 0) (row := row) (rotation := 0)) - (Circuit.main c (column := 4) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looking Byte (Regional)
  ((Circuit.main c (column := 8) (row := row) (rotation := 0)), [5, 7, 0, 0, (Circuit.main c (column := 5) (row := row) (rotation := 0)), (((Circuit.main c (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (column := 5) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looking Byte (Regional)
  ((Circuit.main c (column := 8) (row := row) (rotation := 0)), [5, 7, 0, 0, (Circuit.main c (column := 6) (row := row) (rotation := 0)), (((Circuit.main c (column := 2) (row := row) (rotation := 0)) - (Circuit.main c (column := 6) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looking Byte (Regional)
  ((Circuit.main c (column := 8) (row := row) (rotation := 0)), [5, 7, 0, 0, (Circuit.main c (column := 7) (row := row) (rotation := 0)), (((Circuit.main c (column := 3) (row := row) (rotation := 0)) - (Circuit.main c (column := 7) (row := row) (rotation := 0))) * 2122383361)])])
@[constraint_and_interaction_simplification]
def constraint_list {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: List Prop :=
  [
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end U16ToU8GadgetSafe.Extraction
