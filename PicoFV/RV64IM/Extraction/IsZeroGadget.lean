--Extracted from pico commit "2acc7c1828fb4ec1bed5963511bb370870c5b608" by extractor/. Do not edit.
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace IsZeroGadget.Extraction
--Num constraints: 3
--Constraints---
@[extracted_constraint_definition] def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 3) (row := row) (rotation := 0)) * ((1 - ((Circuit.main c (column := 1) (row := row) (rotation := 0)) * (Circuit.main c (column := 0) (row := row) (rotation := 0)))) - (Circuit.main c (column := 2) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 3) (row := row) (rotation := 0)) * ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * ((Circuit.main c (column := 2) (row := row) (rotation := 0)) - 1))) = 0
@[extracted_constraint_definition] def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 3) (row := row) (rotation := 0)) * ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * (Circuit.main c (column := 0) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [])
@[constraint_and_interaction_simplification]
def constraint_list {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: List Prop :=
  [
    constraint_0 c row,
    constraint_1 c row,
    constraint_2 c row
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end IsZeroGadget.Extraction
