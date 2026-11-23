--Extracted from pico commit "fcfa504624657d0c417c43f1233d5d891f293ff9" by extractor/. Do not edit.
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace CodeRangeGadget.Extraction
--Num constraints: 4
--Constraints---
@[extracted_constraint_definition] def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 7) (row := row) (rotation := 0)) * ((Circuit.main c (column := 7) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 8) (row := row) (rotation := 0)) * ((Circuit.main c (column := 8) (row := row) (rotation := 0)) - 1)) * ((Circuit.main c (column := 8) (row := row) (rotation := 0)) - 2)) = 0
@[extracted_constraint_definition] def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (column := 9) (row := row) (rotation := 0)) - ((((Circuit.main c (column := 7) (row := row) (rotation := 0)) * (((0 + (Circuit.main c (column := 3) (row := row) (rotation := 0))) - (Circuit.main c (column := 0) (row := row) (rotation := 0))) - (Circuit.main c (column := 2) (row := row) (rotation := 0)))) + ((1 - (Circuit.main c (column := 7) (row := row) (rotation := 0))) * ((Circuit.main c (column := 0) (row := row) (rotation := 0)) - (Circuit.main c (column := 5) (row := row) (rotation := 0))))) + (65536 * (Circuit.main c (column := 8) (row := row) (rotation := 0)))))) = 0
@[extracted_constraint_definition] def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (column := 10) (row := row) (rotation := 0)) - ((((Circuit.main c (column := 7) (row := row) (rotation := 0)) * ((0 + (Circuit.main c (column := 4) (row := row) (rotation := 0))) - (Circuit.main c (column := 1) (row := row) (rotation := 0)))) + ((1 - (Circuit.main c (column := 7) (row := row) (rotation := 0))) * ((Circuit.main c (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (column := 6) (row := row) (rotation := 0))))) - (Circuit.main c (column := 8) (row := row) (rotation := 0))))) = 0
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [
  -- Looking Program (Regional)
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)), [2, (Circuit.main c (column := 3) (row := row) (rotation := 0)), (Circuit.main c (column := 4) (row := row) (rotation := 0)), (Circuit.main c (column := 5) (row := row) (rotation := 0)), (Circuit.main c (column := 6) (row := row) (rotation := 0))]),
  -- Looking Byte (Regional)
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)), [5, 8, (Circuit.main c (column := 9) (row := row) (rotation := 0)), 0, 0, 0]),
  -- Looking Byte (Regional)
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)), [5, 8, (Circuit.main c (column := 10) (row := row) (rotation := 0)), 0, 0, 0])])
@[constraint_and_interaction_simplification]
def constraint_list {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: List Prop :=
  [
    constraint_0 c row,
    constraint_1 c row,
    constraint_2 c row,
    constraint_3 c row
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end CodeRangeGadget.Extraction
