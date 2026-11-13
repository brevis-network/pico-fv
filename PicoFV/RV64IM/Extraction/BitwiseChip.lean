--Extracted from pico commit "2acc7c1828fb4ec1bed5963511bb370870c5b608" by extractor/. Do not edit.
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace BitwiseChip.Extraction
--Num constraints: 5
--Constraints---
@[extracted_constraint_definition] def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))) * ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 24) (row := row) (rotation := 0)) * ((Circuit.main c (column := 24) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * ((Circuit.main c (column := 25) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * ((Circuit.main c (column := 26) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))) * ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 16) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 8) (row := row) (rotation := 0)), (Circuit.main c (column := 12) (row := row) (rotation := 0))]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 17) (row := row) (rotation := 0)), 0, (((Circuit.main c (column := 0) (row := row) (rotation := 0)) - (Circuit.main c (column := 8) (row := row) (rotation := 0))) * 2122383361), (((Circuit.main c (column := 4) (row := row) (rotation := 0)) - (Circuit.main c (column := 12) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 18) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 9) (row := row) (rotation := 0)), (Circuit.main c (column := 13) (row := row) (rotation := 0))]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 19) (row := row) (rotation := 0)), 0, (((Circuit.main c (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (column := 9) (row := row) (rotation := 0))) * 2122383361), (((Circuit.main c (column := 5) (row := row) (rotation := 0)) - (Circuit.main c (column := 13) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 20) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 10) (row := row) (rotation := 0)), (Circuit.main c (column := 14) (row := row) (rotation := 0))]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 21) (row := row) (rotation := 0)), 0, (((Circuit.main c (column := 2) (row := row) (rotation := 0)) - (Circuit.main c (column := 10) (row := row) (rotation := 0))) * 2122383361), (((Circuit.main c (column := 6) (row := row) (rotation := 0)) - (Circuit.main c (column := 14) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 22) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 11) (row := row) (rotation := 0)), (Circuit.main c (column := 15) (row := row) (rotation := 0))]),
  -- Looking Byte (Regional)
  ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0))), [5, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 1)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 0)), (Circuit.main c (column := 23) (row := row) (rotation := 0)), 0, (((Circuit.main c (column := 3) (row := row) (rotation := 0)) - (Circuit.main c (column := 11) (row := row) (rotation := 0))) * 2122383361), (((Circuit.main c (column := 7) (row := row) (rotation := 0)) - (Circuit.main c (column := 15) (row := row) (rotation := 0))) * 2122383361)]),
  -- Looked Alu (Regional)
  ((0 - (((Circuit.main c (column := 24) (row := row) (rotation := 0)) + (Circuit.main c (column := 25) (row := row) (rotation := 0))) + (Circuit.main c (column := 26) (row := row) (rotation := 0)))), [4, ((((Circuit.main c (column := 24) (row := row) (rotation := 0)) * 2) + ((Circuit.main c (column := 25) (row := row) (rotation := 0)) * 3)) + ((Circuit.main c (column := 26) (row := row) (rotation := 0)) * 4)), ((Circuit.main c (column := 16) (row := row) (rotation := 0)) + ((Circuit.main c (column := 17) (row := row) (rotation := 0)) * 256)), ((Circuit.main c (column := 18) (row := row) (rotation := 0)) + ((Circuit.main c (column := 19) (row := row) (rotation := 0)) * 256)), ((Circuit.main c (column := 20) (row := row) (rotation := 0)) + ((Circuit.main c (column := 21) (row := row) (rotation := 0)) * 256)), ((Circuit.main c (column := 22) (row := row) (rotation := 0)) + ((Circuit.main c (column := 23) (row := row) (rotation := 0)) * 256)), (Circuit.main c (column := 0) (row := row) (rotation := 0)), (Circuit.main c (column := 1) (row := row) (rotation := 0)), (Circuit.main c (column := 2) (row := row) (rotation := 0)), (Circuit.main c (column := 3) (row := row) (rotation := 0)), (Circuit.main c (column := 4) (row := row) (rotation := 0)), (Circuit.main c (column := 5) (row := row) (rotation := 0)), (Circuit.main c (column := 6) (row := row) (rotation := 0)), (Circuit.main c (column := 7) (row := row) (rotation := 0))])])
@[constraint_and_interaction_simplification]
def constraint_list {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: List Prop :=
  [
    constraint_0 c row,
    constraint_1 c row,
    constraint_2 c row,
    constraint_3 c row,
    constraint_4 c row
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end BitwiseChip.Extraction
