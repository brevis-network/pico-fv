--Extracted on 2026-5-11 at 15:37:07.504631720 using git commit "22b0aae6321c1f63c72aafd0b506b5f45b91ffb1"
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace SubwChip.Extraction
--Num constraints: 6
--Constraints---
@[extracted_constraint_definition] def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (column := 11) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((((((((Circuit.main c (column := 3) (row := row) (rotation := 0)) + 65536) - 1) - (Circuit.main c (column := 7) (row := row) (rotation := 0))) - (Circuit.main c (column := 0) (row := row) (rotation := 0))) + 1) * 2130673921) * ((((((((Circuit.main c (column := 3) (row := row) (rotation := 0)) + 65536) - 1) - (Circuit.main c (column := 7) (row := row) (rotation := 0))) - (Circuit.main c (column := 0) (row := row) (rotation := 0))) + 1) * 2130673921) - 1))) = 0
@[extracted_constraint_definition] def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((((((((Circuit.main c (column := 4) (row := row) (rotation := 0)) + 65536) - 1) - (Circuit.main c (column := 8) (row := row) (rotation := 0))) - (Circuit.main c (column := 1) (row := row) (rotation := 0))) + (((((((Circuit.main c (column := 3) (row := row) (rotation := 0)) + 65536) - 1) - (Circuit.main c (column := 7) (row := row) (rotation := 0))) - (Circuit.main c (column := 0) (row := row) (rotation := 0))) + 1) * 2130673921)) * 2130673921) * ((((((((Circuit.main c (column := 4) (row := row) (rotation := 0)) + 65536) - 1) - (Circuit.main c (column := 8) (row := row) (rotation := 0))) - (Circuit.main c (column := 1) (row := row) (rotation := 0))) + (((((((Circuit.main c (column := 3) (row := row) (rotation := 0)) + 65536) - 1) - (Circuit.main c (column := 7) (row := row) (rotation := 0))) - (Circuit.main c (column := 0) (row := row) (rotation := 0))) + 1) * 2130673921)) * 2130673921) - 1))) = 0
@[extracted_constraint_definition] def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (column := 11) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * ((Circuit.main c (column := 2) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (column := 11) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [(-((Circuit.main c (column := 11) (row := row) (rotation := 0))), [4, 8, (Circuit.main c (column := 0) (row := row) (rotation := 0)), 0, 0, 0]),
  (-((Circuit.main c (column := 11) (row := row) (rotation := 0))), [4, 8, (Circuit.main c (column := 1) (row := row) (rotation := 0)), 0, 0, 0]),
  (-((Circuit.main c (column := 11) (row := row) (rotation := 0))), [4, 8, ((2 * (Circuit.main c (column := 1) (row := row) (rotation := 0))) - ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * 65536)), 0, 0, 0]),
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)), [3, 41, (Circuit.main c (column := 0) (row := row) (rotation := 0)), (Circuit.main c (column := 1) (row := row) (rotation := 0)), ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * 65535), ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * 65535), (Circuit.main c (column := 3) (row := row) (rotation := 0)), (Circuit.main c (column := 4) (row := row) (rotation := 0)), (Circuit.main c (column := 5) (row := row) (rotation := 0)), (Circuit.main c (column := 6) (row := row) (rotation := 0)), (Circuit.main c (column := 7) (row := row) (rotation := 0)), (Circuit.main c (column := 8) (row := row) (rotation := 0)), (Circuit.main c (column := 9) (row := row) (rotation := 0)), (Circuit.main c (column := 10) (row := row) (rotation := 0))])])
@[constraint_and_interaction_simplification]
def constraint_list {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: List Prop :=
  [
    constraint_0 c row,
    constraint_1 c row,
    constraint_2 c row,
    constraint_3 c row,
    constraint_4 c row,
    constraint_5 c row
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end SubwChip.Extraction
------
