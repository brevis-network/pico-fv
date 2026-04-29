--Extracted on 2026-4-29 at 16:53:09.603336900 using git commit "01a3f120f6b5197c41e92b7bcc2747ce1b992936"
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace ProgramChip64.Extraction
--Num constraints: 0
--Constraints---
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [((Circuit.main c (column := 0) (row := row) (rotation := 0)), [1, (Circuit.preprocessed c (column := 0) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 1) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 2) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 3) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 3) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 4) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 5) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 6) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 7) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 8) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 9) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 10) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 11) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 12) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 13) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 14) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 15) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 16) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 17) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 18) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 19) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 20) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 21) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 22) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 23) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 24) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 25) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 26) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 27) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 28) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 29) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 30) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 31) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 32) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 33) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 34) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 35) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 36) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 37) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 38) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 39) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 40) (row := row) (rotation := 0)), (Circuit.preprocessed c (column := 41) (row := row) (rotation := 0))])])
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
end ProgramChip64.Extraction
------
