--Extracted on 2026-5-11 at 15:37:26.362282512 using git commit "b6f2de04bef696f0eb7f918a494b2ac3c841d0b0"
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace BitwiseGadget.Extraction
--Num constraints: 0
--Constraints---
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [(-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 16) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 0) (row := row) (rotation := 0)), (Circuit.main c (column := 8) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 17) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 1) (row := row) (rotation := 0)), (Circuit.main c (column := 9) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 18) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 2) (row := row) (rotation := 0)), (Circuit.main c (column := 10) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 19) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 3) (row := row) (rotation := 0)), (Circuit.main c (column := 11) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 20) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 4) (row := row) (rotation := 0)), (Circuit.main c (column := 12) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 21) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 5) (row := row) (rotation := 0)), (Circuit.main c (column := 13) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 22) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 6) (row := row) (rotation := 0)), (Circuit.main c (column := 14) (row := row) (rotation := 0))]),
  (-((Circuit.main c (column := 25) (row := row) (rotation := 0))), [4, (Circuit.main c (column := 24) (row := row) (rotation := 0)), (Circuit.main c (column := 23) (row := row) (rotation := 0)), 0, (Circuit.main c (column := 7) (row := row) (rotation := 0)), (Circuit.main c (column := 15) (row := row) (rotation := 0))])])
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
end BitwiseGadget.Extraction
------
