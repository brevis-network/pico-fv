--Extracted on 2026-5-11 at 15:37:39.548660888 using git commit "0786b8baab6b5f2f32744be1dfc77458fc21a8f2"
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace LtSignedGadget.Extraction
--Num constraints: 24
--Constraints---
@[extracted_constraint_definition] def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * ((Circuit.main c (column := 18) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 19) (row := row) (rotation := 0)) * ((Circuit.main c (column := 19) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 19) (row := row) (rotation := 0)) - 1) * (Circuit.main c (column := 18) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * ((Circuit.main c (column := 18) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 16) (row := row) (rotation := 0)) * ((Circuit.main c (column := 16) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * ((Circuit.main c (column := 18) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 17) (row := row) (rotation := 0)) * ((Circuit.main c (column := 17) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 18) (row := row) (rotation := 0)) - 1) * (Circuit.main c (column := 16) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 18) (row := row) (rotation := 0)) - 1) * (Circuit.main c (column := 17) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 19) (row := row) (rotation := 0)) * ((Circuit.main c (column := 19) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 8) (row := row) (rotation := 0)) * ((Circuit.main c (column := 8) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 9) (row := row) (rotation := 0)) * ((Circuit.main c (column := 9) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 10) (row := row) (rotation := 0)) * ((Circuit.main c (column := 10) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * ((Circuit.main c (column := 11) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((((Circuit.main c (column := 8) (row := row) (rotation := 0)) + (Circuit.main c (column := 9) (row := row) (rotation := 0))) + (Circuit.main c (column := 10) (row := row) (rotation := 0))) + (Circuit.main c (column := 11) (row := row) (rotation := 0))) * (((((Circuit.main c (column := 8) (row := row) (rotation := 0)) + (Circuit.main c (column := 9) (row := row) (rotation := 0))) + (Circuit.main c (column := 10) (row := row) (rotation := 0))) + (Circuit.main c (column := 11) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 19) (row := row) (rotation := 0)) - (0 + (Circuit.main c (column := 11) (row := row) (rotation := 0)))) * ((((Circuit.main c (column := 3) (row := row) (rotation := 0)) + ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 16) (row := row) (rotation := 0)))) - (((Circuit.main c (column := 7) (row := row) (rotation := 0)) + ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 17) (row := row) (rotation := 0)))))) = 0
@[extracted_constraint_definition] def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 19) (row := row) (rotation := 0)) - ((0 + (Circuit.main c (column := 11) (row := row) (rotation := 0))) + (Circuit.main c (column := 10) (row := row) (rotation := 0)))) * ((Circuit.main c (column := 2) (row := row) (rotation := 0)) - (Circuit.main c (column := 6) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 19) (row := row) (rotation := 0)) - (((0 + (Circuit.main c (column := 11) (row := row) (rotation := 0))) + (Circuit.main c (column := 10) (row := row) (rotation := 0))) + (Circuit.main c (column := 9) (row := row) (rotation := 0)))) * ((Circuit.main c (column := 1) (row := row) (rotation := 0)) - (Circuit.main c (column := 5) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 19) (row := row) (rotation := 0)) - ((((0 + (Circuit.main c (column := 11) (row := row) (rotation := 0))) + (Circuit.main c (column := 10) (row := row) (rotation := 0))) + (Circuit.main c (column := 9) (row := row) (rotation := 0))) + (Circuit.main c (column := 8) (row := row) (rotation := 0)))) * ((Circuit.main c (column := 0) (row := row) (rotation := 0)) - (Circuit.main c (column := 4) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((((0 + ((((Circuit.main c (column := 3) (row := row) (rotation := 0)) + ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 16) (row := row) (rotation := 0)))) * (Circuit.main c (column := 11) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 2) (row := row) (rotation := 0)) * (Circuit.main c (column := 10) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 1) (row := row) (rotation := 0)) * (Circuit.main c (column := 9) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * (Circuit.main c (column := 8) (row := row) (rotation := 0)))) - (Circuit.main c (column := 13) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((((0 + ((((Circuit.main c (column := 7) (row := row) (rotation := 0)) + ((Circuit.main c (column := 18) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 17) (row := row) (rotation := 0)))) * (Circuit.main c (column := 11) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 6) (row := row) (rotation := 0)) * (Circuit.main c (column := 10) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 5) (row := row) (rotation := 0)) * (Circuit.main c (column := 9) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 4) (row := row) (rotation := 0)) * (Circuit.main c (column := 8) (row := row) (rotation := 0)))) - (Circuit.main c (column := 14) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((1 - ((((Circuit.main c (column := 8) (row := row) (rotation := 0)) + (Circuit.main c (column := 9) (row := row) (rotation := 0))) + (Circuit.main c (column := 10) (row := row) (rotation := 0))) + (Circuit.main c (column := 11) (row := row) (rotation := 0)))) - 1) * (((Circuit.main c (column := 12) (row := row) (rotation := 0)) * ((Circuit.main c (column := 13) (row := row) (rotation := 0)) - (Circuit.main c (column := 14) (row := row) (rotation := 0)))) - (Circuit.main c (column := 19) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_22 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 19) (row := row) (rotation := 0)) * ((Circuit.main c (column := 19) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_23 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 15) (row := row) (rotation := 0)) * ((Circuit.main c (column := 15) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [(-((Circuit.main c (column := 18) (row := row) (rotation := 0))), [4, 8, ((2 * (Circuit.main c (column := 3) (row := row) (rotation := 0))) - ((Circuit.main c (column := 16) (row := row) (rotation := 0)) * 65536)), 0, 0, 0]),
  (-((Circuit.main c (column := 18) (row := row) (rotation := 0))), [4, 8, ((2 * (Circuit.main c (column := 7) (row := row) (rotation := 0))) - ((Circuit.main c (column := 17) (row := row) (rotation := 0)) * 65536)), 0, 0, 0]),
  (-((Circuit.main c (column := 19) (row := row) (rotation := 0))), [4, 8, (((Circuit.main c (column := 13) (row := row) (rotation := 0)) - (Circuit.main c (column := 14) (row := row) (rotation := 0))) + ((Circuit.main c (column := 15) (row := row) (rotation := 0)) * 65536)), 0, 0, 0])])
@[constraint_and_interaction_simplification]
def constraint_list {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: List Prop :=
  [
    constraint_0 c row,
    constraint_1 c row,
    constraint_2 c row,
    constraint_3 c row,
    constraint_4 c row,
    constraint_5 c row,
    constraint_6 c row,
    constraint_7 c row,
    constraint_8 c row,
    constraint_9 c row,
    constraint_10 c row,
    constraint_11 c row,
    constraint_12 c row,
    constraint_13 c row,
    constraint_14 c row,
    constraint_15 c row,
    constraint_16 c row,
    constraint_17 c row,
    constraint_18 c row,
    constraint_19 c row,
    constraint_20 c row,
    constraint_21 c row,
    constraint_22 c row,
    constraint_23 c row
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end LtSignedGadget.Extraction
------
