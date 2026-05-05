--Extracted on 2026-5-4 at 11:17:56.419613331 using git commit "1d13964da22c7cf660eb6ee312c9c08ab6f76126"
import Mathlib.Data.List.Defs

import LeanZKCircuit_Plonky3.Plonky3.Circuit

import PicoFV.RV64IM.Extraction.Attributes

open Plonky3

set_option linter.all false

namespace LtChip64.Extraction
--Num constraints: 30
--Constraints---
@[extracted_constraint_definition] def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (column := 0) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 1) (row := row) (rotation := 0)) * ((Circuit.main c (column := 1) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) * (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (column := 0) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_4 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) * (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_5 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - 1) * (Circuit.main c (column := 0) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_6 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (column := 0) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_7 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 22) (row := row) (rotation := 0)) * ((Circuit.main c (column := 22) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_8 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (column := 0) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_9 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 23) (row := row) (rotation := 0)) * ((Circuit.main c (column := 23) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_10 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) - 1) * (Circuit.main c (column := 22) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_11 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) - 1) * (Circuit.main c (column := 23) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_12 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) * (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_13 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 14) (row := row) (rotation := 0)) * ((Circuit.main c (column := 14) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_14 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 15) (row := row) (rotation := 0)) * ((Circuit.main c (column := 15) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_15 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 16) (row := row) (rotation := 0)) * ((Circuit.main c (column := 16) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_16 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 17) (row := row) (rotation := 0)) * ((Circuit.main c (column := 17) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_17 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((((Circuit.main c (column := 14) (row := row) (rotation := 0)) + (Circuit.main c (column := 15) (row := row) (rotation := 0))) + (Circuit.main c (column := 16) (row := row) (rotation := 0))) + (Circuit.main c (column := 17) (row := row) (rotation := 0))) * (((((Circuit.main c (column := 14) (row := row) (rotation := 0)) + (Circuit.main c (column := 15) (row := row) (rotation := 0))) + (Circuit.main c (column := 16) (row := row) (rotation := 0))) + (Circuit.main c (column := 17) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_18 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - (0 + (Circuit.main c (column := 17) (row := row) (rotation := 0)))) * ((((Circuit.main c (column := 9) (row := row) (rotation := 0)) + ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 22) (row := row) (rotation := 0)))) - (((Circuit.main c (column := 13) (row := row) (rotation := 0)) + ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 23) (row := row) (rotation := 0)))))) = 0
@[extracted_constraint_definition] def constraint_19 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - ((0 + (Circuit.main c (column := 17) (row := row) (rotation := 0))) + (Circuit.main c (column := 16) (row := row) (rotation := 0)))) * ((Circuit.main c (column := 8) (row := row) (rotation := 0)) - (Circuit.main c (column := 12) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_20 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - (((0 + (Circuit.main c (column := 17) (row := row) (rotation := 0))) + (Circuit.main c (column := 16) (row := row) (rotation := 0))) + (Circuit.main c (column := 15) (row := row) (rotation := 0)))) * ((Circuit.main c (column := 7) (row := row) (rotation := 0)) - (Circuit.main c (column := 11) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_21 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - ((((0 + (Circuit.main c (column := 17) (row := row) (rotation := 0))) + (Circuit.main c (column := 16) (row := row) (rotation := 0))) + (Circuit.main c (column := 15) (row := row) (rotation := 0))) + (Circuit.main c (column := 14) (row := row) (rotation := 0)))) * ((Circuit.main c (column := 6) (row := row) (rotation := 0)) - (Circuit.main c (column := 10) (row := row) (rotation := 0)))) = 0
@[extracted_constraint_definition] def constraint_22 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((((0 + ((((Circuit.main c (column := 9) (row := row) (rotation := 0)) + ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 22) (row := row) (rotation := 0)))) * (Circuit.main c (column := 17) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 8) (row := row) (rotation := 0)) * (Circuit.main c (column := 16) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 7) (row := row) (rotation := 0)) * (Circuit.main c (column := 15) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 6) (row := row) (rotation := 0)) * (Circuit.main c (column := 14) (row := row) (rotation := 0)))) - (Circuit.main c (column := 19) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_23 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((((0 + ((((Circuit.main c (column := 13) (row := row) (rotation := 0)) + ((Circuit.main c (column := 0) (row := row) (rotation := 0)) * 32768)) - (65536 * (Circuit.main c (column := 23) (row := row) (rotation := 0)))) * (Circuit.main c (column := 17) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 12) (row := row) (rotation := 0)) * (Circuit.main c (column := 16) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 11) (row := row) (rotation := 0)) * (Circuit.main c (column := 15) (row := row) (rotation := 0)))) + ((Circuit.main c (column := 10) (row := row) (rotation := 0)) * (Circuit.main c (column := 14) (row := row) (rotation := 0)))) - (Circuit.main c (column := 20) (row := row) (rotation := 0))) = 0
@[extracted_constraint_definition] def constraint_24 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((1 - ((((Circuit.main c (column := 14) (row := row) (rotation := 0)) + (Circuit.main c (column := 15) (row := row) (rotation := 0))) + (Circuit.main c (column := 16) (row := row) (rotation := 0))) + (Circuit.main c (column := 17) (row := row) (rotation := 0)))) - 1) * (((Circuit.main c (column := 18) (row := row) (rotation := 0)) * ((Circuit.main c (column := 19) (row := row) (rotation := 0)) - (Circuit.main c (column := 20) (row := row) (rotation := 0)))) - ((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))))) = 0
@[extracted_constraint_definition] def constraint_25 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) * (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))) - 1)) = 0
@[extracted_constraint_definition] def constraint_26 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  ((Circuit.main c (column := 21) (row := row) (rotation := 0)) * ((Circuit.main c (column := 21) (row := row) (rotation := 0)) - 1)) = 0
@[extracted_constraint_definition] def constraint_27 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (Circuit.main c (column := 3) (row := row) (rotation := 0)) = 0
@[extracted_constraint_definition] def constraint_28 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (Circuit.main c (column := 4) (row := row) (rotation := 0)) = 0
@[extracted_constraint_definition] def constraint_29 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
  (Circuit.main c (column := 5) (row := row) (rotation := 0)) = 0
@[extracted_constraint_definition]
def constrain_interactions {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=
  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [(-((Circuit.main c (column := 0) (row := row) (rotation := 0))), [4, 8, ((2 * (Circuit.main c (column := 9) (row := row) (rotation := 0))) - ((Circuit.main c (column := 22) (row := row) (rotation := 0)) * 65536)), 0, 0, 0]),
  (-((Circuit.main c (column := 0) (row := row) (rotation := 0))), [4, 8, ((2 * (Circuit.main c (column := 13) (row := row) (rotation := 0))) - ((Circuit.main c (column := 23) (row := row) (rotation := 0)) * 65536)), 0, 0, 0]),
  (-(((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0)))), [4, 8, (((Circuit.main c (column := 19) (row := row) (rotation := 0)) - (Circuit.main c (column := 20) (row := row) (rotation := 0))) + ((Circuit.main c (column := 21) (row := row) (rotation := 0)) * 65536)), 0, 0, 0]),
  (((Circuit.main c (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (column := 1) (row := row) (rotation := 0))), [3, (((Circuit.main c (column := 0) (row := row) (rotation := 0)) * 8) + ((Circuit.main c (column := 1) (row := row) (rotation := 0)) * 9)), (Circuit.main c (column := 2) (row := row) (rotation := 0)), (Circuit.main c (column := 3) (row := row) (rotation := 0)), (Circuit.main c (column := 4) (row := row) (rotation := 0)), (Circuit.main c (column := 5) (row := row) (rotation := 0)), (Circuit.main c (column := 6) (row := row) (rotation := 0)), (Circuit.main c (column := 7) (row := row) (rotation := 0)), (Circuit.main c (column := 8) (row := row) (rotation := 0)), (Circuit.main c (column := 9) (row := row) (rotation := 0)), (Circuit.main c (column := 10) (row := row) (rotation := 0)), (Circuit.main c (column := 11) (row := row) (rotation := 0)), (Circuit.main c (column := 12) (row := row) (rotation := 0)), (Circuit.main c (column := 13) (row := row) (rotation := 0))])])
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
    constraint_23 c row,
    constraint_24 c row,
    constraint_25 c row,
    constraint_26 c row,
    constraint_27 c row,
    constraint_28 c row,
    constraint_29 c row
  ]
@[constraint_and_interaction_simplification]
def allHold {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)
: Prop :=
  constrain_interactions c ∧
  List.Forall (·) (constraint_list c row)
end LtChip64.Extraction
------
