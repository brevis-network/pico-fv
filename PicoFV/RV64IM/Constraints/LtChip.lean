import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.LtChip
import PicoFV.RV64IM.Airs.LtChip
import PicoFV.RV64IM.Constraints.LtSignedGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# LtChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and
the list of bus interactions emitted by `LtChip::eval`
(`vm/src/chips/chips/alu/lt/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_LtChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.LtChip`.

The chip layout (matching `LtValueCols<F>`) is:

| Cols   | Field path (under `air.cols.values`)                      |
|--------|-----------------------------------------------------------|
| 0      | `is_slt`                                                  |
| 1      | `is_slt_u`                                                |
| 2..5   | `a_0..a_3` (result word — only `a_0` is the bit)          |
| 6..9   | `b_0..b_3` (first operand)                                |
| 10..13 | `c_0..c_3` (second operand)                               |
| 14..17 | `lt_signed.result.u16_flags_0..3`                         |
| 18     | `lt_signed.result.not_eq_inv`                             |
| 19     | `lt_signed.result.comparison_limbs_0`                     |
| 20     | `lt_signed.result.comparison_limbs_1`                     |
| 21     | `lt_signed.result.bit`                                    |
| 22     | `lt_signed.b_msb.msb`                                     |
| 23     | `lt_signed.c_msb.msb`                                     |

The chip dispatches `LtSignedGadget` with `is_signed = is_slt` and
`is_real = is_slt + is_slt_u`, with the gadget's `a` = chip's `b` and
gadget's `b` = chip's `c`. The chip's own substantive constraints are
`a_1 = a_2 = a_3 = 0` and `(is_slt + is_slt_u) * (a_0 - bit) = 0`,
plus chip-level booleans on `is_slt`, `is_slt_u`, and their sum.

The bus interactions are 3 byte entries (from the gadget) plus one ALU
entry (opcode 3, sub-op `is_slt*8 + is_slt_u*9` ∈ {8 (SLT), 9 (SLTU)}).
-/

namespace LtChip

  open RV64IM_Interactions

  /-- The bus entries the chip contributes per row, packaged as a typed
      `BusRow`. Built compositionally from `LtSignedGadget.AbsBuses`
      (the 3 byte-bus entries: the two `U16MSBGadget` consistency
      checks on `b_3`/`c_3`, plus the `LtWordU16Gadget` Δ + bit·65536
      comparison entry) concatenated with the chip-specific `ALUBus`
      entry for SLT/SLTU. -/
  def AbsBuses
    (is_slt is_slt_u
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     comparison_limbs_0 comparison_limbs_1
     bit
     b_msb c_msb : FKB)
  : BusRow :=
    LtSignedGadget.AbsBuses (is_slt + is_slt_u) is_slt b_3 c_3
      comparison_limbs_0 comparison_limbs_1 bit b_msb c_msb
    ++
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (is_slt + is_slt_u,
          #v[ is_slt * 8 + is_slt_u * 9,
              a_0, a_1, a_2, a_3,
              b_0, b_1, b_2, b_3,
              c_0, c_1, c_2, c_3 ])
      ],
      Byte := [],
      State := [],
      Memory := []
    } : BusRow)

end LtChip

namespace LtChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_slt is boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_slt row 0) * ((air.cols.values.is_slt row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 1: is_slt_u is boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_slt_u row 0) * ((air.cols.values.is_slt_u row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 2: is_real = is_slt + is_slt_u is boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) *
          (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 3: is_slt boolean (duplicate from LtSignedGadget's
      -- `(is_real - 1) * is_signed = 0` flattened with the booleans
      -- emitted by the inner gadgets — Pico re-emits is_slt boolean).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_slt row 0) * ((air.cols.values.is_slt row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 4: is_real = is_slt + is_slt_u boolean (duplicate of 2).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) *
          (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 5: `(is_real - 1) * is_signed = 0`
      -- (LtSignedGadget's own constraint: signed compares are only real rows).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) - 1) *
          (air.cols.values.is_slt row 0)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 6: is_slt boolean (duplicate — U16MSBGadget's
      -- `is_real * (is_real - 1) = 0` with is_real = is_signed = is_slt).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_slt row 0) * ((air.cols.values.is_slt row 0) - 1)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 7: b_msb is boolean (from first U16MSBGadget).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.b_msb.msb row 0) * ((air.cols.values.lt_signed.b_msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 8: is_slt boolean (duplicate — second U16MSBGadget's
      -- own `is_real * (is_real - 1) = 0`).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_slt row 0) * ((air.cols.values.is_slt row 0) - 1)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 9: c_msb is boolean (from second U16MSBGadget).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.c_msb.msb row 0) * ((air.cols.values.lt_signed.c_msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 10: `(is_signed - 1) * b_msb = 0`
      -- (LtSignedGadget's own: unsigned compares zero out b_msb).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) - 1) * (air.cols.values.lt_signed.b_msb.msb row 0)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 11: `(is_signed - 1) * c_msb = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) - 1) * (air.cols.values.lt_signed.c_msb.msb row 0)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 12: is_real = is_slt + is_slt_u boolean (duplicate from
      -- LtWordU16Gadget's first `is_real * (is_real - 1) = 0`).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) *
          (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 13..16: `u16_flags_i ∈ {0, 1}` for i = 0..3.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.result.u16_flags_0 row 0) *
          ((air.cols.values.lt_signed.result.u16_flags_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.result.u16_flags_1 row 0) *
          ((air.cols.values.lt_signed.result.u16_flags_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.result.u16_flags_2 row 0) *
          ((air.cols.values.lt_signed.result.u16_flags_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.result.u16_flags_3 row 0) *
          ((air.cols.values.lt_signed.result.u16_flags_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 17: `(Σ u16_flags) ∈ {0, 1}` — one-hot.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((((air.cols.values.lt_signed.result.u16_flags_0 row 0) +
              (air.cols.values.lt_signed.result.u16_flags_1 row 0)) +
             (air.cols.values.lt_signed.result.u16_flags_2 row 0)) +
            (air.cols.values.lt_signed.result.u16_flags_3 row 0)) *
          ((((air.cols.values.lt_signed.result.u16_flags_0 row 0) +
              (air.cols.values.lt_signed.result.u16_flags_1 row 0)) +
             (air.cols.values.lt_signed.result.u16_flags_2 row 0)) +
            (air.cols.values.lt_signed.result.u16_flags_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 18: limb-3 MSDL check:
      --   `(is_real - u16_flags_3) * (shifted_b_3 - shifted_c_3) = 0`
      -- where `shifted_x_3 = x_3 + is_slt*32768 - 65536*x_msb`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) -
            (0 + (air.cols.values.lt_signed.result.u16_flags_3 row 0))) *
          ((((air.cols.values.b_3 row 0) + ((air.cols.values.is_slt row 0) * 32768)) -
            (65536 * (air.cols.values.lt_signed.b_msb.msb row 0))) -
           (((air.cols.values.c_3 row 0) + ((air.cols.values.is_slt row 0) * 32768)) -
            (65536 * (air.cols.values.lt_signed.c_msb.msb row 0))))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 19: limb-2 MSDL check
      --   `(is_real - (u16_flags_3 + u16_flags_2)) * (b_2 - c_2) = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) -
            ((0 + (air.cols.values.lt_signed.result.u16_flags_3 row 0)) +
             (air.cols.values.lt_signed.result.u16_flags_2 row 0))) *
          ((air.cols.values.b_2 row 0) - (air.cols.values.c_2 row 0))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 20: limb-1 MSDL check
      --   `(is_real - (u16_flags_3 + u16_flags_2 + u16_flags_1)) * (b_1 - c_1) = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) -
            (((0 + (air.cols.values.lt_signed.result.u16_flags_3 row 0)) +
              (air.cols.values.lt_signed.result.u16_flags_2 row 0)) +
             (air.cols.values.lt_signed.result.u16_flags_1 row 0))) *
          ((air.cols.values.b_1 row 0) - (air.cols.values.c_1 row 0))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 21: limb-0 MSDL check
      --   `(is_real - Σ u16_flags) * (b_0 - c_0) = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) -
            ((((0 + (air.cols.values.lt_signed.result.u16_flags_3 row 0)) +
               (air.cols.values.lt_signed.result.u16_flags_2 row 0)) +
              (air.cols.values.lt_signed.result.u16_flags_1 row 0)) +
             (air.cols.values.lt_signed.result.u16_flags_0 row 0))) *
          ((air.cols.values.b_0 row 0) - (air.cols.values.c_0 row 0))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 22: `comparison_limbs_0 = Σ shifted_b_i · u16_flags_i`
      -- (with shifted_b_3 = b_3 + is_slt*32768 - 65536*b_msb, others = b_i).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((((0 +
              ((((air.cols.values.b_3 row 0) + ((air.cols.values.is_slt row 0) * 32768)) -
                 (65536 * (air.cols.values.lt_signed.b_msb.msb row 0))) *
                (air.cols.values.lt_signed.result.u16_flags_3 row 0))) +
             ((air.cols.values.b_2 row 0) * (air.cols.values.lt_signed.result.u16_flags_2 row 0))) +
            ((air.cols.values.b_1 row 0) * (air.cols.values.lt_signed.result.u16_flags_1 row 0))) +
           ((air.cols.values.b_0 row 0) * (air.cols.values.lt_signed.result.u16_flags_0 row 0))) -
          (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 23: `comparison_limbs_1 = Σ shifted_c_i · u16_flags_i`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((((0 +
              ((((air.cols.values.c_3 row 0) + ((air.cols.values.is_slt row 0) * 32768)) -
                 (65536 * (air.cols.values.lt_signed.c_msb.msb row 0))) *
                (air.cols.values.lt_signed.result.u16_flags_3 row 0))) +
             ((air.cols.values.c_2 row 0) * (air.cols.values.lt_signed.result.u16_flags_2 row 0))) +
            ((air.cols.values.c_1 row 0) * (air.cols.values.lt_signed.result.u16_flags_1 row 0))) +
           ((air.cols.values.c_0 row 0) * (air.cols.values.lt_signed.result.u16_flags_0 row 0))) -
          (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 24: differing-limb inverse witness
      --   `(1 - Σ u16_flags - 1) * (not_eq_inv * (comp_0 - comp_1) - is_real) = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((1 -
            ((((air.cols.values.lt_signed.result.u16_flags_0 row 0) +
                (air.cols.values.lt_signed.result.u16_flags_1 row 0)) +
               (air.cols.values.lt_signed.result.u16_flags_2 row 0)) +
              (air.cols.values.lt_signed.result.u16_flags_3 row 0))) - 1) *
          (((air.cols.values.lt_signed.result.not_eq_inv row 0) *
              ((air.cols.values.lt_signed.result.comparison_limbs_0 row 0) -
               (air.cols.values.lt_signed.result.comparison_limbs_1 row 0))) -
            ((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 25: is_real = is_slt + is_slt_u boolean (duplicate from
      -- LtWordU16Gadget's second `is_real * (is_real - 1) = 0`).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) *
          (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) - 1)) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 26: bit ∈ {0, 1} (from LtWordU16Gadget).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.lt_signed.result.bit row 0) *
          ((air.cols.values.lt_signed.result.bit row 0) - 1)) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 27: `a_1 = 0` (chip's own — only `a_0` is the bit).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (air.cols.values.a_1 row 0) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 28: `a_2 = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (air.cols.values.a_2 row 0) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 29: `a_3 = 0`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (air.cols.values.a_3 row 0) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 30: `(is_slt + is_slt_u) * (a_0 - bit) = 0` — when
      -- `is_real = 1`, `a_0` equals the gadget's compare bit.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_LtChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)) *
          ((air.cols.values.a_0 row 0) - (air.cols.values.lt_signed.result.bit row 0))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_LtChip F ExtF) (row : ℕ)
      : LtChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 31 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_LtChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row, constraint_1 air row, constraint_2 air row,
          constraint_3 air row, constraint_4 air row, constraint_5 air row,
          constraint_6 air row, constraint_7 air row, constraint_8 air row,
          constraint_9 air row, constraint_10 air row, constraint_11 air row,
          constraint_12 air row, constraint_13 air row, constraint_14 air row,
          constraint_15 air row, constraint_16 air row, constraint_17 air row,
          constraint_18 air row, constraint_19 air row, constraint_20 air row,
          constraint_21 air row, constraint_22 air row, constraint_23 air row,
          constraint_24 air row, constraint_25 air row, constraint_26 air row,
          constraint_27 air row, constraint_28 air row, constraint_29 air row,
          constraint_30 air row
        ]

    end row_constraints

    section row_buses

      -- =====================================================================
      -- Bus interactions emitted by `LtChip::eval` (per row):
      -- 2 ByteBus entries (opcode 4, sub-op 8): U16Range on the two
      --   shifted top limbs `2*b_3 - b_msb*65536` and `2*c_3 - c_msb*65536`,
      --   gated by `-is_slt` (U16MSBGadget #1 and #2 emit these).
      -- 1 ByteBus entry: the comparison entry from LtWordU16Gadget,
      --   `(comp_0 - comp_1) + bit*65536`, gated by `-(is_slt + is_slt_u)`.
      -- 1 ALU entry (opcode 3, sub-op `is_slt*8 + is_slt_u*9` ∈ {8, 9}):
      --   carries `(a_0..3, b_0..3, c_0..3)`, gated by `+(is_slt + is_slt_u)`.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_LtChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ (-(air.cols.values.is_slt row 0),
            [4, 8,
              2 * (air.cols.values.b_3 row 0)
                - (air.cols.values.lt_signed.b_msb.msb row 0) * 65536,
              0, 0, 0]),
          (-(air.cols.values.is_slt row 0),
            [4, 8,
              2 * (air.cols.values.c_3 row 0)
                - (air.cols.values.lt_signed.c_msb.msb row 0) * 65536,
              0, 0, 0]),
          (-((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)),
            [4, 8,
              ((air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
                - (air.cols.values.lt_signed.result.comparison_limbs_1 row 0))
                + (air.cols.values.lt_signed.result.bit row 0) * 65536,
              0, 0, 0]),
          (((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0)),
            [3,
              (air.cols.values.is_slt row 0) * 8
                + (air.cols.values.is_slt_u row 0) * 9,
              (air.cols.values.a_0 row 0),
              (air.cols.values.a_1 row 0),
              (air.cols.values.a_2 row 0),
              (air.cols.values.a_3 row 0),
              (air.cols.values.b_0 row 0),
              (air.cols.values.b_1 row 0),
              (air.cols.values.b_2 row 0),
              (air.cols.values.b_3 row 0),
              (air.cols.values.c_0 row 0),
              (air.cols.values.c_1 row 0),
              (air.cols.values.c_2 row 0),
              (air.cols.values.c_3 row 0)]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_LtChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    -- =====================================================================
    -- Identification: constraints 3..26 conjoin to
    -- `LtSignedGadget.AbsConstraints` instantiated at the chip's accessors
    -- with `is_real ↦ is_slt + is_slt_u`, `is_signed ↦ is_slt`,
    -- `a_i ↦ b_i`, `b_i ↦ c_i`, and the gadget's bit/flags/limbs taken from
    -- `lt_signed.result.*` / `lt_signed.b_msb.msb` / `lt_signed.c_msb.msb`.
    -- Constraints 0..2 (chip-level booleans on `is_slt`, `is_slt_u`,
    -- their sum) and 27..30 (chip's own substantive: `a_1=a_2=a_3=0`,
    -- `a_0 = bit`) are chip-specific.
    -- =====================================================================

    omit [Field ExtF] in
    @[simp]
    lemma constraint_subset_iff_gadget
      (air : Valid_LtChip F ExtF) (row : ℕ)
    : (constraint_3 air row ∧ constraint_4 air row ∧ constraint_5 air row
        ∧ constraint_6 air row ∧ constraint_7 air row ∧ constraint_8 air row
        ∧ constraint_9 air row ∧ constraint_10 air row ∧ constraint_11 air row
        ∧ constraint_12 air row ∧ constraint_13 air row ∧ constraint_14 air row
        ∧ constraint_15 air row ∧ constraint_16 air row ∧ constraint_17 air row
        ∧ constraint_18 air row ∧ constraint_19 air row ∧ constraint_20 air row
        ∧ constraint_21 air row ∧ constraint_22 air row ∧ constraint_23 air row
        ∧ constraint_24 air row ∧ constraint_25 air row ∧ constraint_26 air row)
      ↔
      LtSignedGadget.AbsConstraints
        ((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0))
        (air.cols.values.is_slt row 0)
        (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
        (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
        (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
        (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
        (air.cols.values.lt_signed.result.u16_flags_0 row 0)
        (air.cols.values.lt_signed.result.u16_flags_1 row 0)
        (air.cols.values.lt_signed.result.u16_flags_2 row 0)
        (air.cols.values.lt_signed.result.u16_flags_3 row 0)
        (air.cols.values.lt_signed.result.not_eq_inv row 0)
        (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
        (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)
        (air.cols.values.lt_signed.result.bit row 0)
        (air.cols.values.lt_signed.b_msb.msb row 0)
        (air.cols.values.lt_signed.c_msb.msb row 0)
    := by
      simp [
        LtSignedGadget.AbsConstraints,
        U16MSBGadget.AbsConstraints,
        LtWordU16Gadget.AbsConstraints,
        constraint_and_interaction_simplification
      ]
      aesop

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_LtChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_LtChip FKB ExtF)
      (row : ℕ)
    :
      LtChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

end LtChip.ConstraintsAndBuses

namespace LtChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `LtChip` row. Defined directly as
      `LtChip.AbsBuses` applied to the chip's accessors, making
      `bus_row_abs` definitionally true. -/
  def bus_row (air : Valid_LtChip FKB ExtF) (row : ℕ) : BusRow :=
    LtChip.AbsBuses
      (air.cols.values.is_slt row 0)
      (air.cols.values.is_slt_u row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)
      (air.cols.values.lt_signed.result.bit row 0)
      (air.cols.values.lt_signed.b_msb.msb row 0)
      (air.cols.values.lt_signed.c_msb.msb row 0)

  @[simp]
  lemma bus_row_equiv (air : Valid_LtChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (LtChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    dsimp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      LtChip.AbsBuses,
      LtSignedGadget.AbsBuses,
      U16MSBGadget.AbsBuses,
      LtWordU16Gadget.AbsBuses,
      pico_encapsulation,
    ]

end LtChip.Interactions

namespace LtChip.Interpretations

  open RV64IM_Interactions
  open LtChip.ConstraintsAndBuses
  open LtChip.Interactions

  -- =======================================================================
  -- Interpretation lemmas: derive semantic properties from raw constraints.
  -- =======================================================================

  /-- Each selector is binary, and their sum `is_real` is 0 or 1. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_constraints : LtChip.Extraction.allHold air row)
  :
    (air.cols.values.is_slt row 0 = 0 ∨ air.cols.values.is_slt row 0 = 1) ∧
    (air.cols.values.is_slt_u row 0 = 0 ∨ air.cols.values.is_slt_u row 0 = 1) ∧
    (air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 0 ∨
     air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1)
  := by
    -- Only the chip-level booleans constraints 0, 1, 2 are needed.
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    obtain ⟨_, h0, h1, h2, _⟩ := h_constraints
    clear *- h0 h1 h2
    grind

  /-- At most one selector is active. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_constraints : LtChip.Extraction.allHold air row)
  :
    (air.cols.values.is_slt row 0 = 1 → air.cols.values.is_slt_u row 0 = 0) ∧
    (air.cols.values.is_slt_u row 0 = 1 → air.cols.values.is_slt row 0 = 0)
  := by
    have h_selectors := selector_breakdown air row h_constraints
    clear *- h_selectors
    grind

  /-- Abstracting the gadget used. Follows the template
      `allHold → preceding ∧ AbsConstraints ∧ following`:

      * Preceding: the chip's own booleans on `is_slt`, `is_slt_u`, and
        their sum (`constraint_0`, `constraint_1`, `constraint_2`).
      * `LtSignedGadget.AbsConstraints` instantiated at the chip's
        accessors (covers `constraint_3` through `constraint_26`).
      * Following: the chip's own substantive constraints
        (`a_1 = a_2 = a_3 = 0` and `(is_real) * (a_0 - bit) = 0`). -/
  lemma allHold_abs
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_constraints : LtChip.Extraction.allHold air row)
  :
    LtSignedGadget.AbsConstraints
      ((air.cols.values.is_slt row 0) + (air.cols.values.is_slt_u row 0))
      (air.cols.values.is_slt row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.lt_signed.result.u16_flags_0 row 0)
      (air.cols.values.lt_signed.result.u16_flags_1 row 0)
      (air.cols.values.lt_signed.result.u16_flags_2 row 0)
      (air.cols.values.lt_signed.result.u16_flags_3 row 0)
      (air.cols.values.lt_signed.result.not_eq_inv row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)
      (air.cols.values.lt_signed.result.bit row 0)
      (air.cols.values.lt_signed.b_msb.msb row 0)
      (air.cols.values.lt_signed.c_msb.msb row 0)
    ∧ constraint_27 air row
    ∧ constraint_28 air row
    ∧ constraint_29 air row
    ∧ constraint_30 air row
  := by
    simp [
      LtSignedGadget.AbsConstraints,
      U16MSBGadget.AbsConstraints,
      LtWordU16Gadget.AbsConstraints,
      constraint_and_interaction_simplification
    ] at h_constraints ⊢
    aesop

  /-- The chip's per-row `BusRow` is exactly `LtChip.AbsBuses` instantiated
      at the chip's accessors. By `LtChip.AbsBuses`'s definition this in
      turn decomposes as `LtSignedGadget.AbsBuses (...) ++ <chip ALU entry>`,
      making the gadget's contribution explicit. -/
  lemma bus_row_abs
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
  :
    LtChip.Interactions.bus_row air row =
    LtChip.AbsBuses
      (air.cols.values.is_slt row 0)
      (air.cols.values.is_slt_u row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)
      (air.cols.values.lt_signed.result.bit row 0)
      (air.cols.values.lt_signed.b_msb.msb row 0)
      (air.cols.values.lt_signed.c_msb.msb row 0)
  := by rfl

end LtChip.Interpretations
