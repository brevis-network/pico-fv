import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.SLLChip
import PicoFV.RV64IM.Airs.SLLChip
import PicoFV.RV64IM.Constraints.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SLLChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and
the list of bus interactions emitted by `SLLChip::eval`
(`vm/src/chips/chips/alu/sll/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`) in terms of the
`Valid_SLLChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.SLLChip`.

The chip layout (matching `ShiftLeftValueCols<F>`) is:

| Cols   | Field path (under `air.cols.values`)             |
|--------|--------------------------------------------------|
| 0..3   | `a_0..a_3` (result)                              |
| 4..7   | `b_0..b_3` (operand 1)                           |
| 8..11  | `c_0..c_3` (operand 2; low 6 bits = shift amt)   |
| 12..17 | `c_bits_0..c_bits_5` (6 LSB bit decomposition)   |
| 18     | `v_01`  = 2^(c_bits_0 + 2·c_bits_1)              |
| 19     | `v_012` = v_01 · 2^(4·c_bits_2)                  |
| 20     | `v_0123` = v_012 · 2^(8·c_bits_3) (bit shift mult) |
| 21..24 | `shift_u16_0..shift_u16_3` (u16-shift selector)  |
| 25..28 | `lower_limb_0..lower_limb_3`                     |
| 29..32 | `higher_limb_0..higher_limb_3`                   |
| 33..36 | `limb_result_0..limb_result_3`                   |
| 37     | `sllw_msb.msb` (U16MSBGadget on a_1)             |
| 38     | `is_sll`                                         |
| 39     | `is_sllw`                                        |

`Valid_ShiftLeftValueCols.is_real = is_sll + is_sllw`.

Algebraic constraint breakdown (53 total):
- 0..2: `is_real`, `is_sll`, `is_sllw` boolean checks.
- 3..8: `c_bits_0..5` boolean checks.
- 9..16: `shift_u16_i` selectors and booleans (paired):
  conditional `shift_u16_i · ((c_bits_4 + 2·c_bits_5·is_sll) - i) = 0`
  plus `shift_u16_i · (shift_u16_i - 1) = 0`.
- 17: exactly-one `shift_u16` selector when `is_real = 1`.
- 18..20: `v_01`, `v_012`, `v_0123` cascade definitions.
- 21..24: per-limb shift carry equations
  `b_i · v_0123 = higher_limb_i · 65536 + lower_limb_i · v_0123`.
- 25..28: `limb_result_i = lower_limb_i · v_0123 (+ higher_limb_{i-1})`.
- 29..44: `is_sll`-gated u16-shift dispatch (4 selectors × 4 limbs).
- 45..50: `is_sllw`-gated u16-shift dispatch (2 selectors × 2 limbs)
  plus the sign-extension `a_2 = a_3 = sllw_msb · 65535`.
- 51..52: `is_sllw` and `sllw_msb` boolean checks
  (`is_sllw` is a duplicate of 2; `sllw_msb` is from U16MSBGadget).

Bus interactions (11 entries):
- 8 ByteBus opcode-9 entries: shift_carry verification of
  `(b_i · v_0123 − lower_limb_i · v_0123 · 65535/v_0123) = …`.
  Pairs `(lower_limb_i, higher_limb_i)` against `(16 − shift, shift)`.
- 1 ByteBus opcode-8 entry: U16MSBGadget on `b_1`,
  `2 · a_1 − sllw_msb · 65536`, gated by `-is_sllw`.
- 1 ALU entry: opcode `is_sll · 5 + is_sllw · 42` ∈ {5 (SLL), 42 (SLLW)},
  gated by `+is_real`, carrying `(a, b, c)`.
-/

namespace SLLChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraint 0: is_real = is_sll + is_sllw is boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_sll row 0) + (air.cols.values.is_sllw row 0)) *
          (((air.cols.values.is_sll row 0) + (air.cols.values.is_sllw row 0)) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 1: is_sll boolean.

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) * ((air.cols.values.is_sll row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 2: is_sllw boolean.

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) * ((air.cols.values.is_sllw row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraints 3..8: c_bits_{0..5} boolean.

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_0 row 0) * ((air.cols.values.c_bits_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_1 row 0) * ((air.cols.values.c_bits_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_2 row 0) * ((air.cols.values.c_bits_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_3 row 0) * ((air.cols.values.c_bits_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_4 row 0) * ((air.cols.values.c_bits_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_5 row 0) * ((air.cols.values.c_bits_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 9..16: shift_u16_i selectors paired with booleans.
      -- Selector i is active iff `c_bits_4 + 2·c_bits_5·is_sll = i`.
      -- For SLL: full 6-bit shift, so c_bits_4..5 select the u16-shift
      --   amount {0,1,2,3}.
      -- For SLLW: only c_bits_0..4 are used (5-bit shift), so c_bits_5
      --   doesn't contribute; shift_u16_i ∈ {0, 1}.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_0 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           (air.cols.values.c_bits_5 row 0) * 2 * (air.cols.values.is_sll row 0) - 0)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_0 row 0) * ((air.cols.values.shift_u16_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_1 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           (air.cols.values.c_bits_5 row 0) * 2 * (air.cols.values.is_sll row 0) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_1 row 0) * ((air.cols.values.shift_u16_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_2 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           (air.cols.values.c_bits_5 row 0) * 2 * (air.cols.values.is_sll row 0) - 2)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_2 row 0) * ((air.cols.values.shift_u16_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_3 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           (air.cols.values.c_bits_5 row 0) * 2 * (air.cols.values.is_sll row 0) - 3)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_3 row 0) * ((air.cols.values.shift_u16_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 17: exactly-one shift_u16 selector when is_real = 1.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_sll row 0) + (air.cols.values.is_sllw row 0)) *
          ((((air.cols.values.shift_u16_0 row 0) + (air.cols.values.shift_u16_1 row 0)) +
            (air.cols.values.shift_u16_2 row 0)) + (air.cols.values.shift_u16_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 18..20: v_01, v_012, v_0123 cascade.
      --   v_01    = (c_bits_0 + 1) · (3·c_bits_1 + 1)        ∈ {1, 2, 4, 8}
      --   v_012   = v_01 · (15·c_bits_2 + 1)                  ∈ … shifted
      --   v_0123  = v_012 · (255·c_bits_3 + 1)
      --         = 2^(c_bits_0 + 2·c_bits_1 + 4·c_bits_2 + 8·c_bits_3)
      --         = bit_shift_multiplier (in RV32 SllAir terminology).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.v_01 row 0) -
          ((air.cols.values.c_bits_0 row 0) + 1) *
            ((air.cols.values.c_bits_1 row 0) * 3 + 1)) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.v_012 row 0) -
          (air.cols.values.v_01 row 0) *
            ((air.cols.values.c_bits_2 row 0) * 15 + 1)) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.v_0123 row 0) -
          (air.cols.values.v_012 row 0) *
            ((air.cols.values.c_bits_3 row 0) * 255 + 1)) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 21..24: per-limb shift carry equations.
      --   b_i · v_0123 = higher_limb_i · 65536 + lower_limb_i · v_0123
      -- Splitting `b_i << k` (where v_0123 = 2^k) into u16-low + u16-high.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.b_0 row 0) * (air.cols.values.v_0123 row 0) -
          ((air.cols.values.higher_limb_0 row 0) * 65536 +
           (air.cols.values.lower_limb_0 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.b_1 row 0) * (air.cols.values.v_0123 row 0) -
          ((air.cols.values.higher_limb_1 row 0) * 65536 +
           (air.cols.values.lower_limb_1 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.b_2 row 0) * (air.cols.values.v_0123 row 0) -
          ((air.cols.values.higher_limb_2 row 0) * 65536 +
           (air.cols.values.lower_limb_2 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.b_3 row 0) * (air.cols.values.v_0123 row 0) -
          ((air.cols.values.higher_limb_3 row 0) * 65536 +
           (air.cols.values.lower_limb_3 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 25..28: limb_result_i carry composition.
      --   limb_result_0 = lower_limb_0 · v_0123
      --   limb_result_{i+1} = lower_limb_{i+1} · v_0123 + higher_limb_i
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_0 row 0) -
          (air.cols.values.lower_limb_0 row 0) * (air.cols.values.v_0123 row 0)) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_1 row 0) -
          ((air.cols.values.lower_limb_1 row 0) * (air.cols.values.v_0123 row 0) +
           (air.cols.values.higher_limb_0 row 0))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_2 row 0) -
          ((air.cols.values.lower_limb_2 row 0) * (air.cols.values.v_0123 row 0) +
           (air.cols.values.higher_limb_1 row 0))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_3 row 0) -
          ((air.cols.values.lower_limb_3 row 0) * (air.cols.values.v_0123 row 0) +
           (air.cols.values.higher_limb_2 row 0))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 29..44: is_sll-gated u16-shift dispatch.
      --   shift_u16_0 (no u16 shift): a_i = limb_result_i for i = 0..3
      --   shift_u16_1 (1 u16):        a_0 = 0; a_{i+1} = limb_result_i
      --   shift_u16_2 (2 u16):        a_0 = a_1 = 0; a_2 = limb_result_0; a_3 = limb_result_1
      --   shift_u16_3 (3 u16):        a_0 = a_1 = a_2 = 0; a_3 = limb_result_0
      -- =====================================================================

      -- shift_u16_0 (29-32): a_i = limb_result_i
      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_0 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.limb_result_1 row 0)))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_2 row 0) - (air.cols.values.limb_result_2 row 0)))) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.limb_result_3 row 0)))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_1 (33-36): a_0 = 0; a_{i+1} = limb_result_i
      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_1 row 0) * (air.cols.values.a_0 row 0))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_2 row 0) - (air.cols.values.limb_result_1 row 0)))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.limb_result_2 row 0)))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_2 (37-40): a_0 = a_1 = 0; a_2 = limb_result_0; a_3 = limb_result_1
      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_2 row 0) * (air.cols.values.a_0 row 0))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_2 row 0) * (air.cols.values.a_1 row 0))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_2 row 0) *
           ((air.cols.values.a_2 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_2 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.limb_result_1 row 0)))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_3 (41-44): a_0 = a_1 = a_2 = 0; a_3 = limb_result_0
      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_3 row 0) * (air.cols.values.a_0 row 0))) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_3 row 0) * (air.cols.values.a_1 row 0))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_3 row 0) * (air.cols.values.a_2 row 0))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sll row 0) *
          ((air.cols.values.shift_u16_3 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 45..50: is_sllw-gated u16-shift dispatch + sign-ext.
      --   shift_u16_0 active (shift ∈ [0,15]):
      --     a_0 = limb_result_0, a_1 = limb_result_1
      --   shift_u16_1 active (shift ∈ [16,31]):
      --     a_0 = 0, a_1 = limb_result_0
      --   Always (sign-extend low 32 to 64):
      --     a_2 = a_3 = sllw_msb · 65535
      -- =====================================================================

      -- shift_u16_0 case (45-46)
      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_0 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.limb_result_1 row 0)))) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_1 case (47-48)
      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) *
          ((air.cols.values.shift_u16_1 row 0) * (air.cols.values.a_0 row 0))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Sign-extension to 64-bit (49-50): a_2 = a_3 = sllw_msb · 65535
      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) *
          ((air.cols.values.sllw_msb.msb row 0) * 65535 - (air.cols.values.a_2 row 0))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) *
          ((air.cols.values.sllw_msb.msb row 0) * 65535 - (air.cols.values.a_3 row 0))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 51..52: is_sllw (duplicate) and sllw_msb boolean checks
      -- (from the embedded U16MSBGadget on a_1).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sllw row 0) * ((air.cols.values.is_sllw row 0) - 1)) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_SLLChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.sllw_msb.msb row 0) * ((air.cols.values.sllw_msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_SLLChip F ExtF) (row : ℕ)
      : SLLChip.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 53 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_SLLChip F ExtF) (row : ℕ) : List Prop :=
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
          constraint_30 air row, constraint_31 air row, constraint_32 air row,
          constraint_33 air row, constraint_34 air row, constraint_35 air row,
          constraint_36 air row, constraint_37 air row, constraint_38 air row,
          constraint_39 air row, constraint_40 air row, constraint_41 air row,
          constraint_42 air row, constraint_43 air row, constraint_44 air row,
          constraint_45 air row, constraint_46 air row, constraint_47 air row,
          constraint_48 air row, constraint_49 air row, constraint_50 air row,
          constraint_51 air row, constraint_52 air row
        ]

    end row_constraints

    section row_buses

      -- =====================================================================
      -- Bus interactions (per row):
      --   8 ByteBus opcode-9 entries: shift_carry verification pairing
      --     limb-result and higher_limb values against the low-4-bit
      --     shift amount `s4 = c_bits_0..3` and `16 - s4`.
      --   1 ByteBus opcode-8 entry: U16MSBGadget on a_1
      --     (gated by `-is_sllw`).
      --   1 ALU entry: opcode `is_sll · 5 + is_sllw · 42` ∈ {5, 42},
      --     gated by `+is_real`, carrying (a, b, c).
      -- The `inv(2)` constant in the extraction is `2097414145`
      -- (since `2 * 2097414145 ≡ 1 (mod KB_prime)`).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_SLLChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        let mult : FKB := air.cols.values.is_sll row 0 + air.cols.values.is_sllw row 0
        let s4 : FKB :=
          (air.cols.values.c_bits_0 row 0) * 1 +
          (air.cols.values.c_bits_1 row 0) * 2 +
          (air.cols.values.c_bits_2 row 0) * 4 +
          (air.cols.values.c_bits_3 row 0) * 8
        let s5 : FKB :=
          s4 + (air.cols.values.c_bits_4 row 0) * 16 + (air.cols.values.c_bits_5 row 0) * 32
        [
          (-mult, [4, 9, ((air.cols.values.c_0 row 0) - s5) * 2097414145, 0, 10, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_0 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_0 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_1 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_1 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_2 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_2 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_3 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_3 row 0), 0, s4, 0]),
          (-(air.cols.values.is_sllw row 0),
            [4, 8, 2 * (air.cols.values.a_1 row 0) - (air.cols.values.sllw_msb.msb row 0) * 65536, 0, 0, 0]),
          (mult,
            [3,
              (air.cols.values.is_sll row 0) * 5 + (air.cols.values.is_sllw row 0) * 42,
              (air.cols.values.a_0 row 0), (air.cols.values.a_1 row 0),
              (air.cols.values.a_2 row 0), (air.cols.values.a_3 row 0),
              (air.cols.values.b_0 row 0), (air.cols.values.b_1 row 0),
              (air.cols.values.b_2 row 0), (air.cols.values.b_3 row 0),
              (air.cols.values.c_0 row 0), (air.cols.values.c_1 row 0),
              (air.cols.values.c_2 row 0), (air.cols.values.c_3 row 0)])
        ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_SLLChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_SLLChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_SLLChip FKB ExtF)
      (row : ℕ)
    :
      SLLChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row)
          ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        SLLChip.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold SLLChip.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end SLLChip.ConstraintsAndBuses

namespace SLLChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `SLLChip` row: 9 byte-bus entries (8 for
      the shift carry chain + 1 for the U16MSBGadget on `b_1`) plus
      1 ALU entry. -/
  def bus_row (air : Valid_SLLChip FKB ExtF) (row : ℕ) : BusRow :=
    let mult : FKB := air.cols.values.is_sll row 0 + air.cols.values.is_sllw row 0
    let s4 : FKB :=
      (air.cols.values.c_bits_0 row 0) * 1 +
      (air.cols.values.c_bits_1 row 0) * 2 +
      (air.cols.values.c_bits_2 row 0) * 4 +
      (air.cols.values.c_bits_3 row 0) * 8
    let s5 : FKB :=
      s4 + (air.cols.values.c_bits_4 row 0) * 16 + (air.cols.values.c_bits_5 row 0) * 32
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (mult,
          #v[
            (air.cols.values.is_sll row 0) * 5 + (air.cols.values.is_sllw row 0) * 42,
            (air.cols.values.a_0 row 0), (air.cols.values.a_1 row 0),
            (air.cols.values.a_2 row 0), (air.cols.values.a_3 row 0),
            (air.cols.values.b_0 row 0), (air.cols.values.b_1 row 0),
            (air.cols.values.b_2 row 0), (air.cols.values.b_3 row 0),
            (air.cols.values.c_0 row 0), (air.cols.values.c_1 row 0),
            (air.cols.values.c_2 row 0), (air.cols.values.c_3 row 0) ])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-mult, #v[9, ((air.cols.values.c_0 row 0) - s5) * 2097414145, 0, 10, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_0 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_0 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_1 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_1 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_2 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_2 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_3 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_3 row 0), 0, s4, 0]),
        (-(air.cols.values.is_sllw row 0),
          #v[8, 2 * (air.cols.values.a_1 row 0) - (air.cols.values.sllw_msb.msb row 0) * 65536, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

  set_option maxRecDepth 4_000_000 in
  @[simp]
  lemma bus_row_equiv (air : Valid_SLLChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (SLLChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    dsimp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      pico_encapsulation,
    ]

end SLLChip.Interactions

namespace SLLChip.Interpretations

  open RV64IM_Interactions
  open SLLChip.ConstraintsAndBuses
  open SLLChip.Interactions

  /-- Each selector is binary and `is_real = is_sll + is_sllw ∈ {0, 1}`. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_constraints : SLLChip.Extraction.allHold air row)
  :
    (air.cols.values.is_sll row 0 = 0 ∨ air.cols.values.is_sll row 0 = 1) ∧
    (air.cols.values.is_sllw row 0 = 0 ∨ air.cols.values.is_sllw row 0 = 1) ∧
    (air.cols.values.is_sll row 0 + air.cols.values.is_sllw row 0 = 0 ∨
     air.cols.values.is_sll row 0 + air.cols.values.is_sllw row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    obtain ⟨_, h_real, h_sll, h_sllw, _⟩ := h_constraints
    clear *- h_real h_sll h_sllw
    grind

  /-- At most one selector is active. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_constraints : SLLChip.Extraction.allHold air row)
  :
    (air.cols.values.is_sll row 0 = 1 → air.cols.values.is_sllw row 0 = 0) ∧
    (air.cols.values.is_sllw row 0 = 1 → air.cols.values.is_sll row 0 = 0)
  := by
    have h_selectors := selector_breakdown air row h_constraints
    clear *- h_selectors
    grind

end SLLChip.Interpretations
