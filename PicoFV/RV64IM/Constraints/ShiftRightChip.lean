import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.ShiftRightChip
import PicoFV.RV64IM.Airs.ShiftRightChip
import PicoFV.RV64IM.Constraints.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# ShiftRightChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each constraint and
the list of bus interactions emitted by `ShiftRightChip::eval`
(`vm/src/chips/chips/alu/sr/constraints.rs` at commit
`b6f2de04bef696f0eb7f918a494b2ac3c841d0b0`) in terms of the
`Valid_ShiftRightChip` air's named accessors, plus a `_equiv` lemma per
constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.ShiftRightChip`.

The chip layout (matching `ShiftRightValueCols<F>`) is:

| Cols   | Field path (under `air.cols.values`)             |
|--------|--------------------------------------------------|
| 0..3   | `a_0..a_3` (result)                              |
| 4..7   | `b_0..b_3` (operand 1)                           |
| 8..11  | `c_for_lookup_0..c_for_lookup_3` (operand 2 on ALU bus) |
| 12     | `b_msb.msb` (U16MSBGadget on `b_3`/`b_1`)        |
| 13     | `srw_msb.msb` (U16MSBGadget on `a_1`, for W ops) |
| 14..19 | `c_bits_0..c_bits_5` (low 6 bits of shift amt)   |
| 20     | `c` (chip's internal shift amount)               |
| 21     | `imm_c`                                          |
| 22     | `sra_msb_v0123` = `b_msb · v_0123`               |
| 23     | `v_0123` = 2^(16 - s4) where s4 = c_bits_0..3    |
| 24     | `v_012`                                          |
| 25     | `v_01`                                           |
| 26..29 | `lower_limb_0..lower_limb_3` (low s4 bits of b_i)|
| 30..33 | `higher_limb_0..higher_limb_3` (high 16-s4 bits) |
| 34..37 | `limb_result_0..limb_result_3`                   |
| 38..41 | `shift_u16_0..shift_u16_3`                       |
| 42     | `is_srl`                                         |
| 43     | `is_sra`                                         |
| 44     | `is_srlw`                                        |
| 45     | `is_sraw`                                        |
| 46     | `is_w_imm`                                       |

`is_real = is_srl + is_sra + is_srlw + is_sraw`.

Algebraic constraint breakdown (59 total):
- 0..3: `is_srl`, `is_sra`, `is_srlw`, `is_sraw` boolean checks.
- 4: `imm_c` boolean.
- 5: `is_w_imm = (is_srlw + is_sraw) · imm_c`.
- 6..11: `c_bits_0..5` boolean checks.
- 12..14: `v_01`, `v_012`, `v_0123` cascade definitions (note: `v_0123 = 2^(16 - s4)`,
  the inverse direction from SLLChip).
- 15..22: `shift_u16_i` selectors and booleans (paired):
  conditional `shift_u16_i · ((c_bits_4 + 2·c_bits_5·(is_srl + is_sra)) - i) = 0`
  plus `shift_u16_i · (shift_u16_i - 1) = 0`.
- 23: exactly-one `shift_u16` selector when `is_real = 1`.
- 24..26: `limb_result_i = higher_limb_i + lower_limb_{i+1} · v_0123` for i = 0..2.
- 27: `limb_result_3 = higher_limb_3` (top u16 has no carry-in from lower_limb_4).
- 28..31: duplicates (is_sra, b_msb, is_sraw, b_msb boolean checks).
- 32: `(is_srl + is_srlw) · b_msb = 0` (no sign extension for logical shift).
- 33: `sra_msb_v0123 = b_msb · v_0123`.
- 34: `(is_srlw + is_sraw)` boolean (i.e., `is_word` is boolean).
- 35: `srw_msb` boolean.
- 36: `(is_srl + is_sra) · srw_msb = 0` (no SRW msb for non-word).
- 37..52: `(is_srl + is_sra)`-gated u16-shift dispatch (4 selectors × 4 limbs):
  the active limb gets `limb_result_? + (b_msb · 65536 - sra_msb_v0123)`
  (the "boundary" limb), others get `limb_result_?` or `b_msb · 65535` (top sign-extension).
- 53..56: `(is_srlw + is_sraw)`-gated u16-shift dispatch (2 selectors × 2 limbs).
- 57..58: `(is_srlw + is_sraw)` × `a_2/a_3 = srw_msb · 65535` (sign-extend to 64).

Bus interactions (12 entries):
- 9 ByteBus opcode-9 (BitRange) entries:
  1 for `(c − s5_full) · inv64 < 1024` (pins `c.val mod 64 = s5_full.val`).
  4 × 2 for `(lower_limb_i, higher_limb_i)` paired against `(s4, 16 − s4)`.
- 3 ByteBus opcode-8 (U16Range) entries (U16MSB gadgets):
  - `(-is_sra, [8, 2·b_3 − b_msb·65536, 0, 0, 0])` — pins `b_msb = MSB(b_3)` for SRA.
  - `(-is_sraw, [8, 2·b_1 − b_msb·65536, 0, 0, 0])` — pins `b_msb = MSB(b_1)` for SRAW.
  - `(-(is_srlw + is_sraw), [8, 2·a_1 − srw_msb·65536, 0, 0, 0])` — pins `srw_msb = MSB(a_1)`.
- 1 ALU entry: opcode `is_srl·6 + is_sra·7 + is_srlw·43 + is_sraw·44`,
  multiplicity `+is_real`, carrying `(a, b, c_for_lookup)`.
-/

namespace ShiftRightChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      -- =====================================================================
      -- Constraints 0..3: is_srl, is_sra, is_srlw, is_sraw booleans.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_srl row 0) * ((air.cols.values.is_srl row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sra row 0) * ((air.cols.values.is_sra row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_srlw row 0) * ((air.cols.values.is_srlw row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sraw row 0) * ((air.cols.values.is_sraw row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 4: imm_c boolean.

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.imm_c row 0) * ((air.cols.values.imm_c row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraint 5: is_w_imm = (is_srlw + is_sraw) * imm_c.

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_w_imm row 0) -
          (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
            (air.cols.values.imm_c row 0))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 6..11: c_bits_0..5 boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_0 row 0) * ((air.cols.values.c_bits_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_1 row 0) * ((air.cols.values.c_bits_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_2 row 0) * ((air.cols.values.c_bits_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_3 row 0) * ((air.cols.values.c_bits_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_4 row 0) * ((air.cols.values.c_bits_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.c_bits_5 row 0) * ((air.cols.values.c_bits_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 12..14: v_01, v_012, v_0123 cascade.
      --   v_01    = ((1 - c_bits_0) + 1) · 2 · ((1 - c_bits_1) · 3 + 1)
      --           = 2^(3 - c_bits_0 - 2·c_bits_1)  (range {1, 2, 4, 8})
      --   v_012   = v_01 · ((1 - c_bits_2) · 15 + 1)  (multiply by 16 iff c_bits_2 = 0)
      --   v_0123  = v_012 · ((1 - c_bits_3) · 255 + 1)
      --         = 2^(16 - s4) where s4 = c_bits_0 + 2·c_bits_1 + 4·c_bits_2 + 8·c_bits_3.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.v_01 row 0) -
          (((1 - (air.cols.values.c_bits_0 row 0)) + 1) * 2) *
            (((1 - (air.cols.values.c_bits_1 row 0)) * 3) + 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.v_012 row 0) -
          (air.cols.values.v_01 row 0) *
            (((1 - (air.cols.values.c_bits_2 row 0)) * 15) + 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.v_0123 row 0) -
          (air.cols.values.v_012 row 0) *
            (((1 - (air.cols.values.c_bits_3 row 0)) * 255) + 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 15..22: shift_u16_i selectors and booleans.
      --   shift_u16_i is non-zero iff c_bits_4 + 2·c_bits_5·(is_srl + is_sra) = i.
      --   For 64-bit ops (is_srl + is_sra = 1): full 6-bit shift, so the
      --     selector i ∈ {0, 1, 2, 3} from c_bits_4 + 2·c_bits_5.
      --   For W variants (is_srl + is_sra = 0): c_bits_5 doesn't contribute,
      --     so i ∈ {0, 1} (5-bit shift).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_0 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           ((air.cols.values.c_bits_5 row 0) * 2) *
             ((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) - 0)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_0 row 0) * ((air.cols.values.shift_u16_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_1 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           ((air.cols.values.c_bits_5 row 0) * 2) *
             ((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) - 1)) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_1 row 0) * ((air.cols.values.shift_u16_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_2 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           ((air.cols.values.c_bits_5 row 0) * 2) *
             ((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) - 2)) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_2 row 0) * ((air.cols.values.shift_u16_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_3 row 0) *
          ((air.cols.values.c_bits_4 row 0) +
           ((air.cols.values.c_bits_5 row 0) * 2) *
             ((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) - 3)) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.shift_u16_3 row 0) * ((air.cols.values.shift_u16_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 23: is_real · (shift_u16_sum - 1) = 0.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) +
          (air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((((air.cols.values.shift_u16_0 row 0) + (air.cols.values.shift_u16_1 row 0)) +
            (air.cols.values.shift_u16_2 row 0)) + (air.cols.values.shift_u16_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 24..27: limb_result_i carry composition (right shift).
      --   limb_result_i = higher_limb_i + lower_limb_{i+1} · v_0123     (i = 0, 1, 2)
      --   limb_result_3 = higher_limb_3                                  (no carry-in)
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_0 row 0) -
          ((air.cols.values.higher_limb_0 row 0) +
           (air.cols.values.lower_limb_1 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_1 row 0) -
          ((air.cols.values.higher_limb_1 row 0) +
           (air.cols.values.lower_limb_2 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_2 row 0) -
          ((air.cols.values.higher_limb_2 row 0) +
           (air.cols.values.lower_limb_3 row 0) * (air.cols.values.v_0123 row 0))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.limb_result_3 row 0) - (air.cols.values.higher_limb_3 row 0)) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 28..31: duplicate boolean checks
      -- (is_sra, b_msb, is_sraw, b_msb again).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sra row 0) * ((air.cols.values.is_sra row 0) - 1)) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.b_msb.msb row 0) * ((air.cols.values.b_msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.is_sraw row 0) * ((air.cols.values.is_sraw row 0) - 1)) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.b_msb.msb row 0) * ((air.cols.values.b_msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 32: (is_srl + is_srlw) · b_msb = 0
      -- (b_msb must be 0 for logical shifts).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_srlw row 0)) *
          (air.cols.values.b_msb.msb row 0)) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 33: sra_msb_v0123 = b_msb · v_0123.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.sra_msb_v0123 row 0) -
          (air.cols.values.b_msb.msb row 0) * (air.cols.values.v_0123 row 0)) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 34: (is_srlw + is_sraw) is boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) - 1)) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 35: srw_msb boolean.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.srw_msb.msb row 0) * ((air.cols.values.srw_msb.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraint 36: (is_srl + is_sra) · srw_msb = 0
      -- (srw_msb only used for W variants).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          (air.cols.values.srw_msb.msb row 0)) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 37..52: (is_srl + is_sra)-gated u16-shift dispatch.
      -- 4 selectors × 4 limbs = 16 constraints.
      --   shift_u16_0: a_0 = lr_0, a_1 = lr_1, a_2 = lr_2,
      --                a_3 = lr_3 + (b_msb · 65536 - sra_msb_v0123)
      --   shift_u16_1: a_0 = lr_1, a_1 = lr_2,
      --                a_2 = lr_3 + (b_msb · 65536 - sra_msb_v0123),
      --                a_3 = b_msb · 65535
      --   shift_u16_2: a_0 = lr_2,
      --                a_1 = lr_3 + (b_msb · 65536 - sra_msb_v0123),
      --                a_2 = a_3 = b_msb · 65535
      --   shift_u16_3: a_0 = lr_3 + (b_msb · 65536 - sra_msb_v0123),
      --                a_1 = a_2 = a_3 = b_msb · 65535
      -- =====================================================================

      -- shift_u16_0 (37..40)
      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_0 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.limb_result_1 row 0)))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_2 row 0) - (air.cols.values.limb_result_2 row 0)))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_3 row 0) -
             ((air.cols.values.limb_result_3 row 0) +
              ((air.cols.values.b_msb.msb row 0) * 65536 -
               (air.cols.values.sra_msb_v0123 row 0)))))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_1 (41..44)
      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_0 row 0) - (air.cols.values.limb_result_1 row 0)))) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.limb_result_2 row 0)))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_2 row 0) -
             ((air.cols.values.limb_result_3 row 0) +
              ((air.cols.values.b_msb.msb row 0) * 65536 -
               (air.cols.values.sra_msb_v0123 row 0)))))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_2 (45..48)
      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_2 row 0) *
           ((air.cols.values.a_0 row 0) - (air.cols.values.limb_result_2 row 0)))) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_2 row 0) *
           ((air.cols.values.a_1 row 0) -
             ((air.cols.values.limb_result_3 row 0) +
              ((air.cols.values.b_msb.msb row 0) * 65536 -
               (air.cols.values.sra_msb_v0123 row 0)))))) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_2 row 0) *
           ((air.cols.values.a_2 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_2 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- shift_u16_3 (49..52)
      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_3 row 0) *
           ((air.cols.values.a_0 row 0) -
             ((air.cols.values.limb_result_3 row 0) +
              ((air.cols.values.b_msb.msb row 0) * 65536 -
               (air.cols.values.sra_msb_v0123 row 0)))))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_3 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_3 row 0) *
           ((air.cols.values.a_2 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0)) *
          ((air.cols.values.shift_u16_3 row 0) *
           ((air.cols.values.a_3 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 53..56: (is_srlw + is_sraw)-gated u16-shift dispatch.
      -- 2 selectors (only shift_u16_0 and shift_u16_1 for word ops) × 2 a-limbs.
      --   shift_u16_0: a_0 = lr_0,
      --                a_1 = higher_limb_1 + (b_msb · 65536 - sra_msb_v0123)
      --   shift_u16_1: a_0 = higher_limb_1 + (b_msb · 65536 - sra_msb_v0123),
      --                a_1 = b_msb · 65535
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_0 row 0) - (air.cols.values.limb_result_0 row 0)))) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((air.cols.values.shift_u16_0 row 0) *
           ((air.cols.values.a_1 row 0) -
             ((air.cols.values.higher_limb_1 row 0) +
              ((air.cols.values.b_msb.msb row 0) * 65536 -
               (air.cols.values.sra_msb_v0123 row 0)))))) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_0 row 0) -
             ((air.cols.values.higher_limb_1 row 0) +
              ((air.cols.values.b_msb.msb row 0) * 65536 -
               (air.cols.values.sra_msb_v0123 row 0)))))) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((air.cols.values.shift_u16_1 row 0) *
           ((air.cols.values.a_1 row 0) - (air.cols.values.b_msb.msb row 0) * 65535))) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Constraints 57..58: W-variant sign extension to 64 bits.
      -- a_2 = a_3 = srw_msb · 65535 for is_word.
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((air.cols.values.a_2 row 0) - (air.cols.values.srw_msb.msb row 0) * 65535)) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)) *
          ((air.cols.values.a_3 row 0) - (air.cols.values.srw_msb.msb row 0) * 65535)) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_ShiftRightChip F ExtF) (row : ℕ)
      : ShiftRightChip.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- =====================================================================
      -- Aggregate list of all 59 row constraints.
      -- =====================================================================

      @[simp]
      def row_constraint_list (air : Valid_ShiftRightChip F ExtF) (row : ℕ) : List Prop :=
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
          constraint_51 air row, constraint_52 air row, constraint_53 air row,
          constraint_54 air row, constraint_55 air row, constraint_56 air row,
          constraint_57 air row, constraint_58 air row
        ]

    end row_constraints

    section row_buses

      -- =====================================================================
      -- Bus interactions (per row):
      --   1 ByteBus opcode-9 entry: `(c − s5_full) · inv64` width 10
      --     (pins `c.val mod 64 = s5_full.val`, where
      --      `s5_full = c_bits_0 + c_bits_1·2 + ... + c_bits_5·32`).
      --   8 ByteBus opcode-9 entries: lower/higher limb decomposition.
      --   3 ByteBus opcode-8 entries (U16MSB):
      --     - b_msb on b_3, gated by is_sra.
      --     - b_msb on b_1, gated by is_sraw.
      --     - srw_msb on a_1, gated by is_srlw + is_sraw.
      --   1 ALU entry: opcode `is_srl·6 + is_sra·7 + is_srlw·43 + is_sraw·44`,
      --     gated by +is_real, carrying (a, b, c_for_lookup).
      -- =====================================================================

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_ShiftRightChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        let mult : FKB :=
          (air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0) +
          (air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)
        let s4 : FKB :=
          (air.cols.values.c_bits_0 row 0) * 1 +
          (air.cols.values.c_bits_1 row 0) * 2 +
          (air.cols.values.c_bits_2 row 0) * 4 +
          (air.cols.values.c_bits_3 row 0) * 8
        let s5 : FKB :=
          s4 + (air.cols.values.c_bits_4 row 0) * 16 + (air.cols.values.c_bits_5 row 0) * 32
        [
          (-mult, [4, 9, ((air.cols.values.c row 0) - s5) * 2097414145, 0, 10, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_0 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_0 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_1 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_1 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_2 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_2 row 0), 0, 16 - s4, 0]),
          (-mult, [4, 9, (air.cols.values.lower_limb_3 row 0), 0, s4, 0]),
          (-mult, [4, 9, (air.cols.values.higher_limb_3 row 0), 0, 16 - s4, 0]),
          (-(air.cols.values.is_sra row 0),
            [4, 8, 2 * (air.cols.values.b_3 row 0) - (air.cols.values.b_msb.msb row 0) * 65536, 0, 0, 0]),
          (-(air.cols.values.is_sraw row 0),
            [4, 8, 2 * (air.cols.values.b_1 row 0) - (air.cols.values.b_msb.msb row 0) * 65536, 0, 0, 0]),
          (-((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)),
            [4, 8, 2 * (air.cols.values.a_1 row 0) - (air.cols.values.srw_msb.msb row 0) * 65536, 0, 0, 0]),
          (mult,
            [3,
              (air.cols.values.is_srl row 0) * 6 + (air.cols.values.is_sra row 0) * 7 +
              (air.cols.values.is_srlw row 0) * 43 + (air.cols.values.is_sraw row 0) * 44,
              (air.cols.values.a_0 row 0), (air.cols.values.a_1 row 0),
              (air.cols.values.a_2 row 0), (air.cols.values.a_3 row 0),
              (air.cols.values.b_0 row 0), (air.cols.values.b_1 row 0),
              (air.cols.values.b_2 row 0), (air.cols.values.b_3 row 0),
              (air.cols.values.c_for_lookup_0 row 0), (air.cols.values.c_for_lookup_1 row 0),
              (air.cols.values.c_for_lookup_2 row 0), (air.cols.values.c_for_lookup_3 row 0)])
        ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_ShiftRightChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_ShiftRightChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_ShiftRightChip FKB ExtF)
      (row : ℕ)
    :
      ShiftRightChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      have equiv_constraints
      :
        List.Forall (fun x ↦ x) (Extraction.constraint_list air row)
          ↔ List.Forall (·) (row_constraint_list air row)
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      have equiv_interactions
      :
        ShiftRightChip.Extraction.constrain_interactions air ↔ constrain_interactions air
      := by
        simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
      unfold ShiftRightChip.Extraction.allHold allHold_simplified
      simp only [*]

  end constraint_simplification

end ShiftRightChip.ConstraintsAndBuses

namespace ShiftRightChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `ShiftRightChip` row: 12 byte-bus entries +
      1 ALU entry. -/
  def bus_row (air : Valid_ShiftRightChip FKB ExtF) (row : ℕ) : BusRow :=
    let mult : FKB :=
      (air.cols.values.is_srl row 0) + (air.cols.values.is_sra row 0) +
      (air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)
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
            (air.cols.values.is_srl row 0) * 6 + (air.cols.values.is_sra row 0) * 7 +
            (air.cols.values.is_srlw row 0) * 43 + (air.cols.values.is_sraw row 0) * 44,
            (air.cols.values.a_0 row 0), (air.cols.values.a_1 row 0),
            (air.cols.values.a_2 row 0), (air.cols.values.a_3 row 0),
            (air.cols.values.b_0 row 0), (air.cols.values.b_1 row 0),
            (air.cols.values.b_2 row 0), (air.cols.values.b_3 row 0),
            (air.cols.values.c_for_lookup_0 row 0), (air.cols.values.c_for_lookup_1 row 0),
            (air.cols.values.c_for_lookup_2 row 0), (air.cols.values.c_for_lookup_3 row 0) ])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-mult, #v[9, ((air.cols.values.c row 0) - s5) * 2097414145, 0, 10, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_0 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_0 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_1 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_1 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_2 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_2 row 0), 0, 16 - s4, 0]),
        (-mult, #v[9, (air.cols.values.lower_limb_3 row 0), 0, s4, 0]),
        (-mult, #v[9, (air.cols.values.higher_limb_3 row 0), 0, 16 - s4, 0]),
        (-(air.cols.values.is_sra row 0),
          #v[8, 2 * (air.cols.values.b_3 row 0) - (air.cols.values.b_msb.msb row 0) * 65536, 0, 0, 0]),
        (-(air.cols.values.is_sraw row 0),
          #v[8, 2 * (air.cols.values.b_1 row 0) - (air.cols.values.b_msb.msb row 0) * 65536, 0, 0, 0]),
        (-((air.cols.values.is_srlw row 0) + (air.cols.values.is_sraw row 0)),
          #v[8, 2 * (air.cols.values.a_1 row 0) - (air.cols.values.srw_msb.msb row 0) * 65536, 0, 0, 0])
      ],
      State := [],
      Memory := []
    }

  set_option maxRecDepth 4_000_000 in
  @[simp]
  lemma bus_row_equiv (air : Valid_ShiftRightChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (ShiftRightChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    dsimp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      pico_encapsulation,
    ]

end ShiftRightChip.Interactions

namespace ShiftRightChip.Interpretations

  open RV64IM_Interactions
  open ShiftRightChip.ConstraintsAndBuses

  -- =====================================================================
  -- Selector breakdown: each `is_*` is 0 or 1.
  -- =====================================================================
  lemma selector_breakdown
    [Field ExtF] (air : Valid_ShiftRightChip FKB ExtF) (row : ℕ)
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
  :
    (air.cols.values.is_srl row 0 = 0 ∨ air.cols.values.is_srl row 0 = 1) ∧
    (air.cols.values.is_sra row 0 = 0 ∨ air.cols.values.is_sra row 0 = 1) ∧
    (air.cols.values.is_srlw row 0 = 0 ∨ air.cols.values.is_srlw row 0 = 1) ∧
    (air.cols.values.is_sraw row 0 = 0 ∨ air.cols.values.is_sraw row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    obtain ⟨_, h_srl_b, h_sra_b, h_srlw_b, h_sraw_b, _⟩ := h_constraints
    clear *- h_srl_b h_sra_b h_srlw_b h_sraw_b
    grind

end ShiftRightChip.Interpretations
