import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.DivRemChip
import PicoFV.RV64IM.Airs.DivRemChip
import PicoFV.RV64IM.Spec.MulGadget
import PicoFV.RV64IM.Spec.AddGadget
import PicoFV.RV64IM.Spec.IsZeroWordGadget
import PicoFV.RV64IM.Spec.IsEqualWordGadget
import PicoFV.RV64IM.Spec.LtWordU16Gadget
import PicoFV.RV64IM.Spec.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# DivRemChip — abstract constraints & buses (RV64)

`DivRemChip`'s Pico Rust source is
`vm/src/chips/chips/alu/divrem/constraints.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

The chip verifies `b = c · quotient + remainder` for each of the
eight DIV/REM opcodes — `DIV`, `DIVU`, `REM`, `REMU`, `DIVW`, `REMW`,
`DIVUW`, `REMUW` — with three orthogonal concerns:

1. **Sign reasoning** — `b_msb`, `c_msb`, `rem_msb` u16-MSB gadgets +
   per-quantity `*_neg` flags pinned to `msb · is_signed_type`.
2. **Width handling** — separate `quotient_comp` / `remainder_comp`
   reconstructions for word vs non-word ops:
   * 64-bit ops: `*_comp = *` identity.
   * Signed word ops: `*_comp` upper limbs = `quot_msb·0xFFFF` /
     `rem_msb·0xFFFF`, lower limbs = `*` (sign-extended view).
   * Unsigned word ops: `*_comp` upper limbs = 0 (zero-extended view).
3. **128-bit arithmetic** — two `MulGadget` instances compute the
   low/high 64 bits of `c · quotient_comp`; the 16-byte product plus
   the 8-byte sign-extended `remainder_comp` are added with carry
   propagation (8 byte chain); the result's lower 32 bits must equal
   `b`'s lower 32 bits, and the upper 32 must equal `b_neg · 0xFFFF`
   (sign-extension of `b`) — except in the unique overflow case
   `b = INT_MIN, c = -1` where the constraint is relaxed.

Plus: division-by-zero (`is_c_0` ⇒ quotient = `u64::MAX`, remainder =
`b`), `|remainder| < |c|` via `LtWordU16Gadget`, `a = quotient` or
`a = remainder` per opcode, exact-one-selector, and bus emission
(two `looking_alu(ADD, …)` for abs-value sub-events plus one
`looked_alu` for the main DivRem event).

## Layout (218 columns under `air.cols.values`)

| Cols      | Field                            |
|-----------|----------------------------------|
| 0..3      | `a_0..a_3` (output)              |
| 4..7      | `b_0..b_3`                       |
| 8..11     | `c_0..c_3`                       |
| 12..15    | `quotient_0..3`                  |
| 16..19    | `quotient_comp_0..3`             |
| 20..23    | `remainder_comp_0..3`            |
| 24..27    | `remainder_0..3`                 |
| 28..31    | `abs_remainder_0..3`             |
| 32..35    | `abs_c_0..3`                     |
| 36..39    | `max_abs_c_or_1_0..3`            |
| 40..47    | `c_times_quotient_0..7`          |
| 48..92    | `c_times_quotient_lower` (45 cols, `MulGadget`) |
| 93..137   | `c_times_quotient_upper` (45 cols, `MulGadget`) |
| 138..145  | `remainder_lt_gadget` (8 cols, `LtWordU16Gadget`) |
| 146..149  | `c_neg_gadget` (4 cols, `AddGadget`) |
| 150..153  | `rem_neg_gadget` (4 cols, `AddGadget`) |
| 154..161  | `carry_0..7`                     |
| 162..172  | `is_c_0` (11 cols, `IsZeroWordGadget`) |
| 173..180  | `is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw` |
| 181       | `is_overflow`                    |
| 182..192  | `is_overflow_b` (11 cols, `IsEqualWordGadget`) |
| 193..203  | `is_overflow_c` (11 cols, `IsEqualWordGadget`) |
| 204       | `b_msb.msb`                      |
| 205       | `rem_msb.msb`                    |
| 206       | `c_msb.msb`                      |
| 207       | `quot_msb.msb`                   |
| 208       | `b_neg`                          |
| 209       | `b_neg_not_overflow`             |
| 210       | `b_not_neg_not_overflow`         |
| 211       | `is_real_not_word`               |
| 212       | `rem_neg`                        |
| 213       | `c_neg`                          |
| 214       | `abs_c_alu_event`                |
| 215       | `abs_rem_alu_event`              |
| 216       | `is_real`                        |
| 217       | `remainder_check_multiplicity`   |
-/

namespace DivRemChip.ConstraintsAndBuses

  open RV64IM_Interactions

  variable [Field F] [Field ExtF]

  /-- The conjunction of algebraic facts `DivRemChip` asserts per row.
      Structured to mirror the seven sections of the Pico Rust
      `eval`: helper definitions (word-op flags, sign-type),
      `is_real_not_word`, MSB-sign pairings, `quotient_comp` /
      `remainder_comp` setup, embedded `MulGadget`×2, embedded
      `IsEqualWordGadget`×4 + `is_overflow`/`b_neg_not_overflow`/
      `b_not_neg_not_overflow` + overflow-case clamping,
      `c·quotient + remainder = b` 8-byte carry chain, `a = quotient`
      / `a = remainder`, sign-consistency, `IsZeroWordGadget` +
      division-by-zero clamps, abs-value reconstructions + embedded
      `AddGadget`×2 + `LtWordU16Gadget`, MSB consistency
      (`U16MSBGadget`×3 in each of two gated modes), boolean checks
      on all flags + carry bits, and the at-most-one selector. -/
  @[constraint_and_interaction_simplification]
  def AbsConstraints (air : Valid_DivRemChip F ExtF) (row : ℕ) : Prop :=
    -- =====================================================================
    -- Column accessors (one per column under `air.cols.values`).
    -- =====================================================================
    let a_0  := air.cols.values.a_0  row 0
    let a_1  := air.cols.values.a_1  row 0
    let a_2  := air.cols.values.a_2  row 0
    let a_3  := air.cols.values.a_3  row 0
    let b_0  := air.cols.values.b_0  row 0
    let b_1  := air.cols.values.b_1  row 0
    let b_2  := air.cols.values.b_2  row 0
    let b_3  := air.cols.values.b_3  row 0
    let c_0  := air.cols.values.c_0  row 0
    let c_1  := air.cols.values.c_1  row 0
    let c_2  := air.cols.values.c_2  row 0
    let c_3  := air.cols.values.c_3  row 0
    let q_0  := air.cols.values.quotient_0 row 0
    let q_1  := air.cols.values.quotient_1 row 0
    let q_2  := air.cols.values.quotient_2 row 0
    let q_3  := air.cols.values.quotient_3 row 0
    let qc_0 := air.cols.values.quotient_comp_0 row 0
    let qc_1 := air.cols.values.quotient_comp_1 row 0
    let qc_2 := air.cols.values.quotient_comp_2 row 0
    let qc_3 := air.cols.values.quotient_comp_3 row 0
    let rc_0 := air.cols.values.remainder_comp_0 row 0
    let rc_1 := air.cols.values.remainder_comp_1 row 0
    let rc_2 := air.cols.values.remainder_comp_2 row 0
    let rc_3 := air.cols.values.remainder_comp_3 row 0
    let r_0  := air.cols.values.remainder_0 row 0
    let r_1  := air.cols.values.remainder_1 row 0
    let r_2  := air.cols.values.remainder_2 row 0
    let r_3  := air.cols.values.remainder_3 row 0
    let ar_0 := air.cols.values.abs_remainder_0 row 0
    let ar_1 := air.cols.values.abs_remainder_1 row 0
    let ar_2 := air.cols.values.abs_remainder_2 row 0
    let ar_3 := air.cols.values.abs_remainder_3 row 0
    let ac_0 := air.cols.values.abs_c_0 row 0
    let ac_1 := air.cols.values.abs_c_1 row 0
    let ac_2 := air.cols.values.abs_c_2 row 0
    let ac_3 := air.cols.values.abs_c_3 row 0
    let mc_0 := air.cols.values.max_abs_c_or_1_0 row 0
    let mc_1 := air.cols.values.max_abs_c_or_1_1 row 0
    let mc_2 := air.cols.values.max_abs_c_or_1_2 row 0
    let mc_3 := air.cols.values.max_abs_c_or_1_3 row 0
    let cq_0 := air.cols.values.c_times_quotient_0 row 0
    let cq_1 := air.cols.values.c_times_quotient_1 row 0
    let cq_2 := air.cols.values.c_times_quotient_2 row 0
    let cq_3 := air.cols.values.c_times_quotient_3 row 0
    let cq_4 := air.cols.values.c_times_quotient_4 row 0
    let cq_5 := air.cols.values.c_times_quotient_5 row 0
    let cq_6 := air.cols.values.c_times_quotient_6 row 0
    let cq_7 := air.cols.values.c_times_quotient_7 row 0
    let cy_0 := air.cols.values.carry_0 row 0
    let cy_1 := air.cols.values.carry_1 row 0
    let cy_2 := air.cols.values.carry_2 row 0
    let cy_3 := air.cols.values.carry_3 row 0
    let cy_4 := air.cols.values.carry_4 row 0
    let cy_5 := air.cols.values.carry_5 row 0
    let cy_6 := air.cols.values.carry_6 row 0
    let cy_7 := air.cols.values.carry_7 row 0
    let is_div    := air.cols.values.is_div    row 0
    let is_divu   := air.cols.values.is_divu   row 0
    let is_rem    := air.cols.values.is_rem    row 0
    let is_remu   := air.cols.values.is_remu   row 0
    let is_divw   := air.cols.values.is_divw   row 0
    let is_remw   := air.cols.values.is_remw   row 0
    let is_divuw  := air.cols.values.is_divuw  row 0
    let is_remuw  := air.cols.values.is_remuw  row 0
    let is_overflow := air.cols.values.is_overflow row 0
    let b_msb     := air.cols.values.b_msb.msb     row 0
    let rem_msb   := air.cols.values.rem_msb.msb   row 0
    let c_msb     := air.cols.values.c_msb.msb     row 0
    let _quot_msb := air.cols.values.quot_msb.msb  row 0
    let b_neg     := air.cols.values.b_neg     row 0
    let b_neg_not_overflow     := air.cols.values.b_neg_not_overflow     row 0
    let b_not_neg_not_overflow := air.cols.values.b_not_neg_not_overflow row 0
    let is_real_not_word := air.cols.values.is_real_not_word row 0
    let rem_neg := air.cols.values.rem_neg row 0
    let c_neg   := air.cols.values.c_neg   row 0
    let abs_c_alu_event   := air.cols.values.abs_c_alu_event   row 0
    let abs_rem_alu_event := air.cols.values.abs_rem_alu_event row 0
    let is_real := air.cols.values.is_real row 0
    let remainder_check_multiplicity :=
      air.cols.values.remainder_check_multiplicity row 0
    -- =====================================================================
    -- Helper expressions (lets — not constraints).
    -- =====================================================================
    let is_word_operation          := is_divw + is_remw + is_divuw + is_remuw
    let is_unsigned_word_operation := is_divuw + is_remuw
    let is_signed_word_operation   := is_divw + is_remw
    let is_not_word_operation      := 1 - is_word_operation
    let is_signed_type             := is_div + is_rem + is_divw + is_remw
    -- =====================================================================
    -- The conjunction.
    -- =====================================================================
    -- ---------------------------------------------------------------------
    -- (1) `is_real_not_word = is_real * (1 - is_word_operation)`.
    -- ---------------------------------------------------------------------
    (is_real_not_word - is_real * is_not_word_operation = 0) ∧
    -- ---------------------------------------------------------------------
    -- (2) MSB-sign pairings: for each of `b`, `rem`, `c`,
    --     `msb · is_signed_type = is_negative`.
    -- ---------------------------------------------------------------------
    (b_msb   * is_signed_type - b_neg   = 0) ∧
    (rem_msb * is_signed_type - rem_neg = 0) ∧
    (c_msb   * is_signed_type - c_neg   = 0) ∧
    -- ---------------------------------------------------------------------
    -- (3) `quotient_comp` setup.
    --     Lower 2 limbs (i = 0,1): `qc_i = q_i` unconditionally.
    --     Upper 2 limbs (i = 2,3) — four conditional clauses each.
    -- ---------------------------------------------------------------------
    (qc_0 - q_0 = 0) ∧
    (qc_1 - q_1 = 0) ∧
    (is_unsigned_word_operation * (qc_2 - 0)                 = 0) ∧
    (is_signed_word_operation   * (qc_2 - _quot_msb * 65535) = 0) ∧
    (is_word_operation          * (q_2  - _quot_msb * 65535) = 0) ∧
    (is_not_word_operation      * (qc_2 - q_2)               = 0) ∧
    (is_unsigned_word_operation * (qc_3 - 0)                 = 0) ∧
    (is_signed_word_operation   * (qc_3 - _quot_msb * 65535) = 0) ∧
    (is_word_operation          * (q_3  - _quot_msb * 65535) = 0) ∧
    (is_not_word_operation      * (qc_3 - q_3)               = 0) ∧
    -- ---------------------------------------------------------------------
    -- (4) `remainder_comp` setup — mirror of (3) but with `rem_msb` /
    --     `remainder_comp` / `remainder`.
    -- ---------------------------------------------------------------------
    (rc_0 - r_0 = 0) ∧
    (rc_1 - r_1 = 0) ∧
    (is_unsigned_word_operation * (rc_2 - 0)               = 0) ∧
    (is_signed_word_operation   * (rc_2 - rem_msb * 65535) = 0) ∧
    (is_word_operation          * (r_2  - rem_msb * 65535) = 0) ∧
    (is_not_word_operation      * (rc_2 - r_2)             = 0) ∧
    (is_unsigned_word_operation * (rc_3 - 0)               = 0) ∧
    (is_signed_word_operation   * (rc_3 - rem_msb * 65535) = 0) ∧
    (is_word_operation          * (r_3  - rem_msb * 65535) = 0) ∧
    (is_not_word_operation      * (rc_3 - r_3)             = 0) ∧
    -- ---------------------------------------------------------------------
    -- (5) `MulGadget` lower half: `(cq_0..3) = c · quotient_comp` low 64
    --     bits, gated by `is_real`. Selectors: `is_mul = is_real`, all
    --     other MUL-family flags = 0.
    -- ---------------------------------------------------------------------
    MulGadget.AbsConstraints
      is_real  is_real  0  0  0  0
      cq_0 cq_1 cq_2 cq_3
      qc_0 qc_1 qc_2 qc_3
      c_0  c_1  c_2  c_3
      (air.cols.values.c_times_quotient_lower.carry_0  row 0)
      (air.cols.values.c_times_quotient_lower.carry_1  row 0)
      (air.cols.values.c_times_quotient_lower.carry_2  row 0)
      (air.cols.values.c_times_quotient_lower.carry_3  row 0)
      (air.cols.values.c_times_quotient_lower.carry_4  row 0)
      (air.cols.values.c_times_quotient_lower.carry_5  row 0)
      (air.cols.values.c_times_quotient_lower.carry_6  row 0)
      (air.cols.values.c_times_quotient_lower.carry_7  row 0)
      (air.cols.values.c_times_quotient_lower.carry_8  row 0)
      (air.cols.values.c_times_quotient_lower.carry_9  row 0)
      (air.cols.values.c_times_quotient_lower.carry_10 row 0)
      (air.cols.values.c_times_quotient_lower.carry_11 row 0)
      (air.cols.values.c_times_quotient_lower.carry_12 row 0)
      (air.cols.values.c_times_quotient_lower.carry_13 row 0)
      (air.cols.values.c_times_quotient_lower.carry_14 row 0)
      (air.cols.values.c_times_quotient_lower.carry_15 row 0)
      (air.cols.values.c_times_quotient_lower.product_0  row 0)
      (air.cols.values.c_times_quotient_lower.product_1  row 0)
      (air.cols.values.c_times_quotient_lower.product_2  row 0)
      (air.cols.values.c_times_quotient_lower.product_3  row 0)
      (air.cols.values.c_times_quotient_lower.product_4  row 0)
      (air.cols.values.c_times_quotient_lower.product_5  row 0)
      (air.cols.values.c_times_quotient_lower.product_6  row 0)
      (air.cols.values.c_times_quotient_lower.product_7  row 0)
      (air.cols.values.c_times_quotient_lower.product_8  row 0)
      (air.cols.values.c_times_quotient_lower.product_9  row 0)
      (air.cols.values.c_times_quotient_lower.product_10 row 0)
      (air.cols.values.c_times_quotient_lower.product_11 row 0)
      (air.cols.values.c_times_quotient_lower.product_12 row 0)
      (air.cols.values.c_times_quotient_lower.product_13 row 0)
      (air.cols.values.c_times_quotient_lower.product_14 row 0)
      (air.cols.values.c_times_quotient_lower.product_15 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_lower.b_msb row 0)
      (air.cols.values.c_times_quotient_lower.c_msb row 0)
      (air.cols.values.c_times_quotient_lower.product_msb.msb row 0)
      (air.cols.values.c_times_quotient_lower.b_sign_extend row 0)
      (air.cols.values.c_times_quotient_lower.c_sign_extend row 0)
    ∧
    -- ---------------------------------------------------------------------
    -- (6) `MulGadget` upper half: `(cq_4..7) = c · quotient_comp` high
    --     64 bits, gated by `is_real_not_word`. Selectors:
    --     `is_mulh = is_div + is_rem`, `is_mulhu = is_divu + is_remu`,
    --     others = 0. (No upper-half multiplication is asserted for word
    --     ops — those work entirely in the low 64 bits.)
    -- ---------------------------------------------------------------------
    MulGadget.AbsConstraints
      is_real_not_word  0  (is_div + is_rem)  0  (is_divu + is_remu)  0
      cq_4 cq_5 cq_6 cq_7
      qc_0 qc_1 qc_2 qc_3
      c_0  c_1  c_2  c_3
      (air.cols.values.c_times_quotient_upper.carry_0  row 0)
      (air.cols.values.c_times_quotient_upper.carry_1  row 0)
      (air.cols.values.c_times_quotient_upper.carry_2  row 0)
      (air.cols.values.c_times_quotient_upper.carry_3  row 0)
      (air.cols.values.c_times_quotient_upper.carry_4  row 0)
      (air.cols.values.c_times_quotient_upper.carry_5  row 0)
      (air.cols.values.c_times_quotient_upper.carry_6  row 0)
      (air.cols.values.c_times_quotient_upper.carry_7  row 0)
      (air.cols.values.c_times_quotient_upper.carry_8  row 0)
      (air.cols.values.c_times_quotient_upper.carry_9  row 0)
      (air.cols.values.c_times_quotient_upper.carry_10 row 0)
      (air.cols.values.c_times_quotient_upper.carry_11 row 0)
      (air.cols.values.c_times_quotient_upper.carry_12 row 0)
      (air.cols.values.c_times_quotient_upper.carry_13 row 0)
      (air.cols.values.c_times_quotient_upper.carry_14 row 0)
      (air.cols.values.c_times_quotient_upper.carry_15 row 0)
      (air.cols.values.c_times_quotient_upper.product_0  row 0)
      (air.cols.values.c_times_quotient_upper.product_1  row 0)
      (air.cols.values.c_times_quotient_upper.product_2  row 0)
      (air.cols.values.c_times_quotient_upper.product_3  row 0)
      (air.cols.values.c_times_quotient_upper.product_4  row 0)
      (air.cols.values.c_times_quotient_upper.product_5  row 0)
      (air.cols.values.c_times_quotient_upper.product_6  row 0)
      (air.cols.values.c_times_quotient_upper.product_7  row 0)
      (air.cols.values.c_times_quotient_upper.product_8  row 0)
      (air.cols.values.c_times_quotient_upper.product_9  row 0)
      (air.cols.values.c_times_quotient_upper.product_10 row 0)
      (air.cols.values.c_times_quotient_upper.product_11 row 0)
      (air.cols.values.c_times_quotient_upper.product_12 row 0)
      (air.cols.values.c_times_quotient_upper.product_13 row 0)
      (air.cols.values.c_times_quotient_upper.product_14 row 0)
      (air.cols.values.c_times_quotient_upper.product_15 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_upper.b_msb row 0)
      (air.cols.values.c_times_quotient_upper.c_msb row 0)
      (air.cols.values.c_times_quotient_upper.product_msb.msb row 0)
      (air.cols.values.c_times_quotient_upper.b_sign_extend row 0)
      (air.cols.values.c_times_quotient_upper.c_sign_extend row 0)
    ∧
    -- ---------------------------------------------------------------------
    -- (7a) `IsEqualWordGadget`s for the overflow predicates.
    --      64-bit: `b == i64::MIN = #v[0, 0, 0, 0x8000]` and `c == -1 =
    --      #v[0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF]` (gated by `is_real_not_word`).
    -- ---------------------------------------------------------------------
    IsEqualWordGadget.AbsConstraints
      is_real_not_word
      b_0 b_1 b_2 b_3
      0 0 0 32768
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_0.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_1.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_2.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_3.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_0.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_1.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_2.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_3.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_lower_half_zero row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_upper_half_zero row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.result row 0)
    ∧
    IsEqualWordGadget.AbsConstraints
      is_real_not_word
      c_0 c_1 c_2 c_3
      65535 65535 65535 65535
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_0.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_1.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_2.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_3.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_0.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_1.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_2.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_3.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_lower_half_zero row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_upper_half_zero row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.result row 0)
    ∧
    -- ---------------------------------------------------------------------
    -- (7b) Same `is_overflow_b` / `is_overflow_c` gadgets, gated by
    --      `is_word_operation`, with the *32-bit truncated* operands
    --      compared against `i32::MIN = #v[0, 0x8000, 0, 0]` (low 32 only)
    --      and `-1 = #v[0xFFFF, 0xFFFF, 0, 0]`. The chip reuses the same
    --      gadget columns under a different gate.
    -- ---------------------------------------------------------------------
    IsEqualWordGadget.AbsConstraints
      is_word_operation
      b_0 b_1 0 0
      0 32768 0 0
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_0.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_1.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_2.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_3.inverse row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_0.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_1.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_2.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_zero_byte_3.result row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_lower_half_zero row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.is_upper_half_zero row 0)
      (air.cols.values.is_overflow_b.is_diff_zero.result row 0)
    ∧
    IsEqualWordGadget.AbsConstraints
      is_word_operation
      c_0 c_1 0 0
      65535 65535 0 0
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_0.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_1.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_2.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_3.inverse row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_0.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_1.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_2.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_zero_byte_3.result row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_lower_half_zero row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.is_upper_half_zero row 0)
      (air.cols.values.is_overflow_c.is_diff_zero.result row 0)
    ∧
    -- ---------------------------------------------------------------------
    -- (7c) `is_overflow = is_overflow_b · is_overflow_c · is_signed_type`,
    --      `b_neg_not_overflow`, `b_not_neg_not_overflow`.
    -- ---------------------------------------------------------------------
    (is_overflow -
       (air.cols.values.is_overflow_b.is_diff_zero.result row 0)
       * (air.cols.values.is_overflow_c.is_diff_zero.result row 0)
       * is_signed_type = 0) ∧
    (b_neg_not_overflow     - b_neg       * (1 - is_overflow) = 0) ∧
    (b_not_neg_not_overflow - (1 - b_neg) * (1 - is_overflow) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (7d) Overflow case clamp: when `is_overflow = 1`, force
    --      `quotient[i] = b[i]` and `remainder[i] = 0`.
    -- ---------------------------------------------------------------------
    (is_overflow * (q_0 - b_0) = 0) ∧
    (is_overflow * (r_0 - 0)   = 0) ∧
    (is_overflow * (q_1 - b_1) = 0) ∧
    (is_overflow * (r_1 - 0)   = 0) ∧
    (is_overflow * (q_2 - b_2) = 0) ∧
    (is_overflow * (r_2 - 0)   = 0) ∧
    (is_overflow * (q_3 - b_3) = 0) ∧
    (is_overflow * (r_3 - 0)   = 0) ∧
    -- ---------------------------------------------------------------------
    -- (8) `b = c · quotient + remainder` carry-chain. For each
    --     `i ∈ 0..LONG_WORD_SIZE = 8`:
    --       cqr[i] := c_times_quotient[i] + (rc[i] if i<4 else rem_neg·0xFFFF)
    --                 - carry[i]·base + (carry[i-1] if i>0 else 0)
    --     and (when not overflow):
    --       i < 4 → b[i] = cqr[i]
    --       i ≥ 4 → b_neg·0xFFFF = cqr[i]
    --     where base = 2^16.
    -- ---------------------------------------------------------------------
    let base : F := 65536
    let sign_ext := rem_neg * 65535
    let cqr_0 := cq_0 + rc_0      - cy_0 * base
    let cqr_1 := cq_1 + rc_1      - cy_1 * base + cy_0
    let cqr_2 := cq_2 + rc_2      - cy_2 * base + cy_1
    let cqr_3 := cq_3 + rc_3      - cy_3 * base + cy_2
    let cqr_4 := cq_4 + sign_ext  - cy_4 * base + cy_3
    let cqr_5 := cq_5 + sign_ext  - cy_5 * base + cy_4
    let cqr_6 := cq_6 + sign_ext  - cy_6 * base + cy_5
    let cqr_7 := cq_7 + sign_ext  - cy_7 * base + cy_6
    ((is_overflow - 1) * (b_0 - cqr_0) = 0) ∧
    ((is_overflow - 1) * (b_1 - cqr_1) = 0) ∧
    ((is_overflow - 1) * (b_2 - cqr_2) = 0) ∧
    ((is_overflow - 1) * (b_3 - cqr_3) = 0) ∧
    ((is_overflow - 1) * (b_neg * 65535 - cqr_4) = 0) ∧
    ((is_overflow - 1) * (b_neg * 65535 - cqr_5) = 0) ∧
    ((is_overflow - 1) * (b_neg * 65535 - cqr_6) = 0) ∧
    ((is_overflow - 1) * (b_neg * 65535 - cqr_7) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (9) `a = quotient` or `a = remainder` per opcode.
    -- ---------------------------------------------------------------------
    let div_active := is_divu + is_div + is_divuw + is_divw
    let rem_active := is_remu + is_rem + is_remuw + is_remw
    (div_active * (q_0 - a_0) = 0) ∧
    (rem_active * (r_0 - a_0) = 0) ∧
    (div_active * (q_1 - a_1) = 0) ∧
    (rem_active * (r_1 - a_1) = 0) ∧
    (div_active * (q_2 - a_2) = 0) ∧
    (rem_active * (r_2 - a_2) = 0) ∧
    (div_active * (q_3 - a_3) = 0) ∧
    (rem_active * (r_3 - a_3) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (10) Sign consistency between `remainder` and `b`.
    --      • `rem_neg → b_neg = 1` (Rust: `when(rem_neg).assert_one(b_neg)`)
    --      • `(remainder ≠ 0) ∧ (¬rem_neg) → b_neg = 0`
    -- ---------------------------------------------------------------------
    (rem_neg * (b_neg - 1) = 0) ∧
    ((r_0 + r_1 + r_2 + r_3) * (1 - rem_neg) * b_neg = 0) ∧
    -- ---------------------------------------------------------------------
    -- (11) `IsZeroWordGadget` on `c`, gated by `is_real`.
    -- ---------------------------------------------------------------------
    IsZeroWordGadget.AbsConstraints
      is_real
      c_0 c_1 c_2 c_3
      (air.cols.values.is_c_0.is_zero_byte_0.inverse row 0)
      (air.cols.values.is_c_0.is_zero_byte_1.inverse row 0)
      (air.cols.values.is_c_0.is_zero_byte_2.inverse row 0)
      (air.cols.values.is_c_0.is_zero_byte_3.inverse row 0)
      (air.cols.values.is_c_0.is_zero_byte_0.result row 0)
      (air.cols.values.is_c_0.is_zero_byte_1.result row 0)
      (air.cols.values.is_c_0.is_zero_byte_2.result row 0)
      (air.cols.values.is_c_0.is_zero_byte_3.result row 0)
      (air.cols.values.is_c_0.is_lower_half_zero row 0)
      (air.cols.values.is_c_0.is_upper_half_zero row 0)
      (air.cols.values.is_c_0.result row 0)
    ∧
    let is_c_0_result := air.cols.values.is_c_0.result row 0
    -- ---------------------------------------------------------------------
    -- (12) Division-by-zero clamps: `is_c_0 → quotient = u64::MAX` (i.e.
    --      every limb = `0xFFFF`) and `remainder_comp = b`.
    -- ---------------------------------------------------------------------
    (is_c_0_result * (q_0 - 65535) = 0) ∧
    (is_c_0_result * (q_1 - 65535) = 0) ∧
    (is_c_0_result * (q_2 - 65535) = 0) ∧
    (is_c_0_result * (q_3 - 65535) = 0) ∧
    (is_c_0_result * (rc_0 - b_0) = 0) ∧
    (is_c_0_result * (rc_1 - b_1) = 0) ∧
    (is_c_0_result * (rc_2 - b_2) = 0) ∧
    (is_c_0_result * (rc_3 - b_3) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (13) `abs(c) = c` when `¬c_neg`; `abs(remainder) = remainder` when
    --      `¬rem_neg`. (The negative case is handled by the
    --      `AddGadget`s below — they verify `c + abs_c = 0` etc.)
    -- ---------------------------------------------------------------------
    ((c_neg - 1) * (c_0 - ac_0) = 0) ∧
    ((rem_neg - 1) * (r_0 - ar_0) = 0) ∧
    ((c_neg - 1) * (c_1 - ac_1) = 0) ∧
    ((rem_neg - 1) * (r_1 - ar_1) = 0) ∧
    ((c_neg - 1) * (c_2 - ac_2) = 0) ∧
    ((rem_neg - 1) * (r_2 - ar_2) = 0) ∧
    ((c_neg - 1) * (c_3 - ac_3) = 0) ∧
    ((rem_neg - 1) * (r_3 - ar_3) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (14) `max_abs_c_or_1 = max(abs_c, 1)`. The least significant limb
    --      gets `1` when `is_c_0`, the rest get `0`; otherwise `abs_c`.
    -- ---------------------------------------------------------------------
    (mc_0 - (is_c_0_result + (1 - is_c_0_result) * ac_0) = 0) ∧
    (mc_1 - (1 - is_c_0_result) * ac_1 = 0) ∧
    (mc_2 - (1 - is_c_0_result) * ac_2 = 0) ∧
    (mc_3 - (1 - is_c_0_result) * ac_3 = 0) ∧
    -- ---------------------------------------------------------------------
    -- (15) `remainder_check_multiplicity = (1 - is_c_0) · is_real` and
    --      the two abs-value ALU event selectors.
    -- ---------------------------------------------------------------------
    ((1 - is_c_0_result) * is_real - remainder_check_multiplicity = 0) ∧
    (abs_c_alu_event   - c_neg   * is_real = 0) ∧
    (abs_rem_alu_event - rem_neg * is_real = 0) ∧
    -- ---------------------------------------------------------------------
    -- (16) `AddGadget` instances verifying `c + abs_c = 0` (gated by
    --      `abs_c_alu_event`) and `remainder_comp + abs_remainder = 0`
    --      (gated by `abs_rem_alu_event`). The `value` column of each
    --      gadget *is the sum that's asserted to be zero*; the
    --      sign-flipped operand sits implicitly in the gadget's carry
    --      chain.
    -- ---------------------------------------------------------------------
    AddGadget.AbsConstraints
      abs_c_alu_event
      c_0 c_1 c_2 c_3
      ac_0 ac_1 ac_2 ac_3
      (air.cols.values.c_neg_gadget.value_0 row 0)
      (air.cols.values.c_neg_gadget.value_1 row 0)
      (air.cols.values.c_neg_gadget.value_2 row 0)
      (air.cols.values.c_neg_gadget.value_3 row 0)
    ∧
    AddGadget.AbsConstraints
      abs_rem_alu_event
      rc_0 rc_1 rc_2 rc_3
      ar_0 ar_1 ar_2 ar_3
      (air.cols.values.rem_neg_gadget.value_0 row 0)
      (air.cols.values.rem_neg_gadget.value_1 row 0)
      (air.cols.values.rem_neg_gadget.value_2 row 0)
      (air.cols.values.rem_neg_gadget.value_3 row 0)
    ∧
    -- ---------------------------------------------------------------------
    -- (17) When the `_alu_event` flag is set, the `AddGadget`'s `value`
    --      output must be zero (so `c + abs_c = 0` resp.
    --      `remainder_comp + abs_remainder = 0` hold).
    -- ---------------------------------------------------------------------
    (abs_c_alu_event * (air.cols.values.c_neg_gadget.value_0 row 0) = 0) ∧
    (abs_c_alu_event * (air.cols.values.c_neg_gadget.value_1 row 0) = 0) ∧
    (abs_c_alu_event * (air.cols.values.c_neg_gadget.value_2 row 0) = 0) ∧
    (abs_c_alu_event * (air.cols.values.c_neg_gadget.value_3 row 0) = 0) ∧
    (abs_rem_alu_event * (air.cols.values.rem_neg_gadget.value_0 row 0) = 0) ∧
    (abs_rem_alu_event * (air.cols.values.rem_neg_gadget.value_1 row 0) = 0) ∧
    (abs_rem_alu_event * (air.cols.values.rem_neg_gadget.value_2 row 0) = 0) ∧
    (abs_rem_alu_event * (air.cols.values.rem_neg_gadget.value_3 row 0) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (18) `LtWordU16Gadget`: `abs_remainder < max_abs_c_or_1`, gated
    --      by `remainder_check_multiplicity`.
    -- ---------------------------------------------------------------------
    LtWordU16Gadget.AbsConstraints
      remainder_check_multiplicity
      ar_0 ar_1 ar_2 ar_3
      mc_0 mc_1 mc_2 mc_3
      (air.cols.values.remainder_lt_gadget.u16_flags_0 row 0)
      (air.cols.values.remainder_lt_gadget.u16_flags_1 row 0)
      (air.cols.values.remainder_lt_gadget.u16_flags_2 row 0)
      (air.cols.values.remainder_lt_gadget.u16_flags_3 row 0)
      (air.cols.values.remainder_lt_gadget.not_eq_inv row 0)
      (air.cols.values.remainder_lt_gadget.comparison_limbs_0 row 0)
      (air.cols.values.remainder_lt_gadget.comparison_limbs_1 row 0)
      (air.cols.values.remainder_lt_gadget.bit row 0)
    ∧
    -- ---------------------------------------------------------------------
    -- (18b) `LtWordU16Gadget` only enforces `bit ↔ (|rem| < max(|c|, 1))`
    --       (a consistency oracle); the chip separately pins
    --       `bit = 1` whenever the gadget fires, which is what actually
    --       enforces `|remainder| < |c|`. Added in Pico PR #101 at
    --       commit `0786b8b` after the Lean-side soundness audit.
    -- ---------------------------------------------------------------------
    (remainder_check_multiplicity *
       (air.cols.values.remainder_lt_gadget.bit row 0 - 1) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (19) `U16MSBGadget`s in two gated modes:
    --        • `is_real_not_word` ⇒ MSB of the top u16 limb (index 3)
    --        • `is_word_operation` ⇒ MSB of the middle u16 limb (index 1)
    --      for each of `b`, `c`, `rem`. The boolean checks duplicate
    --      across modes; the bus side enforces the actual top-bit
    --      relation.
    -- ---------------------------------------------------------------------
    U16MSBGadget.AbsConstraints is_real_not_word b_msb ∧
    U16MSBGadget.AbsConstraints is_real_not_word c_msb ∧
    U16MSBGadget.AbsConstraints is_real_not_word rem_msb ∧
    U16MSBGadget.AbsConstraints is_word_operation b_msb ∧
    U16MSBGadget.AbsConstraints is_word_operation c_msb ∧
    U16MSBGadget.AbsConstraints is_word_operation rem_msb ∧
    -- ---------------------------------------------------------------------
    -- (20) Boolean checks: 8 carry bits + 8 selectors + `is_overflow`,
    --      `is_real_not_word`, `b_neg`, `b_neg_not_overflow`,
    --      `b_not_neg_not_overflow`, `rem_neg`, `c_neg`, `is_real`,
    --      `abs_c_alu_event`, `abs_rem_alu_event` (= 18 bools),
    --      plus 8 carry bits.
    -- ---------------------------------------------------------------------
    (cy_0 * (cy_0 - 1) = 0) ∧
    (cy_1 * (cy_1 - 1) = 0) ∧
    (cy_2 * (cy_2 - 1) = 0) ∧
    (cy_3 * (cy_3 - 1) = 0) ∧
    (cy_4 * (cy_4 - 1) = 0) ∧
    (cy_5 * (cy_5 - 1) = 0) ∧
    (cy_6 * (cy_6 - 1) = 0) ∧
    (cy_7 * (cy_7 - 1) = 0) ∧
    (is_div    * (is_div    - 1) = 0) ∧
    (is_divu   * (is_divu   - 1) = 0) ∧
    (is_rem    * (is_rem    - 1) = 0) ∧
    (is_remu   * (is_remu   - 1) = 0) ∧
    (is_divw   * (is_divw   - 1) = 0) ∧
    (is_remw   * (is_remw   - 1) = 0) ∧
    (is_divuw  * (is_divuw  - 1) = 0) ∧
    (is_remuw  * (is_remuw  - 1) = 0) ∧
    (is_overflow * (is_overflow - 1) = 0) ∧
    (is_real_not_word * (is_real_not_word - 1) = 0) ∧
    (b_neg * (b_neg - 1) = 0) ∧
    (b_neg_not_overflow     * (b_neg_not_overflow     - 1) = 0) ∧
    (b_not_neg_not_overflow * (b_not_neg_not_overflow - 1) = 0) ∧
    (rem_neg * (rem_neg - 1) = 0) ∧
    (c_neg   * (c_neg   - 1) = 0) ∧
    (is_real * (is_real - 1) = 0) ∧
    (abs_c_alu_event   * (abs_c_alu_event   - 1) = 0) ∧
    (abs_rem_alu_event * (abs_rem_alu_event - 1) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (21) Exactly one of the eight opcode selectors is set.
    -- ---------------------------------------------------------------------
    (1 - (is_divu + is_remu + is_div + is_rem
          + is_divw + is_remw + is_divuw + is_remuw) = 0)

  /-- `AbsConstraints` with all 11 sub-gadget `AbsConstraints` calls
      stripped out (`MulGadget × 2`, `IsEqualWordGadget × 4`,
      `IsZeroWordGadget`, `AddGadget × 2`, `LtWordU16Gadget`,
      `U16MSBGadget × 6`).

      Kept in the same section order as `AbsConstraints`. This is the
      "what's left after the gadget specs have been applied" side of
      `gadget_specs_pack`: the gadget AbsConstraints become spec
      conclusions (`ALUBus.Spec`, `result ↔ word_eq`, etc.) and
      `AbsConstraints_NoGadgets` carries the chip-own algebraic facts
      (sign pairings, `quotient_comp` / `remainder_comp` setup,
      overflow predicates, the 8-byte carry chain, `a = q/r`,
      div-by-zero clamps, abs-value reconstructions, boolean checks,
      and the exact-one-selector constraint). -/
  def AbsConstraints_NoGadgets (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : Prop :=
    let a_0  := air.cols.values.a_0  row 0
    let a_1  := air.cols.values.a_1  row 0
    let a_2  := air.cols.values.a_2  row 0
    let a_3  := air.cols.values.a_3  row 0
    let b_0  := air.cols.values.b_0  row 0
    let b_1  := air.cols.values.b_1  row 0
    let b_2  := air.cols.values.b_2  row 0
    let b_3  := air.cols.values.b_3  row 0
    let c_0  := air.cols.values.c_0  row 0
    let c_1  := air.cols.values.c_1  row 0
    let c_2  := air.cols.values.c_2  row 0
    let c_3  := air.cols.values.c_3  row 0
    let q_0  := air.cols.values.quotient_0 row 0
    let q_1  := air.cols.values.quotient_1 row 0
    let q_2  := air.cols.values.quotient_2 row 0
    let q_3  := air.cols.values.quotient_3 row 0
    let qc_0 := air.cols.values.quotient_comp_0 row 0
    let qc_1 := air.cols.values.quotient_comp_1 row 0
    let qc_2 := air.cols.values.quotient_comp_2 row 0
    let qc_3 := air.cols.values.quotient_comp_3 row 0
    let rc_0 := air.cols.values.remainder_comp_0 row 0
    let rc_1 := air.cols.values.remainder_comp_1 row 0
    let rc_2 := air.cols.values.remainder_comp_2 row 0
    let rc_3 := air.cols.values.remainder_comp_3 row 0
    let r_0  := air.cols.values.remainder_0 row 0
    let r_1  := air.cols.values.remainder_1 row 0
    let r_2  := air.cols.values.remainder_2 row 0
    let r_3  := air.cols.values.remainder_3 row 0
    let ar_0 := air.cols.values.abs_remainder_0 row 0
    let ar_1 := air.cols.values.abs_remainder_1 row 0
    let ar_2 := air.cols.values.abs_remainder_2 row 0
    let ar_3 := air.cols.values.abs_remainder_3 row 0
    let ac_0 := air.cols.values.abs_c_0 row 0
    let ac_1 := air.cols.values.abs_c_1 row 0
    let ac_2 := air.cols.values.abs_c_2 row 0
    let ac_3 := air.cols.values.abs_c_3 row 0
    let mc_0 := air.cols.values.max_abs_c_or_1_0 row 0
    let mc_1 := air.cols.values.max_abs_c_or_1_1 row 0
    let mc_2 := air.cols.values.max_abs_c_or_1_2 row 0
    let mc_3 := air.cols.values.max_abs_c_or_1_3 row 0
    let cq_0 := air.cols.values.c_times_quotient_0 row 0
    let cq_1 := air.cols.values.c_times_quotient_1 row 0
    let cq_2 := air.cols.values.c_times_quotient_2 row 0
    let cq_3 := air.cols.values.c_times_quotient_3 row 0
    let cq_4 := air.cols.values.c_times_quotient_4 row 0
    let cq_5 := air.cols.values.c_times_quotient_5 row 0
    let cq_6 := air.cols.values.c_times_quotient_6 row 0
    let cq_7 := air.cols.values.c_times_quotient_7 row 0
    let cy_0 := air.cols.values.carry_0 row 0
    let cy_1 := air.cols.values.carry_1 row 0
    let cy_2 := air.cols.values.carry_2 row 0
    let cy_3 := air.cols.values.carry_3 row 0
    let cy_4 := air.cols.values.carry_4 row 0
    let cy_5 := air.cols.values.carry_5 row 0
    let cy_6 := air.cols.values.carry_6 row 0
    let cy_7 := air.cols.values.carry_7 row 0
    let is_div    := air.cols.values.is_div    row 0
    let is_divu   := air.cols.values.is_divu   row 0
    let is_rem    := air.cols.values.is_rem    row 0
    let is_remu   := air.cols.values.is_remu   row 0
    let is_divw   := air.cols.values.is_divw   row 0
    let is_remw   := air.cols.values.is_remw   row 0
    let is_divuw  := air.cols.values.is_divuw  row 0
    let is_remuw  := air.cols.values.is_remuw  row 0
    let is_overflow := air.cols.values.is_overflow row 0
    let b_msb := air.cols.values.b_msb.msb     row 0
    let r_msb := air.cols.values.rem_msb.msb   row 0
    let c_msb := air.cols.values.c_msb.msb     row 0
    let q_msb := air.cols.values.quot_msb.msb  row 0
    let b_neg := air.cols.values.b_neg row 0
    let b_neg_not_overflow     := air.cols.values.b_neg_not_overflow     row 0
    let b_not_neg_not_overflow := air.cols.values.b_not_neg_not_overflow row 0
    let is_real_not_word := air.cols.values.is_real_not_word row 0
    let rem_neg := air.cols.values.rem_neg row 0
    let c_neg   := air.cols.values.c_neg   row 0
    let abs_c_alu_event   := air.cols.values.abs_c_alu_event   row 0
    let abs_rem_alu_event := air.cols.values.abs_rem_alu_event row 0
    let is_real := air.cols.values.is_real row 0
    let remainder_check_multiplicity :=
      air.cols.values.remainder_check_multiplicity row 0
    let is_word_operation          := is_divw + is_remw + is_divuw + is_remuw
    let is_unsigned_word_operation := is_divuw + is_remuw
    let is_signed_word_operation   := is_divw + is_remw
    let is_not_word_operation      := 1 - is_word_operation
    let is_signed_type             := is_div + is_rem + is_divw + is_remw
    -- (1) is_real_not_word definition.
    (is_real_not_word = is_real * is_not_word_operation) ∧
    -- (2) MSB-sign pairings × 3.
    (b_neg   = if (is_signed_type = 1) then b_msb else 0) ∧
    (rem_neg = if (is_signed_type = 1) then r_msb else 0) ∧
    (c_neg   = if (is_signed_type = 1) then c_msb else 0) ∧
    -- (3) quotient_comp setup.
    (qc_0 = q_0) ∧ (qc_1 = q_1) ∧
    (rc_0 = r_0) ∧ (rc_1 = r_1) ∧
    (is_unsigned_word_operation = 1 → qc_2 = 0 ∧ qc_3 = 0 ∧ rc_2 = 0 ∧ rc_3 = 0) ∧
    (is_signed_word_operation = 1 → qc_2 = q_msb * 65535 ∧ qc_3 = q_msb * 65535 ∧ rc_2 = r_msb * 65535 ∧ rc_3 = r_msb * 65535) ∧
    (is_word_operation = 1 → q_2 = q_msb * 65535 ∧ q_3 = q_msb * 65535 ∧ r_2 = r_msb * 65535 ∧ r_3 = r_msb * 65535) ∧
    (is_not_word_operation = 1 → qc_2 = q_2 ∧ qc_3 = q_3 ∧ rc_2 = r_2 ∧ rc_3 = r_3) ∧
    -- (7c) is_overflow definition + b_neg_not_overflow + b_not_neg_not_overflow.
    (is_overflow =
      is_signed_type *
      (air.cols.values.is_overflow_b.is_diff_zero.result row 0) *
      (air.cols.values.is_overflow_c.is_diff_zero.result row 0)) ∧
    (b_neg_not_overflow     = b_neg       * (1 - is_overflow)) ∧
    (b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow)) ∧
    -- (7d) Overflow case clamp.
    (is_overflow = 1 →
      q_0 = b_0 ∧ q_1 = b_1 ∧ q_2 = b_2 ∧ q_3 = b_3 ∧
      r_0 = 0 ∧ r_1 = 0 ∧ r_2 = 0 ∧ r_3 = 0) ∧
    -- (8) b = c·q + r carry chain.
    let base : FKB := 65536
    let sign_ext := rem_neg * 65535
    let cqr_0 := cq_0 + rc_0      - cy_0 * base
    let cqr_1 := cq_1 + rc_1      - cy_1 * base + cy_0
    let cqr_2 := cq_2 + rc_2      - cy_2 * base + cy_1
    let cqr_3 := cq_3 + rc_3      - cy_3 * base + cy_2
    let cqr_4 := cq_4 + sign_ext  - cy_4 * base + cy_3
    let cqr_5 := cq_5 + sign_ext  - cy_5 * base + cy_4
    let cqr_6 := cq_6 + sign_ext  - cy_6 * base + cy_5
    let cqr_7 := cq_7 + sign_ext  - cy_7 * base + cy_6
    (is_overflow = 0 →
      cqr_0 = b_0 ∧ cqr_1 = b_1 ∧ cqr_2 = b_2 ∧ cqr_3 = b_3 ∧
      cqr_4 = b_neg * 65535 ∧ cqr_5 = b_neg * 65535 ∧
      cqr_6 = b_neg * 65535 ∧ cqr_7 = b_neg * 65535) ∧
    -- (9) a = q or r per opcode.
    let div_active := is_divu + is_div + is_divuw + is_divw
    let rem_active := is_remu + is_rem + is_remuw + is_remw
    (div_active = 1 → a_0 = q_0 ∧ a_1 = q_1 ∧ a_2 = q_2 ∧ a_3 = q_3) ∧
    (rem_active = 1 → a_0 = r_0 ∧ a_1 = r_1 ∧ a_2 = r_2 ∧ a_3 = r_3) ∧
    -- (10) Sign consistency.
    (rem_neg = 1 → b_neg = 1) ∧
    ((r_0 + r_1 + r_2 + r_3) * (rem_neg - 1) * b_neg = 0) ∧
    -- (12) Div-by-zero clamps.
    let is_c_0_result := air.cols.values.is_c_0.result row 0
    (is_c_0_result = 1 →
      q_0 = 65535 ∧ q_1 = 65535 ∧ q_2 = 65535 ∧ q_3 = 65535 ∧
      rc_0 = b_0 ∧ rc_1 = b_1 ∧ rc_2 = b_2 ∧ rc_3 = b_3) ∧
    -- (13) Abs-values when not negative.
    (c_neg   = 0 → ac_0 = c_0 ∧ ac_1 = c_1 ∧ ac_2 = c_2 ∧ ac_3 = c_3) ∧
    (rem_neg = 0 → ar_0 = r_0 ∧ ar_1 = r_1 ∧ ar_2 = r_2 ∧ ar_3 = r_3) ∧
    -- (14) max_abs_c_or_1.
    (mc_0 = (is_c_0_result + (1 - is_c_0_result) * ac_0)) ∧
    (mc_1 = (1 - is_c_0_result) * ac_1) ∧
    (mc_2 = (1 - is_c_0_result) * ac_2) ∧
    (mc_3 = (1 - is_c_0_result) * ac_3) ∧
    -- (15) remainder_check_multiplicity + abs alu events.
    (remainder_check_multiplicity = (1 - is_c_0_result) * is_real) ∧
    (abs_c_alu_event   = c_neg   * is_real) ∧
    (abs_rem_alu_event = rem_neg * is_real) ∧
    -- (17) value = 0 when alu event.
    (abs_c_alu_event = 1 →
      air.cols.values.c_neg_gadget.value_0 row 0 = 0 ∧ air.cols.values.c_neg_gadget.value_1 row 0 = 0 ∧
      air.cols.values.c_neg_gadget.value_2 row 0 = 0 ∧ air.cols.values.c_neg_gadget.value_3 row 0 = 0) ∧
    (abs_rem_alu_event = 1 →
      air.cols.values.rem_neg_gadget.value_0 row 0 = 0 ∧ air.cols.values.rem_neg_gadget.value_1 row 0 = 0 ∧
      air.cols.values.rem_neg_gadget.value_2 row 0 = 0 ∧ air.cols.values.rem_neg_gadget.value_3 row 0 = 0) ∧
    -- (18b) `bit = 1` pin from Pico PR #101 — closes the LtWordU16Gadget
    --       soundness gap (gadget only enforces `bit ↔ (a < b)`).
    (remainder_check_multiplicity = 1 →
      air.cols.values.remainder_lt_gadget.bit row 0 = 1) ∧
    -- (20) Boolean checks on carry bits + selectors + flags.
    (cy_0 * (cy_0 - 1) = 0) ∧
    (cy_1 * (cy_1 - 1) = 0) ∧
    (cy_2 * (cy_2 - 1) = 0) ∧
    (cy_3 * (cy_3 - 1) = 0) ∧
    (cy_4 * (cy_4 - 1) = 0) ∧
    (cy_5 * (cy_5 - 1) = 0) ∧
    (cy_6 * (cy_6 - 1) = 0) ∧
    (cy_7 * (cy_7 - 1) = 0) ∧
    (is_div    * (is_div    - 1) = 0) ∧
    (is_divu   * (is_divu   - 1) = 0) ∧
    (is_rem    * (is_rem    - 1) = 0) ∧
    (is_remu   * (is_remu   - 1) = 0) ∧
    (is_divw   * (is_divw   - 1) = 0) ∧
    (is_remw   * (is_remw   - 1) = 0) ∧
    (is_divuw  * (is_divuw  - 1) = 0) ∧
    (is_remuw  * (is_remuw  - 1) = 0) ∧
    (is_overflow * (is_overflow - 1) = 0) ∧
    (is_real_not_word * (is_real_not_word - 1) = 0) ∧
    (b_neg * (b_neg - 1) = 0) ∧
    (b_neg_not_overflow     * (b_neg_not_overflow     - 1) = 0) ∧
    (b_not_neg_not_overflow * (b_not_neg_not_overflow - 1) = 0) ∧
    (rem_neg * (rem_neg - 1) = 0) ∧
    (c_neg   * (c_neg   - 1) = 0) ∧
    (is_real * (is_real - 1) = 0) ∧
    (abs_c_alu_event   * (abs_c_alu_event   - 1) = 0) ∧
    (abs_rem_alu_event * (abs_rem_alu_event - 1) = 0) ∧
    -- (21) Exact-one selector.
    (is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)

  /-- The chip-own bus entries (everything in `AbsBuses` after the
      sub-gadget `AbsBuses` blocks): 32 byte-bus u16 range-check
      entries on `quotient`, `remainder`, `c_times_quotient`, the
      computed `c·q + rem` carry chain, `abs_c`, `abs_remainder`,
      plus the two `looking_alu(ADD)` ALU entries for the abs-value
      sub-events and the chip's own `looked_alu` dispatching to the
      selector-encoded ALU opcode
      `is_div · 34 + is_divu · 35 + is_rem · 36 + is_remu · 37
       + is_divw · 49 + is_divuw · 50 + is_remw · 51 + is_remuw · 52`.

      Factored out of `AbsBuses` (and intentionally **not** marked
      `@[constraint_and_interaction_simplification]`) so that the
      automation can split `bus_row_ext_asm` / `bus_row_wf_asm` on
      the typed bus into gadget-bus pieces + a single opaque
      `bus_row_ext_asm (ChipExtraBuses air row)` /
      `bus_row_wf_asm (ChipExtraBuses air row)` residual that
      callers unfold explicitly when they need to extract
      operand-range hypotheses or byte-bus u16 bounds. -/
  def ChipExtraBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let a_0 := air.cols.values.a_0 row 0
    let a_1 := air.cols.values.a_1 row 0
    let a_2 := air.cols.values.a_2 row 0
    let a_3 := air.cols.values.a_3 row 0
    let b_0 := air.cols.values.b_0 row 0
    let b_1 := air.cols.values.b_1 row 0
    let b_2 := air.cols.values.b_2 row 0
    let b_3 := air.cols.values.b_3 row 0
    let c_0 := air.cols.values.c_0 row 0
    let c_1 := air.cols.values.c_1 row 0
    let c_2 := air.cols.values.c_2 row 0
    let c_3 := air.cols.values.c_3 row 0
    let q_0 := air.cols.values.quotient_0 row 0
    let q_1 := air.cols.values.quotient_1 row 0
    let q_2 := air.cols.values.quotient_2 row 0
    let q_3 := air.cols.values.quotient_3 row 0
    let rc_0 := air.cols.values.remainder_comp_0 row 0
    let rc_1 := air.cols.values.remainder_comp_1 row 0
    let rc_2 := air.cols.values.remainder_comp_2 row 0
    let rc_3 := air.cols.values.remainder_comp_3 row 0
    let r_0 := air.cols.values.remainder_0 row 0
    let r_1 := air.cols.values.remainder_1 row 0
    let r_2 := air.cols.values.remainder_2 row 0
    let r_3 := air.cols.values.remainder_3 row 0
    let ar_0 := air.cols.values.abs_remainder_0 row 0
    let ar_1 := air.cols.values.abs_remainder_1 row 0
    let ar_2 := air.cols.values.abs_remainder_2 row 0
    let ar_3 := air.cols.values.abs_remainder_3 row 0
    let ac_0 := air.cols.values.abs_c_0 row 0
    let ac_1 := air.cols.values.abs_c_1 row 0
    let ac_2 := air.cols.values.abs_c_2 row 0
    let ac_3 := air.cols.values.abs_c_3 row 0
    let cq_0 := air.cols.values.c_times_quotient_0 row 0
    let cq_1 := air.cols.values.c_times_quotient_1 row 0
    let cq_2 := air.cols.values.c_times_quotient_2 row 0
    let cq_3 := air.cols.values.c_times_quotient_3 row 0
    let cq_4 := air.cols.values.c_times_quotient_4 row 0
    let cq_5 := air.cols.values.c_times_quotient_5 row 0
    let cq_6 := air.cols.values.c_times_quotient_6 row 0
    let cq_7 := air.cols.values.c_times_quotient_7 row 0
    let cy_0 := air.cols.values.carry_0 row 0
    let cy_1 := air.cols.values.carry_1 row 0
    let cy_2 := air.cols.values.carry_2 row 0
    let cy_3 := air.cols.values.carry_3 row 0
    let cy_4 := air.cols.values.carry_4 row 0
    let cy_5 := air.cols.values.carry_5 row 0
    let cy_6 := air.cols.values.carry_6 row 0
    let cy_7 := air.cols.values.carry_7 row 0
    let is_div    := air.cols.values.is_div    row 0
    let is_divu   := air.cols.values.is_divu   row 0
    let is_rem    := air.cols.values.is_rem    row 0
    let is_remu   := air.cols.values.is_remu   row 0
    let is_divw   := air.cols.values.is_divw   row 0
    let is_remw   := air.cols.values.is_remw   row 0
    let is_divuw  := air.cols.values.is_divuw  row 0
    let is_remuw  := air.cols.values.is_remuw  row 0
    let is_real           := air.cols.values.is_real           row 0
    let rem_neg           := air.cols.values.rem_neg           row 0
    let abs_c_alu_event   := air.cols.values.abs_c_alu_event   row 0
    let abs_rem_alu_event := air.cols.values.abs_rem_alu_event row 0
    let base : FKB := 65536
    let sign_ext := rem_neg * 65535
    let cqr_0 := cq_0 + rc_0     - cy_0 * base
    let cqr_1 := cq_1 + rc_1     - cy_1 * base + cy_0
    let cqr_2 := cq_2 + rc_2     - cy_2 * base + cy_1
    let cqr_3 := cq_3 + rc_3     - cy_3 * base + cy_2
    let cqr_4 := cq_4 + sign_ext - cy_4 * base + cy_3
    let cqr_5 := cq_5 + sign_ext - cy_5 * base + cy_4
    let cqr_6 := cq_6 + sign_ext - cy_6 * base + cy_5
    let cqr_7 := cq_7 + sign_ext - cy_7 * base + cy_6
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(abs_c_alu_event),
          #v[ 0,  0, 0, 0, 0,
              c_0,  c_1,  c_2,  c_3,
              ac_0, ac_1, ac_2, ac_3 ]),
        (-(abs_rem_alu_event),
          #v[ 0,  0, 0, 0, 0,
              r_0,  r_1,  r_2,  r_3,
              ar_0, ar_1, ar_2, ar_3 ]),
        (is_real,
          #v[ is_div   * 34 + is_divu  * 35
              + is_rem * 36 + is_remu  * 37
              + is_divw * 49 + is_divuw * 50
              + is_remw * 51 + is_remuw * 52,
              a_0, a_1, a_2, a_3,
              b_0, b_1, b_2, b_3,
              c_0, c_1, c_2, c_3 ])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        (-(is_real), #v[8, q_0, 0, 0, 0]),
        (-(is_real), #v[8, q_1, 0, 0, 0]),
        (-(is_real), #v[8, q_2, 0, 0, 0]),
        (-(is_real), #v[8, q_3, 0, 0, 0]),
        (-(is_real), #v[8, r_0, 0, 0, 0]),
        (-(is_real), #v[8, r_1, 0, 0, 0]),
        (-(is_real), #v[8, r_2, 0, 0, 0]),
        (-(is_real), #v[8, r_3, 0, 0, 0]),
        (-(is_real), #v[8, cq_0, 0, 0, 0]),
        (-(is_real), #v[8, cq_1, 0, 0, 0]),
        (-(is_real), #v[8, cq_2, 0, 0, 0]),
        (-(is_real), #v[8, cq_3, 0, 0, 0]),
        (-(is_real), #v[8, cq_4, 0, 0, 0]),
        (-(is_real), #v[8, cq_5, 0, 0, 0]),
        (-(is_real), #v[8, cq_6, 0, 0, 0]),
        (-(is_real), #v[8, cq_7, 0, 0, 0]),
        (-(is_real), #v[8, cqr_0, 0, 0, 0]),
        (-(is_real), #v[8, cqr_1, 0, 0, 0]),
        (-(is_real), #v[8, cqr_2, 0, 0, 0]),
        (-(is_real), #v[8, cqr_3, 0, 0, 0]),
        (-(is_real), #v[8, cqr_4, 0, 0, 0]),
        (-(is_real), #v[8, cqr_5, 0, 0, 0]),
        (-(is_real), #v[8, cqr_6, 0, 0, 0]),
        (-(is_real), #v[8, cqr_7, 0, 0, 0]),
        (-(is_real), #v[8, ac_0, 0, 0, 0]),
        (-(is_real), #v[8, ac_1, 0, 0, 0]),
        (-(is_real), #v[8, ac_2, 0, 0, 0]),
        (-(is_real), #v[8, ac_3, 0, 0, 0]),
        (-(is_real), #v[8, ar_0, 0, 0, 0]),
        (-(is_real), #v[8, ar_1, 0, 0, 0]),
        (-(is_real), #v[8, ar_2, 0, 0, 0]),
        (-(is_real), #v[8, ar_3, 0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)

  /-- The bus entries `DivRemChip` contributes per row.
      Composed compositionally from the sub-gadget `AbsBuses`s
      (`MulGadget` × 2, `AddGadget` × 2, `LtWordU16Gadget`,
      `U16MSBGadget` × 6 — `IsZeroWordGadget` / `IsEqualWordGadget`
      contribute no bus entries), plus `ChipExtraBuses` (the
      chip-own range checks + ALU entries). -/
  @[constraint_and_interaction_simplification]
  def AbsBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let b_1 := air.cols.values.b_1 row 0
    let b_3 := air.cols.values.b_3 row 0
    let c_0 := air.cols.values.c_0 row 0
    let c_1 := air.cols.values.c_1 row 0
    let c_2 := air.cols.values.c_2 row 0
    let c_3 := air.cols.values.c_3 row 0
    let qc_0 := air.cols.values.quotient_comp_0 row 0
    let qc_1 := air.cols.values.quotient_comp_1 row 0
    let qc_2 := air.cols.values.quotient_comp_2 row 0
    let qc_3 := air.cols.values.quotient_comp_3 row 0
    let r_1 := air.cols.values.remainder_1 row 0
    let r_3 := air.cols.values.remainder_3 row 0
    let cq_1 := air.cols.values.c_times_quotient_1 row 0
    let cq_5 := air.cols.values.c_times_quotient_5 row 0
    let b_msb   := air.cols.values.b_msb.msb   row 0
    let c_msb   := air.cols.values.c_msb.msb   row 0
    let rem_msb := air.cols.values.rem_msb.msb row 0
    let is_divw   := air.cols.values.is_divw   row 0
    let is_remw   := air.cols.values.is_remw   row 0
    let is_divuw  := air.cols.values.is_divuw  row 0
    let is_remuw  := air.cols.values.is_remuw  row 0
    let is_real           := air.cols.values.is_real           row 0
    let is_real_not_word  := air.cols.values.is_real_not_word  row 0
    let abs_c_alu_event   := air.cols.values.abs_c_alu_event   row 0
    let abs_rem_alu_event := air.cols.values.abs_rem_alu_event row 0
    let remainder_check_multiplicity :=
      air.cols.values.remainder_check_multiplicity row 0
    let is_word_operation := is_divw + is_remw + is_divuw + is_remuw
    -- (a) `MulGadget` × 2.
    MulGadget.AbsBuses
      is_real 0
      cq_1
      qc_0 qc_1 qc_2 qc_3
      c_0  c_1  c_2  c_3
      (air.cols.values.c_times_quotient_lower.carry_0  row 0)
      (air.cols.values.c_times_quotient_lower.carry_1  row 0)
      (air.cols.values.c_times_quotient_lower.carry_2  row 0)
      (air.cols.values.c_times_quotient_lower.carry_3  row 0)
      (air.cols.values.c_times_quotient_lower.carry_4  row 0)
      (air.cols.values.c_times_quotient_lower.carry_5  row 0)
      (air.cols.values.c_times_quotient_lower.carry_6  row 0)
      (air.cols.values.c_times_quotient_lower.carry_7  row 0)
      (air.cols.values.c_times_quotient_lower.carry_8  row 0)
      (air.cols.values.c_times_quotient_lower.carry_9  row 0)
      (air.cols.values.c_times_quotient_lower.carry_10 row 0)
      (air.cols.values.c_times_quotient_lower.carry_11 row 0)
      (air.cols.values.c_times_quotient_lower.carry_12 row 0)
      (air.cols.values.c_times_quotient_lower.carry_13 row 0)
      (air.cols.values.c_times_quotient_lower.carry_14 row 0)
      (air.cols.values.c_times_quotient_lower.carry_15 row 0)
      (air.cols.values.c_times_quotient_lower.product_0  row 0)
      (air.cols.values.c_times_quotient_lower.product_1  row 0)
      (air.cols.values.c_times_quotient_lower.product_2  row 0)
      (air.cols.values.c_times_quotient_lower.product_3  row 0)
      (air.cols.values.c_times_quotient_lower.product_4  row 0)
      (air.cols.values.c_times_quotient_lower.product_5  row 0)
      (air.cols.values.c_times_quotient_lower.product_6  row 0)
      (air.cols.values.c_times_quotient_lower.product_7  row 0)
      (air.cols.values.c_times_quotient_lower.product_8  row 0)
      (air.cols.values.c_times_quotient_lower.product_9  row 0)
      (air.cols.values.c_times_quotient_lower.product_10 row 0)
      (air.cols.values.c_times_quotient_lower.product_11 row 0)
      (air.cols.values.c_times_quotient_lower.product_12 row 0)
      (air.cols.values.c_times_quotient_lower.product_13 row 0)
      (air.cols.values.c_times_quotient_lower.product_14 row 0)
      (air.cols.values.c_times_quotient_lower.product_15 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_lower.b_msb row 0)
      (air.cols.values.c_times_quotient_lower.c_msb row 0)
      (air.cols.values.c_times_quotient_lower.product_msb.msb row 0)
    ++
    MulGadget.AbsBuses
      is_real_not_word 0
      cq_5
      qc_0 qc_1 qc_2 qc_3
      c_0  c_1  c_2  c_3
      (air.cols.values.c_times_quotient_upper.carry_0  row 0)
      (air.cols.values.c_times_quotient_upper.carry_1  row 0)
      (air.cols.values.c_times_quotient_upper.carry_2  row 0)
      (air.cols.values.c_times_quotient_upper.carry_3  row 0)
      (air.cols.values.c_times_quotient_upper.carry_4  row 0)
      (air.cols.values.c_times_quotient_upper.carry_5  row 0)
      (air.cols.values.c_times_quotient_upper.carry_6  row 0)
      (air.cols.values.c_times_quotient_upper.carry_7  row 0)
      (air.cols.values.c_times_quotient_upper.carry_8  row 0)
      (air.cols.values.c_times_quotient_upper.carry_9  row 0)
      (air.cols.values.c_times_quotient_upper.carry_10 row 0)
      (air.cols.values.c_times_quotient_upper.carry_11 row 0)
      (air.cols.values.c_times_quotient_upper.carry_12 row 0)
      (air.cols.values.c_times_quotient_upper.carry_13 row 0)
      (air.cols.values.c_times_quotient_upper.carry_14 row 0)
      (air.cols.values.c_times_quotient_upper.carry_15 row 0)
      (air.cols.values.c_times_quotient_upper.product_0  row 0)
      (air.cols.values.c_times_quotient_upper.product_1  row 0)
      (air.cols.values.c_times_quotient_upper.product_2  row 0)
      (air.cols.values.c_times_quotient_upper.product_3  row 0)
      (air.cols.values.c_times_quotient_upper.product_4  row 0)
      (air.cols.values.c_times_quotient_upper.product_5  row 0)
      (air.cols.values.c_times_quotient_upper.product_6  row 0)
      (air.cols.values.c_times_quotient_upper.product_7  row 0)
      (air.cols.values.c_times_quotient_upper.product_8  row 0)
      (air.cols.values.c_times_quotient_upper.product_9  row 0)
      (air.cols.values.c_times_quotient_upper.product_10 row 0)
      (air.cols.values.c_times_quotient_upper.product_11 row 0)
      (air.cols.values.c_times_quotient_upper.product_12 row 0)
      (air.cols.values.c_times_quotient_upper.product_13 row 0)
      (air.cols.values.c_times_quotient_upper.product_14 row 0)
      (air.cols.values.c_times_quotient_upper.product_15 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.c_times_quotient_upper.b_msb row 0)
      (air.cols.values.c_times_quotient_upper.c_msb row 0)
      (air.cols.values.c_times_quotient_upper.product_msb.msb row 0)
    ++
    -- (b) `AddGadget` × 2.
    AddGadget.AbsBuses abs_c_alu_event
      (air.cols.values.c_neg_gadget.value_0 row 0)
      (air.cols.values.c_neg_gadget.value_1 row 0)
      (air.cols.values.c_neg_gadget.value_2 row 0)
      (air.cols.values.c_neg_gadget.value_3 row 0)
    ++
    AddGadget.AbsBuses abs_rem_alu_event
      (air.cols.values.rem_neg_gadget.value_0 row 0)
      (air.cols.values.rem_neg_gadget.value_1 row 0)
      (air.cols.values.rem_neg_gadget.value_2 row 0)
      (air.cols.values.rem_neg_gadget.value_3 row 0)
    ++
    -- (c) `LtWordU16Gadget`.
    LtWordU16Gadget.AbsBuses
      remainder_check_multiplicity
      (air.cols.values.remainder_lt_gadget.comparison_limbs_0 row 0)
      (air.cols.values.remainder_lt_gadget.comparison_limbs_1 row 0)
      (air.cols.values.remainder_lt_gadget.bit row 0)
    ++
    -- (d) `U16MSBGadget` × 6 (3 msbs × 2 gated modes).
    U16MSBGadget.AbsBuses is_real_not_word b_3 b_msb
    ++ U16MSBGadget.AbsBuses is_real_not_word c_3 c_msb
    ++ U16MSBGadget.AbsBuses is_real_not_word r_3 rem_msb
    ++ U16MSBGadget.AbsBuses is_word_operation b_1 b_msb
    ++ U16MSBGadget.AbsBuses is_word_operation c_1 c_msb
    ++ U16MSBGadget.AbsBuses is_word_operation r_1 rem_msb
    ++
    -- (e) Chip-own: 32 slice u16 range checks + 2 looking_alu(ADD)
    --     + 1 looked_alu(main DivRem). Factored into `ChipExtraBuses`
    --     above so `bus_row_ext_asm` / `bus_row_wf_asm` simplifications
    --     don't unfold its 35 entries by default.
    ChipExtraBuses air row

  /-- `Extraction.allHold` ↔ `Extraction.constrain_interactions ∧ AbsConstraints`.
      For `MulChip` (5 selectors, 51 constraints) the analogous lemma
      closes by a single `simp` invocation. For `DivRemChip` (8
      selectors, 337 extracted constraints, 2 nested `MulGadget`s +
      `LtWordU16Gadget` + 2 `AddGadget`s + `IsZeroWordGadget` + 2
      `IsEqualWordGadget`s + 6 `U16MSBGadget`s) it is a heavyweight
      derivation — the same simp set, but expected to be much slower.
      Drives `allHold_abs` (and via it, the chip-level `spec`s). -/
  @[constraint_and_interaction_simplification]
  def allHold_simplified
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
  : Prop :=
    DivRemChip.Extraction.constrain_interactions air ∧ AbsConstraints air row

  set_option maxRecDepth 4_000_000 in
  @[simp]
  lemma allHold_iff_allHold_simplified
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
  :
    DivRemChip.Extraction.allHold air row ↔ allHold_simplified air row
  := by
    unfold Extraction.allHold allHold_simplified
    simp [pico_encapsulation,
          extracted_constraint_definition,
          constraint_and_interaction_simplification,
          MulGadget.AbsConstraints,
          IsEqualWordGadget.AbsConstraints,
          IsZeroGadget.AbsConstraints,
          IsZeroWordGadget.AbsConstraints,
          AddGadget.AbsConstraints,
          LtWordU16Gadget.AbsConstraints,
          U16MSBGadget.AbsConstraints,
          and_assoc,
          or_assoc]

end DivRemChip.ConstraintsAndBuses

namespace DivRemChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `DivRemChip` row. Just an alias for
      `ConstraintsAndBuses.AbsBuses`, which already takes the air
      directly (unlike `MulChip` which has a parametric `AbsBuses`
      and a separate `bus_row`). -/
  def bus_row (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    DivRemChip.ConstraintsAndBuses.AbsBuses air row

  /-- Trivial unfolding of `bus_row`. -/
  @[simp]
  lemma bus_row_def (air : Valid_DivRemChip FKB ExtF) (row : ℕ) :
    bus_row air row = DivRemChip.ConstraintsAndBuses.AbsBuses air row
  := rfl

end DivRemChip.Interactions

namespace DivRemChip.Interpretations

  open RV64IM_Interactions
  open DivRemChip.ConstraintsAndBuses
  open DivRemChip.Interactions

  /-- All eight DIV/REM selectors are boolean (each ∈ `{0, 1}`),
      and exactly one is `1` (their sum equals `1`). The boolean
      checks plus the exact-one constraint come from `AbsConstraints`
      (Section 20 and 21). -/
  lemma selector_breakdown
    [Field F] [Field ExtF]
    (air : Valid_DivRemChip F ExtF) (row : ℕ)
    (h_constraints : AbsConstraints air row)
  :
    (air.cols.values.is_div    row 0 = 0 ∨ air.cols.values.is_div    row 0 = 1) ∧
    (air.cols.values.is_divu   row 0 = 0 ∨ air.cols.values.is_divu   row 0 = 1) ∧
    (air.cols.values.is_rem    row 0 = 0 ∨ air.cols.values.is_rem    row 0 = 1) ∧
    (air.cols.values.is_remu   row 0 = 0 ∨ air.cols.values.is_remu   row 0 = 1) ∧
    (air.cols.values.is_divw   row 0 = 0 ∨ air.cols.values.is_divw   row 0 = 1) ∧
    (air.cols.values.is_remw   row 0 = 0 ∨ air.cols.values.is_remw   row 0 = 1) ∧
    (air.cols.values.is_divuw  row 0 = 0 ∨ air.cols.values.is_divuw  row 0 = 1) ∧
    (air.cols.values.is_remuw  row 0 = 0 ∨ air.cols.values.is_remuw  row 0 = 1) ∧
    (air.cols.values.is_divu  row 0 + air.cols.values.is_remu  row 0 +
     air.cols.values.is_div   row 0 + air.cols.values.is_rem   row 0 +
     air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
     air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1)
  := by
    -- The 8 boolean checks are conjuncts inside `AbsConstraints` (Section
    -- 20). The sum-equals-one constraint is Section 21.
    simp [AbsConstraints, sub_eq_zero] at h_constraints
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (clear *- h_constraints; aesop)

  /-- Exactly one of the eight selectors is `1`: if any of `is_div`,
      `is_divu`, `is_rem`, `is_remu`, `is_divw`, `is_remw`, `is_divuw`,
      `is_remuw` is `1`, the other seven are `0`. Follows from
      `selector_breakdown` plus the exact-one constraint
      `is_divu + is_remu + is_div + is_rem + is_divw + is_remw +
       is_divuw + is_remuw = 1` (last conjunct of `AbsConstraints`). -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_constraints : AbsConstraints air row)
  :
    (air.cols.values.is_div row 0 = 1 →
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_divu row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_rem row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_remu row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_divw row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_remw row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_divuw row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_remuw row 0 = 0) ∧
    (air.cols.values.is_remuw row 0 = 1 →
      air.cols.values.is_div   row 0 = 0 ∧
      air.cols.values.is_divu  row 0 = 0 ∧
      air.cols.values.is_rem   row 0 = 0 ∧
      air.cols.values.is_remu  row 0 = 0 ∧
      air.cols.values.is_divw  row 0 = 0 ∧
      air.cols.values.is_remw  row 0 = 0 ∧
      air.cols.values.is_divuw row 0 = 0)
  := by
    have h_breakdown := selector_breakdown air row h_constraints
    clear *- h_breakdown
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h_sum⟩ := h_breakdown
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_,
            fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

  -- =====================================================================
  -- Preprocessing lemma: bus split + gadget-spec application.
  --
  -- Every chip-level `spec_*` proof used to start with the same
  -- boilerplate:
  --   (i)  peel `bus_row_ext_asm` / `bus_row_wf_asm` over the 11-way
  --        `++` chain in `AbsBuses` into one `(ext_asm, wf_asm)` pair
  --        per sub-gadget plus a residual on `ChipExtraBuses`;
  --   (ii) feed each sub-gadget's `(ext_asm, wf_asm, AbsConstraints,
  --        gate)` bundle into its `Spec.gadget_spec`.
  --
  -- `gadget_specs_pack` does both at once and returns:
  --   * chip-only `bus_row_ext_asm (ChipExtraBuses air row)`,
  --   * chip-only `bus_row_wf_asm  (ChipExtraBuses air row)`,
  --   * `AbsConstraints_NoGadgets air row` (the 107 non-gadget
  --     conjuncts of `AbsConstraints`),
  --   * the gadget specs as *conditional* facts (each curried on its
  --     parametric gate + any external range hypothesis).
  --
  -- The conditional shape is necessary because the chip-side gates
  -- are parametric expressions (`is_real`, `is_real_not_word`,
  -- `is_word_operation`, `abs_c_alu_event`, `remainder_check_multiplicity`,
  -- …): the caller substitutes selector-specific values (`is_real = 1`,
  -- `is_div + is_rem = 1`, etc.) before `simp [*] at gadget_specs`,
  -- which collapses the antecedents and exposes direct gadget conclusions.
  --
  -- See [memory] gadget_specs_pack_pattern.md for the call-site idiom.
  -- =====================================================================

  set_option linter.constructorNameAsVariable false in
  /-- Preprocessing lemma: bus-row split + gadget-spec application.

      Given the full typed `bus_row_ext_asm` / `bus_row_wf_asm` plus
      `AbsConstraints`, returns the chip-only `ChipExtraBuses` ext/wf
      residual, the gadget specs as conditional thunks (each curried
      on its parametric gate and any operand-range hypothesis the
      gadget needs externally), and the non-gadget conjuncts of
      `AbsConstraints` as `AbsConstraints_NoGadgets`.

      All gadget-AbsConstraints / gadget-bus pieces are consumed
      internally by the per-gadget `Spec.gadget_spec` calls; their
      `AbsConstraints` parameters survive only inside the thunks.

      Used by `DivRemChip.Spec.spec_DIV_REM` (and the other spec_*
      lemmas) as the single boilerplate-elimination step — see
      [memory] gadget_specs_pack_pattern.md. -/
  lemma gadget_specs_pack
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm  : bus_row_wf_asm  (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
  :
    -- (1) chip-only residual ext/wf (the 32 byte-bus u16 range checks
    --     + 2 looking_alu(ADD) + 1 looked_alu(DivRem); opaque under the
    --     `@[constraint_and_interaction_simplification]` simp set).
    bus_row_ext_asm (ChipExtraBuses air row) ∧
    bus_row_wf_asm  (ChipExtraBuses air row) ∧
    -- (2) Non-gadget AbsConstraints conjuncts (107 of them — sign
    --     pairings, `*_comp` setup, overflow predicates, the carry
    --     chain, `a = q/r`, sign consistency, div-by-zero clamps,
    --     abs-value reconstructions, `max_abs_c_or_1` setup, the abs
    --     ALU-event ⇒ value=0 conjuncts, boolean checks, exact-one
    --     selector).
    AbsConstraints_NoGadgets air row ∧
    -- (3) Lower `MulGadget` thunk — `c · quotient_comp` low 64 bits.
    (ALUBus.Spec
      30
      (air.cols.values.c_times_quotient_0 row 0)
      (air.cols.values.c_times_quotient_1 row 0)
      (air.cols.values.c_times_quotient_2 row 0)
      (air.cols.values.c_times_quotient_3 row 0)
      (air.cols.values.quotient_comp_0 row 0)
      (air.cols.values.quotient_comp_1 row 0)
      (air.cols.values.quotient_comp_2 row 0)
      (air.cols.values.quotient_comp_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)) ∧
    -- (4) Upper `MulGadget` thunk — `c · quotient_comp` high 64 bits.
    --     Gate = `is_real_not_word`. Caller must also supply the
    --     parametric `is_real_eq_sum` identity (follows from the chip's
    --     `is_real = 1` + exact-one-selector + boolean checks; we leave
    --     it on the caller so the lemma stays opcode-agnostic).
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.is_div  row 0 + air.cols.values.is_rem  row 0 +
       air.cols.values.is_divu row 0 + air.cols.values.is_remu row 0 = 1) →
      ALUBus.Spec
        ((air.cols.values.is_div  row 0 + air.cols.values.is_rem  row 0) * 31 +
         (air.cols.values.is_divu row 0 + air.cols.values.is_remu row 0) * 32)
        (air.cols.values.c_times_quotient_4 row 0)
        (air.cols.values.c_times_quotient_5 row 0)
        (air.cols.values.c_times_quotient_6 row 0)
        (air.cols.values.c_times_quotient_7 row 0)
        (air.cols.values.quotient_comp_0 row 0)
        (air.cols.values.quotient_comp_1 row 0)
        (air.cols.values.quotient_comp_2 row 0)
        (air.cols.values.quotient_comp_3 row 0)
        (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
        (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)) ∧
    -- (5) `IsEqualWordGadget` thunk: `b == #v[0,0,0,0x8000]` (i64::MIN),
    --     gated by `is_real_not_word = 1`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      let result := air.cols.values.is_overflow_b.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.b_0 row 0 = 0 ∧ air.cols.values.b_1 row 0 = 0 ∧
         air.cols.values.b_2 row 0 = 0 ∧ air.cols.values.b_3 row 0 = 32768))) ∧
    -- (6) `IsEqualWordGadget` thunk: `c == #v[0xFFFF,…]` (−1, 64-bit),
    --     gated by `is_real_not_word = 1`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      let result := air.cols.values.is_overflow_c.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.c_0 row 0 = 65535 ∧ air.cols.values.c_1 row 0 = 65535 ∧
         air.cols.values.c_2 row 0 = 65535 ∧ air.cols.values.c_3 row 0 = 65535))) ∧
    -- (7) `IsEqualWordGadget` thunk: 32-bit `b_lo == i32::MIN`, gated
    --     by `is_word_operation = 1`. Reuses the same `is_overflow_b`
    --     columns under a different gate (the two gates are mutually
    --     exclusive, so only one of the two `IsEqualWord` thunks
    --     supplies an informative result per row).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
     air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      let result := air.cols.values.is_overflow_b.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.b_0 row 0 = 0 ∧ air.cols.values.b_1 row 0 = 32768 ∧
         (0 : FKB) = 0 ∧ (0 : FKB) = 0))) ∧
    -- (8) `IsEqualWordGadget` thunk: 32-bit `c_lo == -1`, gated by
    --     `is_word_operation = 1`.
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
     air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      let result := air.cols.values.is_overflow_c.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.c_0 row 0 = 65535 ∧ air.cols.values.c_1 row 0 = 65535 ∧
         (0 : FKB) = 0 ∧ (0 : FKB) = 0))) ∧
    -- (9) `IsZeroWordGadget` thunk on `c`.
    (let result := air.cols.values.is_c_0.result row 0
     (result = 0 ∨ result = 1) ∧
     (result = 1 ↔
       (air.cols.values.c_0 row 0 = 0 ∧ air.cols.values.c_1 row 0 = 0 ∧
         air.cols.values.c_2 row 0 = 0 ∧ air.cols.values.c_3 row 0 = 0))) ∧
    -- (10) `AddGadget` thunk: `c + abs_c = c_neg_gadget.value`, gated
    --      by `abs_c_alu_event = 1`. Needs u16 ranges on `c` and `ac`.
    (air.cols.values.abs_c_alu_event row 0 = 1 →
      (air.cols.values.c_0 row 0).val < 65536 ∧ (air.cols.values.c_1 row 0).val < 65536 ∧
      (air.cols.values.c_2 row 0).val < 65536 ∧ (air.cols.values.c_3 row 0).val < 65536 →
        (air.cols.values.abs_c_0 row 0).val < 65536 ∧ (air.cols.values.abs_c_1 row 0).val < 65536 ∧
        (air.cols.values.abs_c_2 row 0).val < 65536 ∧ (air.cols.values.abs_c_3 row 0).val < 65536 →
      (air.cols.values.c_neg_gadget.value_0 row 0).val < 65536 ∧
      (air.cols.values.c_neg_gadget.value_1 row 0).val < 65536 ∧
      (air.cols.values.c_neg_gadget.value_2 row 0).val < 65536 ∧
      (air.cols.values.c_neg_gadget.value_3 row 0).val < 65536 ∧
      U64w.toBV #v[air.cols.values.c_neg_gadget.value_0 row 0,
                   air.cols.values.c_neg_gadget.value_1 row 0,
                   air.cols.values.c_neg_gadget.value_2 row 0,
                   air.cols.values.c_neg_gadget.value_3 row 0]
      = U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                     air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]
      + U64w.toBV #v[air.cols.values.abs_c_0 row 0, air.cols.values.abs_c_1 row 0,
                     air.cols.values.abs_c_2 row 0, air.cols.values.abs_c_3 row 0]) ∧
    -- (11) `AddGadget` thunk: `rc + abs_r = rem_neg_gadget.value`,
    --      gated by `abs_rem_alu_event = 1`. Needs u16 ranges on
    --      `remainder_comp` and `abs_remainder`.
    (air.cols.values.abs_rem_alu_event row 0 = 1 →
      (air.cols.values.remainder_comp_0 row 0).val < 65536 ∧ (air.cols.values.remainder_comp_1 row 0).val < 65536 ∧
      (air.cols.values.remainder_comp_2 row 0).val < 65536 ∧ (air.cols.values.remainder_comp_3 row 0).val < 65536 →
        (air.cols.values.abs_remainder_0 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_1 row 0).val < 65536 ∧
        (air.cols.values.abs_remainder_2 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_3 row 0).val < 65536 →
      (air.cols.values.rem_neg_gadget.value_0 row 0).val < 65536 ∧
      (air.cols.values.rem_neg_gadget.value_1 row 0).val < 65536 ∧
      (air.cols.values.rem_neg_gadget.value_2 row 0).val < 65536 ∧
      (air.cols.values.rem_neg_gadget.value_3 row 0).val < 65536 ∧
      U64w.toBV #v[air.cols.values.rem_neg_gadget.value_0 row 0,
                   air.cols.values.rem_neg_gadget.value_1 row 0,
                   air.cols.values.rem_neg_gadget.value_2 row 0,
                   air.cols.values.rem_neg_gadget.value_3 row 0]
      = U64w.toBV #v[air.cols.values.remainder_comp_0 row 0,
                     air.cols.values.remainder_comp_1 row 0,
                     air.cols.values.remainder_comp_2 row 0,
                     air.cols.values.remainder_comp_3 row 0]
      + U64w.toBV #v[air.cols.values.abs_remainder_0 row 0,
                     air.cols.values.abs_remainder_1 row 0,
                     air.cols.values.abs_remainder_2 row 0,
                     air.cols.values.abs_remainder_3 row 0]) ∧
    -- (12) `LtWordU16Gadget` thunk: `abs_remainder < max_abs_c_or_1`,
    --      gated by `remainder_check_multiplicity = 1`. Needs u16
    --      ranges on `abs_remainder` and `max_abs_c_or_1`.
    (air.cols.values.remainder_check_multiplicity row 0 = 1 →
      (air.cols.values.abs_remainder_0 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_1 row 0).val < 65536 ∧
      (air.cols.values.abs_remainder_2 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_3 row 0).val < 65536 →
        (air.cols.values.max_abs_c_or_1_0 row 0).val < 65536 ∧ (air.cols.values.max_abs_c_or_1_1 row 0).val < 65536 ∧
        (air.cols.values.max_abs_c_or_1_2 row 0).val < 65536 ∧ (air.cols.values.max_abs_c_or_1_3 row 0).val < 65536 →
      let bit := air.cols.values.remainder_lt_gadget.bit row 0
      (bit = 0 ∨ bit = 1) ∧
      (bit = 1 ↔
        (U64w.toBV #v[air.cols.values.abs_remainder_0 row 0,
                      air.cols.values.abs_remainder_1 row 0,
                      air.cols.values.abs_remainder_2 row 0,
                      air.cols.values.abs_remainder_3 row 0]).toNat
        <
        (U64w.toBV #v[air.cols.values.max_abs_c_or_1_0 row 0,
                      air.cols.values.max_abs_c_or_1_1 row 0,
                      air.cols.values.max_abs_c_or_1_2 row 0,
                      air.cols.values.max_abs_c_or_1_3 row 0]).toNat)) ∧
    -- (13) `U16MSBGadget` thunk on `b_msb` for `b_3`, gated by
    --      `is_real_not_word = 1`. Needs `b_3 < 65536` (external from
    --      `ALUBus.operandRange`).
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.b_3 row 0).val < 65536 →
      let msb := air.cols.values.b_msb.msb row 0
      let value := air.cols.values.b_3 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (14) `U16MSBGadget` thunk on `c_msb` for `c_3`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.c_3 row 0).val < 65536 →
      let msb := air.cols.values.c_msb.msb row 0
      let value := air.cols.values.c_3 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (15) `U16MSBGadget` thunk on `rem_msb` for `r_3`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.remainder_3 row 0).val < 65536 →
      let msb := air.cols.values.rem_msb.msb row 0
      let value := air.cols.values.remainder_3 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (16) `U16MSBGadget` thunk on `b_msb` for `b_1` (word-variant mode).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.b_1 row 0).val < 65536 →
      let msb := air.cols.values.b_msb.msb row 0
      let value := air.cols.values.b_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (17) `U16MSBGadget` thunk on `c_msb` for `c_1` (word-variant mode).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.c_1 row 0).val < 65536 →
      let msb := air.cols.values.c_msb.msb row 0
      let value := air.cols.values.c_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (18) `U16MSBGadget` thunk on `rem_msb` for `r_1` (word-variant mode).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.remainder_1 row 0).val < 65536 →
      let msb := air.cols.values.rem_msb.msb row 0
      let value := air.cols.values.remainder_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val))
  := by
    have h_breakdown := selector_breakdown air row h_constraints
    have h_exclusive := selector_exclusivity air row h_constraints
    have : bus_row_ext_asm (ChipExtraBuses air row) := by
      simp [AbsBuses] at h_ext_asm; aesop
    simp [this]; clear this
    have : bus_row_wf_asm (ChipExtraBuses air row) := by
      simp [AbsBuses] at h_wf_asm; aesop
    simp [this]; clear this
    have : AbsConstraints_NoGadgets air row := by
      simp [AbsConstraints] at h_constraints
      simp [AbsConstraints_NoGadgets]
      simp [sub_eq_zero] at h_constraints ⊢
      -- Pull out every conjunct of `AbsConstraints` (in section order)
      -- as a named hypothesis. The 11 gadget AbsConstraints calls
      -- (`h_mul_lo`, `h_mul_hi`, `h_overflow_b_64`, `h_overflow_c_64`,
      -- `h_overflow_b_32`, `h_overflow_c_32`, `h_iszero_c`, `h_add_c`,
      -- `h_add_rem`, `h_lt`, `h_msb_b3..rem1`) survive as single
      -- hypotheses; everything else is an inline scalar equation.
      obtain
        ⟨ eq_is_real_not_word,
          -- (2) MSB-sign pairings × 3
          eq_b_msb_neg, eq_rem_msb_neg, eq_c_msb_neg,
          -- (3) quotient_comp setup (10)
          eq_qc_0, eq_qc_1,
          eq_uw_qc2, eq_sw_qc2, eq_w_q2, eq_nw_qc2,
          eq_uw_qc3, eq_sw_qc3, eq_w_q3, eq_nw_qc3,
          -- (4) remainder_comp setup (10)
          eq_rc_0, eq_rc_1,
          eq_uw_rc2, eq_sw_rc2, eq_w_r2, eq_nw_rc2,
          eq_uw_rc3, eq_sw_rc3, eq_w_r3, eq_nw_rc3,
          -- (5)-(6) MulGadget × 2
          h_mul_lo, h_mul_hi,
          -- (7a) 64-bit IsEqualWord × 2
          h_overflow_b_64, h_overflow_c_64,
          -- (7b) 32-bit IsEqualWord × 2
          h_overflow_b_32, h_overflow_c_32,
          -- (7c) is_overflow + b_neg_not_overflow + b_not_neg_not_overflow
          eq_is_overflow, eq_b_neg_not_overflow, eq_b_not_neg_not_overflow,
          -- (7d) Overflow case clamp (8)
          eq_of_q0, eq_of_q1, eq_of_q2, eq_of_q3,
          eq_of_r0, eq_of_r1, eq_of_r2, eq_of_r3,
          -- (8) `b = c·q + r` carry chain (8)
          eq_cqr0, eq_cqr1, eq_cqr2, eq_cqr3,
          eq_cqr4, eq_cqr5, eq_cqr6, eq_cqr7,
          -- (9) a = q / r per opcode (8)
          eq_aq0, eq_aq1, eq_aq2, eq_aq3,
          eq_ar0, eq_ar1, eq_ar2, eq_ar3,
          -- (10) Sign consistency (2)
          eq_rn_bn, eq_rnz_bn,
          -- (11) IsZeroWordGadget on c
          h_iszero_c,
          -- (12) Div-by-zero clamps (8)
          eq_dbz_q0, eq_dbz_q1, eq_dbz_q2, eq_dbz_q3,
          eq_dbz_r0, eq_dbz_r1, eq_dbz_r2, eq_dbz_r3,
          -- (13) Abs-values when not negative (8)
          eq_abs_c0, eq_abs_c1, eq_abs_c2, eq_abs_c3,
          eq_abs_r0, eq_abs_r1, eq_abs_r2, eq_abs_r3,
          -- (14) max_abs_c_or_1 (4)
          eq_mc0, eq_mc1, eq_mc2, eq_mc3,
          -- (15) rcm, abs_c_event, abs_rem_event (3)
          eq_rcm, eq_abs_c_event, eq_abs_rem_event,
          -- (16) AddGadget × 2
          h_add_c, h_add_rem,
          -- (17) value=0 when alu event (8)
          eq_acneg0, eq_acneg1, eq_acneg2, eq_acneg3,
          eq_arneg0, eq_arneg1, eq_arneg2, eq_arneg3,
          -- (18) LtWordU16Gadget
          h_lt,
          -- (18b) Enforcing lt
          h_is_lt,
          -- (19) U16MSBGadget × 6
          h_msb_b3, h_msb_c3, h_msb_rem3,
          h_msb_b1, h_msb_c1, h_msb_rem1,
          -- (20) Boolean checks (8 selectors + 10 flags + 8 carries)
          bool_is_div, bool_is_divu, bool_is_rem, bool_is_remu,
          bool_is_divw, bool_is_remw, bool_is_divuw, bool_is_remuw,
          bool_is_overflow, bool_is_real_not_word,
          bool_b_neg, bool_b_neg_not_overflow, bool_b_not_neg_not_overflow,
          bool_rem_neg, bool_c_neg, bool_is_real,
          bool_abs_c_event, bool_abs_rem_event,
          bool_cy0, bool_cy1, bool_cy2, bool_cy3,
          bool_cy4, bool_cy5, bool_cy6, bool_cy7,
          -- (21) exactly-one selector
          eq_one_selector
        ⟩ := h_constraints
      clear h_ext_asm h_wf_asm h_exclusive
            h_mul_lo h_mul_hi h_overflow_b_64 h_overflow_c_64 h_overflow_b_32 h_overflow_c_32
            h_add_c h_add_rem h_lt h_msb_b3 h_msb_c3 h_msb_rem3
            h_msb_b1 h_msb_c1 h_msb_rem1
      rw [eq_comm (a := 1)] at *
      have b_c_0 := IsZeroWordGadget.Spec.gadget_spec (h_gadget_constraints := h_iszero_c)
      simp [h_is_real] at b_c_0; replace b_c_0 := b_c_0.1
      simp [imp_and, show ∀ a b, a → b ↔ ¬ a ∨ b by clear *-; grind]
      have not_0_eq_1 : ∀ (a : FKB) (b_a : a = 0 ∨ a = 1), ¬(a = 0) ↔ a = 1 := by clear *-; grind
      have not_1_eq_0 : ∀ (a : FKB) (b_a : a = 0 ∨ a = 1), ¬(a = 1) ↔ a = 0 := by clear *-; grind
      repeat (rw [not_0_eq_1] <;> [ skip; (clear *- h_breakdown; grind) ])
      repeat (rw [not_0_eq_1] <;> [ skip; assumption ])
      repeat (rw [not_1_eq_0] <;> [ skip; (clear *- h_breakdown; grind) ])
      repeat (rw [not_1_eq_0] <;> [ skip; assumption ])
      repeat (rw [not_1_eq_0] <;> [ skip; (clear *- h_breakdown; grind) ])
      repeat (rw [not_1_eq_0] <;> [ skip; assumption ])
      symm at eq_is_overflow eq_b_neg_not_overflow eq_b_not_neg_not_overflow
              eq_mc0 eq_mc1 eq_mc2 eq_mc3 eq_is_real_not_word
      simp_all
      grind (splits := 32)
    simp [this]; clear this
    -- Split externals
    simp [AbsBuses, and_assoc] at h_ext_asm h_wf_asm
    simp [AbsConstraints] at h_constraints
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := MulGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_ext_asm := h_ext_asm.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    simp [h_is_real] at this; simp [this]; clear this
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := MulGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_ext_asm := h_ext_asm.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    simp at this
    constructor <;> [ (clear *- this; grind); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := IsEqualWordGadget.Spec.gadget_spec (h_gadget_constraints := h_constraints.1)
    constructor <;> [ (clear *- this; grind); clear this]
    replace h_constraints := h_constraints.2
    have := IsEqualWordGadget.Spec.gadget_spec (h_gadget_constraints := h_constraints.1)
    constructor <;> [ (clear *- this; grind); clear this]
    replace h_constraints := h_constraints.2
    have := IsEqualWordGadget.Spec.gadget_spec (h_gadget_constraints := h_constraints.1)
    constructor <;> [ (clear *- this; grind); clear this]
    replace h_constraints := h_constraints.2
    have := IsEqualWordGadget.Spec.gadget_spec (h_gadget_constraints := h_constraints.1)
    constructor <;> [ (clear *- this; grind); clear this]
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := IsZeroWordGadget.Spec.gadget_spec (h_gadget_constraints := h_constraints.1)
    simp [h_is_real] at this
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := AddGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    simp at this
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := AddGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    simp at this
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := LtWordU16Gadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    simp at this
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    constructor <;> [ (clear *- this; assumption); clear this]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    clear *- this; assumption

end DivRemChip.Interpretations
