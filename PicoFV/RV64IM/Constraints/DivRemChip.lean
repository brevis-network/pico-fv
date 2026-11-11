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
`2acc7c1828fb4ec1bed5963511bb370870c5b608` (Pico v3.1.1).

The chip verifies `b = c · quotient + remainder` for each of the
eight DIV/REM opcodes — `DIV`, `DIVU`, `REM`, `REMU`, `DIVW`, `REMW`,
`DIVUW`, `REMUW` — with three orthogonal concerns:

1. **Sign reasoning** — `b_msb`, `c_msb`, `r_msb` u16-MSB gadgets +
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

## Layout (226 columns under `air.cols.values`)

| Cols      | Field                            |
|-----------|----------------------------------|
| 0..3      | `a_0..a_3` (output)              |
| 4..7      | `b_0..b_3`                       |
| 8..11     | `c_0..c_3`                       |
| 12..15    | `b_raw_0..b_raw_3`               |
| 16..19    | `c_raw_0..c_raw_3`               |
| 20..23    | `quotient_0..3`                  |
| 24..27    | `quotient_comp_0..3`             |
| 28..31    | `remainder_comp_0..3`            |
| 32..35    | `remainder_0..3`                 |
| 36..39    | `abs_remainder_0..3`             |
| 40..43    | `abs_c_0..3`                     |
| 44..47    | `max_abs_c_or_1_0..3`            |
| 48..55    | `c_times_quotient_0..7`          |
| 56..100   | `c_times_quotient_lower` (45 cols, `MulGadget`) |
| 101..145  | `c_times_quotient_upper` (45 cols, `MulGadget`) |
| 146..153  | `remainder_lt_gadget` (8 cols, `LtWordU16Gadget`) |
| 154..157  | `c_neg_gadget` (4 cols, `AddGadget`) |
| 158..161  | `rem_neg_gadget` (4 cols, `AddGadget`) |
| 162..169  | `carry_0..7`                     |
| 170..180  | `is_c_0` (11 cols, `IsZeroWordGadget`) |
| 181..188  | `is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw` |
| 189       | `is_overflow`                    |
| 190..200  | `is_overflow_b` (11 cols, `IsEqualWordGadget`) |
| 201..211  | `is_overflow_c` (11 cols, `IsEqualWordGadget`) |
| 212       | `b_msb.msb`                      |
| 213       | `r_msb.msb`                      |
| 214       | `c_msb.msb`                      |
| 215       | `quot_msb.msb`                   |
| 216       | `b_neg`                          |
| 217       | `b_neg_not_overflow`             |
| 218       | `b_not_neg_not_overflow`         |
| 219       | `is_real_not_word`               |
| 220       | `rem_neg`                        |
| 221       | `c_neg`                          |
| 222       | `abs_c_alu_event`                |
| 223       | `abs_rem_alu_event`              |
| 224       | `is_real`                        |
| 225       | `remainder_check_multiplicity`   |
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
    let b_raw_0 := air.cols.values.b_raw_0 row 0
    let b_raw_1 := air.cols.values.b_raw_1 row 0
    let b_raw_2 := air.cols.values.b_raw_2 row 0
    let b_raw_3 := air.cols.values.b_raw_3 row 0
    let c_raw_0 := air.cols.values.c_raw_0 row 0
    let c_raw_1 := air.cols.values.c_raw_1 row 0
    let c_raw_2 := air.cols.values.c_raw_2 row 0
    let c_raw_3 := air.cols.values.c_raw_3 row 0
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
    let r_msb     := air.cols.values.rem_msb.msb   row 0
    let c_msb     := air.cols.values.c_msb.msb     row 0
    let q_msb     := air.cols.values.quot_msb.msb  row 0
    let b_neg                  := air.cols.values.b_neg                  row 0
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
    (b_msb * is_signed_type - b_neg   = 0) ∧
    (r_msb * is_signed_type - rem_neg = 0) ∧
    (c_msb * is_signed_type - c_neg   = 0) ∧
    -- ---------------------------------------------------------------------
    -- (3) `b`, `c` from the raw register values `b_raw`, `c_raw` that
    --     the ALU bus carries (`constraints.rs:178-195`). The low 32 bits
    --     are equal; the upper limbs are the raw ones for 64-bit
    --     operations and `_neg · 0xFFFF` (the sign- or zero-extension of
    --     the low 32 bits) for DIVW/REMW/DIVUW/REMUW, whose registers'
    --     upper 32 bits RV64 leaves undefined. Without the word-op
    --     extension of c, a prover could set c_2 ≠ 0 while c_0 = c_1 =
    --     0, making `is_c_0` false while the actual 32-bit divisor is
    --     zero — bypassing the div-by-zero clamp. Without b's, a prover
    --     could pick a large quotient `q` such that `c · q` overflows
    --     into b_2 / b_3, satisfying `c·q + r = b` with an incorrect
    --     quotient (the upper `MulGadget` is disabled for word ops and
    --     provides no protection). Order matches the Rust source's loops
    --     (`b_i` then `c_i` for each `i`).
    -- ---------------------------------------------------------------------
    (b_raw_0 - b_0 = 0) ∧
    (c_raw_0 - c_0 = 0) ∧
    (b_raw_1 - b_1 = 0) ∧
    (c_raw_1 - c_1 = 0) ∧
    (b_2 - (b_raw_2 * is_not_word_operation + b_neg * is_word_operation * 65535) = 0) ∧
    (c_2 - (c_raw_2 * is_not_word_operation + c_neg * is_word_operation * 65535) = 0) ∧
    (b_3 - (b_raw_3 * is_not_word_operation + b_neg * is_word_operation * 65535) = 0) ∧
    (c_3 - (c_raw_3 * is_not_word_operation + c_neg * is_word_operation * 65535) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (4) `quotient_comp` setup.
    --     Lower 2 limbs (i = 0,1): `qc_i = q_i` unconditionally.
    --     Upper 2 limbs (i = 2,3) — four conditional clauses each.
    -- ---------------------------------------------------------------------
    (qc_0 - q_0 = 0) ∧
    (qc_1 - q_1 = 0) ∧
    (is_unsigned_word_operation * (qc_2 - 0)             = 0) ∧
    (is_signed_word_operation   * (qc_2 - q_msb * 65535) = 0) ∧
    (is_word_operation          * (q_2  - q_msb * 65535) = 0) ∧
    (is_not_word_operation      * (qc_2 - q_2)           = 0) ∧
    (is_unsigned_word_operation * (qc_3 - 0)             = 0) ∧
    (is_signed_word_operation   * (qc_3 - q_msb * 65535) = 0) ∧
    (is_word_operation          * (q_3  - q_msb * 65535) = 0) ∧
    (is_not_word_operation      * (qc_3 - q_3)           = 0) ∧
    -- ---------------------------------------------------------------------
    -- (5) `remainder_comp` setup — mirror of (4) but with `r_msb` /
    --     `remainder_comp` / `remainder`.
    -- ---------------------------------------------------------------------
    (rc_0 - r_0 = 0) ∧
    (rc_1 - r_1 = 0) ∧
    (is_unsigned_word_operation * (rc_2 - 0)             = 0) ∧
    (is_signed_word_operation   * (rc_2 - r_msb * 65535) = 0) ∧
    (is_word_operation          * (r_2  - r_msb * 65535) = 0) ∧
    (is_not_word_operation      * (rc_2 - r_2)           = 0) ∧
    (is_unsigned_word_operation * (rc_3 - 0)             = 0) ∧
    (is_signed_word_operation   * (rc_3 - r_msb * 65535) = 0) ∧
    (is_word_operation          * (r_3  - r_msb * 65535) = 0) ∧
    (is_not_word_operation      * (rc_3 - r_3)           = 0) ∧
    -- ---------------------------------------------------------------------
    -- (6) `MulGadget` lower half: `(cq_0..3) = c · quotient_comp` low 64
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
    -- (7) `MulGadget` upper half: `(cq_4..7) = c · quotient_comp` high
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
    -- (8a) `IsEqualWordGadget`s for the overflow predicates.
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
    -- (8b) Same `is_overflow_b` / `is_overflow_c` gadgets, gated by
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
    -- (8c) `is_overflow = is_overflow_b · is_overflow_c · is_signed_type`,
    --      `b_neg_not_overflow`, `b_not_neg_not_overflow`.
    -- ---------------------------------------------------------------------
    (is_overflow -
       (air.cols.values.is_overflow_b.is_diff_zero.result row 0)
       * (air.cols.values.is_overflow_c.is_diff_zero.result row 0)
       * is_signed_type = 0) ∧
    (b_neg_not_overflow     - b_neg       * (1 - is_overflow) = 0) ∧
    (b_not_neg_not_overflow - (1 - b_neg) * (1 - is_overflow) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (8d) Overflow case clamp: when `is_overflow = 1`, force
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
    -- (9) `b = c · quotient + remainder` carry-chain. For each
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
    -- (10) `a = quotient` or `a = remainder` per opcode.
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
    -- (11) Sign consistency between `remainder` and `b`.
    --      • `rem_neg → b_neg = 1` (Rust: `when(rem_neg).assert_one(b_neg)`)
    --      • `(remainder ≠ 0) ∧ (¬rem_neg) → b_neg = 0`
    -- ---------------------------------------------------------------------
    (rem_neg * (b_neg - 1) = 0) ∧
    ((r_0 + r_1 + r_2 + r_3) * (1 - rem_neg) * b_neg = 0) ∧
    -- ---------------------------------------------------------------------
    -- (12) `IsZeroWordGadget` on `c`, gated by `is_real`.
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
    -- (13) Division-by-zero clamps: `is_c_0 → quotient = u64::MAX` (i.e.
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
    -- (14) `abs(c) = c` when `¬c_neg`; `abs(remainder) = remainder_comp`
    --      when `¬rem_neg` (`constraints.rs:491-498`). (The negative case
    --      is handled by the `AddGadget`s below — they verify
    --      `c + abs_c = 0` etc.)
    -- ---------------------------------------------------------------------
    ((c_neg - 1) * (c_0 - ac_0) = 0) ∧
    ((rem_neg - 1) * (rc_0 - ar_0) = 0) ∧
    ((c_neg - 1) * (c_1 - ac_1) = 0) ∧
    ((rem_neg - 1) * (rc_1 - ar_1) = 0) ∧
    ((c_neg - 1) * (c_2 - ac_2) = 0) ∧
    ((rem_neg - 1) * (rc_2 - ar_2) = 0) ∧
    ((c_neg - 1) * (c_3 - ac_3) = 0) ∧
    ((rem_neg - 1) * (rc_3 - ar_3) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (15) `max_abs_c_or_1 = max(abs_c, 1)`. The least significant limb
    --      gets `1` when `is_c_0`, the rest get `0`; otherwise `abs_c`.
    -- ---------------------------------------------------------------------
    (mc_0 - (is_c_0_result + (1 - is_c_0_result) * ac_0) = 0) ∧
    (mc_1 - (1 - is_c_0_result) * ac_1 = 0) ∧
    (mc_2 - (1 - is_c_0_result) * ac_2 = 0) ∧
    (mc_3 - (1 - is_c_0_result) * ac_3 = 0) ∧
    -- ---------------------------------------------------------------------
    -- (16) `remainder_check_multiplicity = (1 - is_c_0) · is_real` and
    --      the two abs-value ALU event selectors.
    -- ---------------------------------------------------------------------
    ((1 - is_c_0_result) * is_real - remainder_check_multiplicity = 0) ∧
    (abs_c_alu_event   - c_neg   * is_real = 0) ∧
    (abs_rem_alu_event - rem_neg * is_real = 0) ∧
    -- ---------------------------------------------------------------------
    -- (17) `AddGadget` instances verifying `c + abs_c = 0` (gated by
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
    -- (18) When the `_alu_event` flag is set, the `AddGadget`'s `value`
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
    -- (19) `LtWordU16Gadget`: `abs_remainder < max_abs_c_or_1`, gated
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
    -- (20) `LtWordU16Gadget` only enforces `bit ↔ (|rem| < max(|c|, 1))`
    --       (a consistency oracle); the chip separately pins
    --       `bit = 1` whenever the gadget fires, which is what actually
    --       enforces `|remainder| < |c|` (`constraints.rs:595-597`;
    --       absent in 2.x, gap DR-1).
    -- ---------------------------------------------------------------------
    (remainder_check_multiplicity *
       (air.cols.values.remainder_lt_gadget.bit row 0 - 1) = 0) ∧
    -- ---------------------------------------------------------------------
    -- (21) `U16MSBGadget`s in two gated modes:
    --        • `is_real_not_word` ⇒ MSB of the top u16 limb (index 3)
    --        • `is_word_operation` ⇒ MSB of the middle u16 limb (index 1)
    --      for each of `b`, `c`, `rem`. The boolean checks duplicate
    --      across modes; the bus side enforces the actual top-bit
    --      relation.
    -- ---------------------------------------------------------------------
    U16MSBGadget.AbsConstraints is_real_not_word b_msb ∧
    U16MSBGadget.AbsConstraints is_real_not_word c_msb ∧
    U16MSBGadget.AbsConstraints is_real_not_word r_msb ∧
    U16MSBGadget.AbsConstraints is_word_operation b_msb ∧
    U16MSBGadget.AbsConstraints is_word_operation c_msb ∧
    U16MSBGadget.AbsConstraints is_word_operation r_msb ∧
    -- `constraints.rs:635-640`: bind `quot_msb` to bit-15 of
    -- `quotient_1` (the high u16 of the low 32-bit half), gated by
    -- `is_word_operation`. Closes the 2.x gap DR-2, where `quot_msb`
    -- was unconstrained.
    U16MSBGadget.AbsConstraints is_word_operation q_msb ∧
    -- ---------------------------------------------------------------------
    -- (22) Boolean checks: 8 carry bits + 8 selectors + `is_overflow`,
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
    -- (23) Exactly one of the eight opcode selectors is set.
    -- ---------------------------------------------------------------------
    (1 - (is_divu + is_remu + is_div + is_rem
          + is_divw + is_remw + is_divuw + is_remuw) = 0)

  /-- `AbsConstraints` with all 11 sub-gadget `AbsConstraints` calls
      stripped out (`MulGadget × 2`, `IsEqualWordGadget × 4`,
      `IsZeroWordGadget`, `AddGadget × 2`, `LtWordU16Gadget`,
      `U16MSBGadget × 7`).

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
    let b_msb := air.cols.values.b_msb.msb    row 0
    let r_msb := air.cols.values.rem_msb.msb  row 0
    let c_msb := air.cols.values.c_msb.msb    row 0
    let q_msb := air.cols.values.quot_msb.msb row 0
    let b_neg                  := air.cols.values.b_neg                  row 0
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
    -- (3) Word-op b/c upper-limbs sign/zero-extension. (The raw-operand
    --     equalities of `AbsConstraints` (3) are in `operands_of_raw`.)
    (is_word_operation = 1 →
      b_2 = b_neg * 65535 ∧ c_2 = c_neg * 65535 ∧
      b_3 = b_neg * 65535 ∧ c_3 = c_neg * 65535) ∧
    -- (4) quotient_comp setup.
    (qc_0 = q_0) ∧ (qc_1 = q_1) ∧
    (rc_0 = r_0) ∧ (rc_1 = r_1) ∧
    (is_unsigned_word_operation = 1 → qc_2 = 0 ∧ qc_3 = 0 ∧ rc_2 = 0 ∧ rc_3 = 0) ∧
    (is_signed_word_operation = 1 → qc_2 = q_msb * 65535 ∧ qc_3 = q_msb * 65535 ∧ rc_2 = r_msb * 65535 ∧ rc_3 = r_msb * 65535) ∧
    (is_word_operation = 1 → q_2 = q_msb * 65535 ∧ q_3 = q_msb * 65535 ∧ r_2 = r_msb * 65535 ∧ r_3 = r_msb * 65535) ∧
    (is_not_word_operation = 1 → qc_2 = q_2 ∧ qc_3 = q_3 ∧ rc_2 = r_2 ∧ rc_3 = r_3) ∧
    -- (8c) is_overflow definition + b_neg_not_overflow + b_not_neg_not_overflow.
    (is_overflow =
      is_signed_type *
      (air.cols.values.is_overflow_b.is_diff_zero.result row 0) *
      (air.cols.values.is_overflow_c.is_diff_zero.result row 0)) ∧
    (b_neg_not_overflow     = b_neg       * (1 - is_overflow)) ∧
    (b_not_neg_not_overflow = (1 - b_neg) * (1 - is_overflow)) ∧
    -- (8d) Overflow case clamp.
    (is_overflow = 1 →
      q_0 = b_0 ∧ q_1 = b_1 ∧ q_2 = b_2 ∧ q_3 = b_3 ∧
      r_0 = 0 ∧ r_1 = 0 ∧ r_2 = 0 ∧ r_3 = 0) ∧
    -- (9) b = c·q + r carry chain.
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
    -- (10) a = q or r per opcode.
    let div_active := is_divu + is_div + is_divuw + is_divw
    let rem_active := is_remu + is_rem + is_remuw + is_remw
    (div_active = 1 → a_0 = q_0 ∧ a_1 = q_1 ∧ a_2 = q_2 ∧ a_3 = q_3) ∧
    (rem_active = 1 → a_0 = r_0 ∧ a_1 = r_1 ∧ a_2 = r_2 ∧ a_3 = r_3) ∧
    -- (11) Sign consistency.
    (rem_neg = 1 → b_neg = 1) ∧
    ((r_0 + r_1 + r_2 + r_3) * (rem_neg - 1) * b_neg = 0) ∧
    -- (13) Div-by-zero clamps.
    let is_c_0_result := air.cols.values.is_c_0.result row 0
    (is_c_0_result = 1 →
      q_0 = 65535 ∧ q_1 = 65535 ∧ q_2 = 65535 ∧ q_3 = 65535 ∧
      rc_0 = b_0 ∧ rc_1 = b_1 ∧ rc_2 = b_2 ∧ rc_3 = b_3) ∧
    -- (14) Abs-values when not negative.
    (c_neg   = 0 → ac_0 = c_0 ∧ ac_1 = c_1 ∧ ac_2 = c_2 ∧ ac_3 = c_3) ∧
    (rem_neg = 0 → ar_0 = rc_0 ∧ ar_1 = rc_1 ∧ ar_2 = rc_2 ∧ ar_3 = rc_3) ∧
    -- (15) max_abs_c_or_1.
    (mc_0 = (is_c_0_result + (1 - is_c_0_result) * ac_0)) ∧
    (mc_1 = (1 - is_c_0_result) * ac_1) ∧
    (mc_2 = (1 - is_c_0_result) * ac_2) ∧
    (mc_3 = (1 - is_c_0_result) * ac_3) ∧
    -- (16) remainder_check_multiplicity + abs alu events.
    (remainder_check_multiplicity = (1 - is_c_0_result) * is_real) ∧
    (abs_c_alu_event   = c_neg   * is_real) ∧
    (abs_rem_alu_event = rem_neg * is_real) ∧
    -- (18) value = 0 when alu event.
    (abs_c_alu_event = 1 →
      air.cols.values.c_neg_gadget.value_0 row 0 = 0 ∧ air.cols.values.c_neg_gadget.value_1 row 0 = 0 ∧
      air.cols.values.c_neg_gadget.value_2 row 0 = 0 ∧ air.cols.values.c_neg_gadget.value_3 row 0 = 0) ∧
    (abs_rem_alu_event = 1 →
      air.cols.values.rem_neg_gadget.value_0 row 0 = 0 ∧ air.cols.values.rem_neg_gadget.value_1 row 0 = 0 ∧
      air.cols.values.rem_neg_gadget.value_2 row 0 = 0 ∧ air.cols.values.rem_neg_gadget.value_3 row 0 = 0) ∧
    -- (20) `bit = 1` pin (`constraints.rs:595-597`) — closes the LtWordU16Gadget
    --       soundness gap (gadget only enforces `bit ↔ (a < b)`).
    (remainder_check_multiplicity = 1 →
      air.cols.values.remainder_lt_gadget.bit row 0 = 1) ∧
    -- (22) Boolean checks on carry bits + selectors + flags.
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
    -- (23) Exact-one selector.
    (is_divu + is_remu + is_div + is_rem + is_divw + is_remw + is_divuw + is_remuw = 1)

  -- =====================================================================
  -- The chip-own bus blocks. `AbsBuses` below interleaves them with the
  -- sub-gadget `AbsBuses` blocks in the order Pico's `eval` emits them,
  -- which is the order `raw_bus_row` (and hence the extraction) lists.
  --
  -- None of them is marked `@[constraint_and_interaction_simplification]`,
  -- so that the automation splits `bus_row_ext_asm` / `bus_row_wf_asm` on
  -- the typed bus into the sub-gadget pieces plus one opaque residual per
  -- block, which callers unfold explicitly when they need a byte-bus u16
  -- bound or the ALU entry's operand ranges.
  -- =====================================================================

  /-- u16 range checks on the eight limbs of `c · quotient + remainder`,
      reconstructed from `c_times_quotient`, `remainder_comp` (sign-extended
      by `rem_neg`) and the carry chain (`constraints.rs:423`). -/
  def CarryChainBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let rc_0 := air.cols.values.remainder_comp_0 row 0
    let rc_1 := air.cols.values.remainder_comp_1 row 0
    let rc_2 := air.cols.values.remainder_comp_2 row 0
    let rc_3 := air.cols.values.remainder_comp_3 row 0
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
    let rem_neg := air.cols.values.rem_neg row 0
    let is_real := air.cols.values.is_real row 0
    let base : FKB := 65536
    let sign_ext := rem_neg * 65535
    ({
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real), #v[8, cq_0 + rc_0     - cy_0 * base,         0, 0, 0]),
        ((is_real), #v[8, cq_1 + rc_1     - cy_1 * base + cy_0,  0, 0, 0]),
        ((is_real), #v[8, cq_2 + rc_2     - cy_2 * base + cy_1,  0, 0, 0]),
        ((is_real), #v[8, cq_3 + rc_3     - cy_3 * base + cy_2,  0, 0, 0]),
        ((is_real), #v[8, cq_4 + sign_ext - cy_4 * base + cy_3,  0, 0, 0]),
        ((is_real), #v[8, cq_5 + sign_ext - cy_5 * base + cy_4,  0, 0, 0]),
        ((is_real), #v[8, cq_6 + sign_ext - cy_6 * base + cy_5,  0, 0, 0]),
        ((is_real), #v[8, cq_7 + sign_ext - cy_7 * base + cy_6,  0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)

  /-- The two `looking_alu(ADD, 0, …)` sub-events that pin the absolute
      values: `c + abs_c = 0` when `c` is negative, and
      `remainder + abs_remainder = 0` when the remainder is negative
      (`constraints.rs:501` and `:508`). -/
  def AbsAluEventBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let c_0 := air.cols.values.c_0 row 0
    let c_1 := air.cols.values.c_1 row 0
    let c_2 := air.cols.values.c_2 row 0
    let c_3 := air.cols.values.c_3 row 0
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
    let abs_c_alu_event   := air.cols.values.abs_c_alu_event   row 0
    let abs_rem_alu_event := air.cols.values.abs_rem_alu_event row 0
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((abs_c_alu_event),
          #v[ 0,  0, 0, 0, 0,
              c_0,  c_1,  c_2,  c_3,
              ac_0, ac_1, ac_2, ac_3 ]),
        ((abs_rem_alu_event),
          #v[ 0,  0, 0, 0, 0,
              r_0,  r_1,  r_2,  r_3,
              ar_0, ar_1, ar_2, ar_3 ])
      ],
      Byte := [],
      State := [],
      Memory := []
    } : BusRow)

  /-- u16 range checks on `abs_c` (`constraints.rs:559`). -/
  def AbsCRangeBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let is_real := air.cols.values.is_real row 0
    ({
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real), #v[8, air.cols.values.abs_c_0 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.abs_c_1 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.abs_c_2 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.abs_c_3 row 0, 0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)

  /-- u16 range checks on `abs_remainder` (`constraints.rs:570`). -/
  def AbsRemainderRangeBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let is_real := air.cols.values.is_real row 0
    ({
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real), #v[8, air.cols.values.abs_remainder_0 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.abs_remainder_1 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.abs_remainder_2 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.abs_remainder_3 row 0, 0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)

  /-- u16 range checks on `quotient`, `remainder` and `c_times_quotient`
      (`constraints.rs:645`, `:646` and `:652`). -/
  def SliceRangeBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let is_real := air.cols.values.is_real row 0
    ({
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real), #v[8, air.cols.values.quotient_0 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.quotient_1 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.quotient_2 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.quotient_3 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.remainder_0 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.remainder_1 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.remainder_2 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.remainder_3 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_0 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_1 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_2 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_3 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_4 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_5 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_6 row 0, 0, 0, 0]),
        ((is_real), #v[8, air.cols.values.c_times_quotient_7 row 0, 0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)

  /-- The chip's own `looked_alu` entry (`constraints.rs:717`): the
      selector-encoded ALU opcode, the output `a`, and the *raw* register
      operands `b_raw`, `c_raw` the CPU sent. The opcode sum is written in
      the extractor's order, so that `bus_row_equiv` closes by `dsimp`. -/
  def LookedAluBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let a_0 := air.cols.values.a_0 row 0
    let a_1 := air.cols.values.a_1 row 0
    let a_2 := air.cols.values.a_2 row 0
    let a_3 := air.cols.values.a_3 row 0
    let b_raw_0 := air.cols.values.b_raw_0 row 0
    let b_raw_1 := air.cols.values.b_raw_1 row 0
    let b_raw_2 := air.cols.values.b_raw_2 row 0
    let b_raw_3 := air.cols.values.b_raw_3 row 0
    let c_raw_0 := air.cols.values.c_raw_0 row 0
    let c_raw_1 := air.cols.values.c_raw_1 row 0
    let c_raw_2 := air.cols.values.c_raw_2 row 0
    let c_raw_3 := air.cols.values.c_raw_3 row 0
    let is_div    := air.cols.values.is_div    row 0
    let is_divu   := air.cols.values.is_divu   row 0
    let is_rem    := air.cols.values.is_rem    row 0
    let is_remu   := air.cols.values.is_remu   row 0
    let is_divw   := air.cols.values.is_divw   row 0
    let is_remw   := air.cols.values.is_remw   row 0
    let is_divuw  := air.cols.values.is_divuw  row 0
    let is_remuw  := air.cols.values.is_remuw  row 0
    let is_real   := air.cols.values.is_real   row 0
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        (-(is_real),
          #v[ is_divu * 35 + is_remu  * 37
              + is_div * 34 + is_rem   * 36
              + is_divw * 49 + is_remw  * 51
              + is_divuw * 50 + is_remuw * 52,
              a_0, a_1, a_2, a_3,
              b_raw_0, b_raw_1, b_raw_2, b_raw_3,
              c_raw_0, c_raw_1, c_raw_2, c_raw_3 ])
      ],
      Byte := [],
      State := [],
      Memory := []
    } : BusRow)

  /-- Everything `DivRemChip` puts on the bus itself, as opposed to through
      a sub-gadget: the six blocks above flattened into one `BusRow`, in
      the order they appear in `AbsBuses` (`ChipExtraBuses_split`).
      `gadget_specs_pack` hands this back as the residual left once the
      sub-gadget pieces are consumed; callers unfold it to read off a
      byte-bus u16 bound or an ALU entry's assumptions. -/
  def ChipExtraBuses (air : Valid_DivRemChip FKB ExtF) (row : ℕ) : BusRow :=
    let a_0 := air.cols.values.a_0 row 0
    let a_1 := air.cols.values.a_1 row 0
    let a_2 := air.cols.values.a_2 row 0
    let a_3 := air.cols.values.a_3 row 0
    let c_0 := air.cols.values.c_0 row 0
    let c_1 := air.cols.values.c_1 row 0
    let c_2 := air.cols.values.c_2 row 0
    let c_3 := air.cols.values.c_3 row 0
    let b_raw_0 := air.cols.values.b_raw_0 row 0
    let b_raw_1 := air.cols.values.b_raw_1 row 0
    let b_raw_2 := air.cols.values.b_raw_2 row 0
    let b_raw_3 := air.cols.values.b_raw_3 row 0
    let c_raw_0 := air.cols.values.c_raw_0 row 0
    let c_raw_1 := air.cols.values.c_raw_1 row 0
    let c_raw_2 := air.cols.values.c_raw_2 row 0
    let c_raw_3 := air.cols.values.c_raw_3 row 0
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
    ({
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        ((abs_c_alu_event),
          #v[ 0,  0, 0, 0, 0,
              c_0,  c_1,  c_2,  c_3,
              ac_0, ac_1, ac_2, ac_3 ]),
        ((abs_rem_alu_event),
          #v[ 0,  0, 0, 0, 0,
              r_0,  r_1,  r_2,  r_3,
              ar_0, ar_1, ar_2, ar_3 ]),
        (-(is_real),
          #v[ is_divu * 35 + is_remu  * 37
              + is_div * 34 + is_rem   * 36
              + is_divw * 49 + is_remw  * 51
              + is_divuw * 50 + is_remuw * 52,
              a_0, a_1, a_2, a_3,
              b_raw_0, b_raw_1, b_raw_2, b_raw_3,
              c_raw_0, c_raw_1, c_raw_2, c_raw_3 ])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        ((is_real), #v[8, cq_0 + rc_0     - cy_0 * base,         0, 0, 0]),
        ((is_real), #v[8, cq_1 + rc_1     - cy_1 * base + cy_0,  0, 0, 0]),
        ((is_real), #v[8, cq_2 + rc_2     - cy_2 * base + cy_1,  0, 0, 0]),
        ((is_real), #v[8, cq_3 + rc_3     - cy_3 * base + cy_2,  0, 0, 0]),
        ((is_real), #v[8, cq_4 + sign_ext - cy_4 * base + cy_3,  0, 0, 0]),
        ((is_real), #v[8, cq_5 + sign_ext - cy_5 * base + cy_4,  0, 0, 0]),
        ((is_real), #v[8, cq_6 + sign_ext - cy_6 * base + cy_5,  0, 0, 0]),
        ((is_real), #v[8, cq_7 + sign_ext - cy_7 * base + cy_6,  0, 0, 0]),
        ((is_real), #v[8, ac_0, 0, 0, 0]),
        ((is_real), #v[8, ac_1, 0, 0, 0]),
        ((is_real), #v[8, ac_2, 0, 0, 0]),
        ((is_real), #v[8, ac_3, 0, 0, 0]),
        ((is_real), #v[8, ar_0, 0, 0, 0]),
        ((is_real), #v[8, ar_1, 0, 0, 0]),
        ((is_real), #v[8, ar_2, 0, 0, 0]),
        ((is_real), #v[8, ar_3, 0, 0, 0]),
        ((is_real), #v[8, q_0, 0, 0, 0]),
        ((is_real), #v[8, q_1, 0, 0, 0]),
        ((is_real), #v[8, q_2, 0, 0, 0]),
        ((is_real), #v[8, q_3, 0, 0, 0]),
        ((is_real), #v[8, r_0, 0, 0, 0]),
        ((is_real), #v[8, r_1, 0, 0, 0]),
        ((is_real), #v[8, r_2, 0, 0, 0]),
        ((is_real), #v[8, r_3, 0, 0, 0]),
        ((is_real), #v[8, cq_0, 0, 0, 0]),
        ((is_real), #v[8, cq_1, 0, 0, 0]),
        ((is_real), #v[8, cq_2, 0, 0, 0]),
        ((is_real), #v[8, cq_3, 0, 0, 0]),
        ((is_real), #v[8, cq_4, 0, 0, 0]),
        ((is_real), #v[8, cq_5, 0, 0, 0]),
        ((is_real), #v[8, cq_6, 0, 0, 0]),
        ((is_real), #v[8, cq_7, 0, 0, 0])
      ],
      State := [],
      Memory := []
    } : BusRow)

  omit [Field ExtF] in
  /-- `ChipExtraBuses` is exactly the six chip-own blocks concatenated, in
      the order `AbsBuses` puts them. Lets a caller turn the per-block
      residuals `AbsBuses` produces into the single `ChipExtraBuses` one. -/
  lemma ChipExtraBuses_split (air : Valid_DivRemChip FKB ExtF) (row : ℕ) :
    ChipExtraBuses air row =
      CarryChainBuses air row
      ++ AbsAluEventBuses air row
      ++ AbsCRangeBuses air row
      ++ AbsRemainderRangeBuses air row
      ++ SliceRangeBuses air row
      ++ LookedAluBuses air row
  := rfl

  /-- The bus entries `DivRemChip` contributes per row.
      Composed compositionally from the sub-gadget `AbsBuses`s
      (`MulGadget` × 2, `AddGadget` × 2, `LtWordU16Gadget`,
      `U16MSBGadget` × 7 — `IsZeroWordGadget` / `IsEqualWordGadget`
      contribute no bus entries), interleaved with the chip-own blocks
      above in the order Pico's `eval` emits them. `bus_row_equiv` proves
      that this is the extracted interaction list, entry for entry. -/
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
    let q_1  := air.cols.values.quotient_1 row 0
    let r_1 := air.cols.values.remainder_1 row 0
    let r_3 := air.cols.values.remainder_3 row 0
    let cq_1 := air.cols.values.c_times_quotient_1 row 0
    let cq_5 := air.cols.values.c_times_quotient_5 row 0
    let b_msb   := air.cols.values.b_msb.msb     row 0
    let c_msb   := air.cols.values.c_msb.msb     row 0
    let r_msb := air.cols.values.rem_msb.msb     row 0
    let quot_msb := air.cols.values.quot_msb.msb row 0
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
    -- (b) Chip-own: the carry-chain range checks (`constraints.rs:423`)
    --     and the two abs-value `looking_alu(ADD)` sub-events
    --     (`constraints.rs:501`, `:508`).
    CarryChainBuses air row
    ++ AbsAluEventBuses air row
    ++
    -- (c) `AddGadget` on `c + abs_c` (`constraints.rs:552`), then the
    --     chip-own range checks on `abs_c` (`constraints.rs:559`).
    AddGadget.AbsBuses abs_c_alu_event
      (air.cols.values.c_neg_gadget.value_0 row 0)
      (air.cols.values.c_neg_gadget.value_1 row 0)
      (air.cols.values.c_neg_gadget.value_2 row 0)
      (air.cols.values.c_neg_gadget.value_3 row 0)
    ++ AbsCRangeBuses air row
    ++
    -- (d) `AddGadget` on `remainder_comp + abs_remainder`
    --     (`constraints.rs:563`), then the range checks on
    --     `abs_remainder` (`constraints.rs:570`).
    AddGadget.AbsBuses abs_rem_alu_event
      (air.cols.values.rem_neg_gadget.value_0 row 0)
      (air.cols.values.rem_neg_gadget.value_1 row 0)
      (air.cols.values.rem_neg_gadget.value_2 row 0)
      (air.cols.values.rem_neg_gadget.value_3 row 0)
    ++ AbsRemainderRangeBuses air row
    ++
    -- (e) `LtWordU16Gadget` (`constraints.rs:586`).
    LtWordU16Gadget.AbsBuses
      remainder_check_multiplicity
      (air.cols.values.remainder_lt_gadget.comparison_limbs_0 row 0)
      (air.cols.values.remainder_lt_gadget.comparison_limbs_1 row 0)
      (air.cols.values.remainder_lt_gadget.bit row 0)
    ++
    -- (f) `U16MSBGadget` × 7 (3 msbs × 2 gated modes, plus `quot_msb`).
    U16MSBGadget.AbsBuses is_real_not_word b_3 b_msb
    ++ U16MSBGadget.AbsBuses is_real_not_word c_3 c_msb
    ++ U16MSBGadget.AbsBuses is_real_not_word r_3 r_msb
    ++ U16MSBGadget.AbsBuses is_word_operation b_1 b_msb
    ++ U16MSBGadget.AbsBuses is_word_operation c_1 c_msb
    ++ U16MSBGadget.AbsBuses is_word_operation r_1 r_msb
    -- `constraints.rs:635-640`: U16Range lookup on
    -- `2 * q_1 - quot_msb * 65536` enforcing `quot_msb = bit-15(q_1)`.
    ++ U16MSBGadget.AbsBuses is_word_operation q_1 quot_msb
    ++
    -- (g) Chip-own: the remaining 16 slice u16 range checks
    --     (`constraints.rs:645`, `:646`, `:652`) and the chip's own
    --     `looked_alu` entry (`constraints.rs:717`).
    SliceRangeBuses air row
    ++ LookedAluBuses air row

  /-- The raw bus entries `DivRemChip` emits per row: a restatement of
      `Extraction.constrain_interactions`'s 121-entry list with the
      column accessors named, in the same order. The bus id is the head
      of each entry (`4` = ALU, `5` = byte); `AbsBuses` above is the same
      list in typed form, as `bus_row_equiv` proves. -/
  @[constraint_and_interaction_simplification]
  def raw_bus_row (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
  : List (FKB × List FKB) :=
    let a_0 := air.cols.values.a_0 row 0
    let a_1 := air.cols.values.a_1 row 0
    let a_2 := air.cols.values.a_2 row 0
    let a_3 := air.cols.values.a_3 row 0
    let b_1 := air.cols.values.b_1 row 0
    let b_3 := air.cols.values.b_3 row 0
    let c_0 := air.cols.values.c_0 row 0
    let c_1 := air.cols.values.c_1 row 0
    let c_2 := air.cols.values.c_2 row 0
    let c_3 := air.cols.values.c_3 row 0
    let b_raw_0 := air.cols.values.b_raw_0 row 0
    let b_raw_1 := air.cols.values.b_raw_1 row 0
    let b_raw_2 := air.cols.values.b_raw_2 row 0
    let b_raw_3 := air.cols.values.b_raw_3 row 0
    let c_raw_0 := air.cols.values.c_raw_0 row 0
    let c_raw_1 := air.cols.values.c_raw_1 row 0
    let c_raw_2 := air.cols.values.c_raw_2 row 0
    let c_raw_3 := air.cols.values.c_raw_3 row 0
    let quotient_0 := air.cols.values.quotient_0 row 0
    let quotient_1 := air.cols.values.quotient_1 row 0
    let quotient_2 := air.cols.values.quotient_2 row 0
    let quotient_3 := air.cols.values.quotient_3 row 0
    let quotient_comp_0 := air.cols.values.quotient_comp_0 row 0
    let quotient_comp_1 := air.cols.values.quotient_comp_1 row 0
    let quotient_comp_2 := air.cols.values.quotient_comp_2 row 0
    let quotient_comp_3 := air.cols.values.quotient_comp_3 row 0
    let remainder_comp_0 := air.cols.values.remainder_comp_0 row 0
    let remainder_comp_1 := air.cols.values.remainder_comp_1 row 0
    let remainder_comp_2 := air.cols.values.remainder_comp_2 row 0
    let remainder_comp_3 := air.cols.values.remainder_comp_3 row 0
    let remainder_0 := air.cols.values.remainder_0 row 0
    let remainder_1 := air.cols.values.remainder_1 row 0
    let remainder_2 := air.cols.values.remainder_2 row 0
    let remainder_3 := air.cols.values.remainder_3 row 0
    let abs_remainder_0 := air.cols.values.abs_remainder_0 row 0
    let abs_remainder_1 := air.cols.values.abs_remainder_1 row 0
    let abs_remainder_2 := air.cols.values.abs_remainder_2 row 0
    let abs_remainder_3 := air.cols.values.abs_remainder_3 row 0
    let abs_c_0 := air.cols.values.abs_c_0 row 0
    let abs_c_1 := air.cols.values.abs_c_1 row 0
    let abs_c_2 := air.cols.values.abs_c_2 row 0
    let abs_c_3 := air.cols.values.abs_c_3 row 0
    let c_times_quotient_0 := air.cols.values.c_times_quotient_0 row 0
    let c_times_quotient_1 := air.cols.values.c_times_quotient_1 row 0
    let c_times_quotient_2 := air.cols.values.c_times_quotient_2 row 0
    let c_times_quotient_3 := air.cols.values.c_times_quotient_3 row 0
    let c_times_quotient_4 := air.cols.values.c_times_quotient_4 row 0
    let c_times_quotient_5 := air.cols.values.c_times_quotient_5 row 0
    let c_times_quotient_6 := air.cols.values.c_times_quotient_6 row 0
    let c_times_quotient_7 := air.cols.values.c_times_quotient_7 row 0
    let lo_carry_0 := air.cols.values.c_times_quotient_lower.carry_0 row 0
    let lo_carry_1 := air.cols.values.c_times_quotient_lower.carry_1 row 0
    let lo_carry_2 := air.cols.values.c_times_quotient_lower.carry_2 row 0
    let lo_carry_3 := air.cols.values.c_times_quotient_lower.carry_3 row 0
    let lo_carry_4 := air.cols.values.c_times_quotient_lower.carry_4 row 0
    let lo_carry_5 := air.cols.values.c_times_quotient_lower.carry_5 row 0
    let lo_carry_6 := air.cols.values.c_times_quotient_lower.carry_6 row 0
    let lo_carry_7 := air.cols.values.c_times_quotient_lower.carry_7 row 0
    let lo_carry_8 := air.cols.values.c_times_quotient_lower.carry_8 row 0
    let lo_carry_9 := air.cols.values.c_times_quotient_lower.carry_9 row 0
    let lo_carry_10 := air.cols.values.c_times_quotient_lower.carry_10 row 0
    let lo_carry_11 := air.cols.values.c_times_quotient_lower.carry_11 row 0
    let lo_carry_12 := air.cols.values.c_times_quotient_lower.carry_12 row 0
    let lo_carry_13 := air.cols.values.c_times_quotient_lower.carry_13 row 0
    let lo_carry_14 := air.cols.values.c_times_quotient_lower.carry_14 row 0
    let lo_carry_15 := air.cols.values.c_times_quotient_lower.carry_15 row 0
    let lo_product_0 := air.cols.values.c_times_quotient_lower.product_0 row 0
    let lo_product_1 := air.cols.values.c_times_quotient_lower.product_1 row 0
    let lo_product_2 := air.cols.values.c_times_quotient_lower.product_2 row 0
    let lo_product_3 := air.cols.values.c_times_quotient_lower.product_3 row 0
    let lo_product_4 := air.cols.values.c_times_quotient_lower.product_4 row 0
    let lo_product_5 := air.cols.values.c_times_quotient_lower.product_5 row 0
    let lo_product_6 := air.cols.values.c_times_quotient_lower.product_6 row 0
    let lo_product_7 := air.cols.values.c_times_quotient_lower.product_7 row 0
    let lo_product_8 := air.cols.values.c_times_quotient_lower.product_8 row 0
    let lo_product_9 := air.cols.values.c_times_quotient_lower.product_9 row 0
    let lo_product_10 := air.cols.values.c_times_quotient_lower.product_10 row 0
    let lo_product_11 := air.cols.values.c_times_quotient_lower.product_11 row 0
    let lo_product_12 := air.cols.values.c_times_quotient_lower.product_12 row 0
    let lo_product_13 := air.cols.values.c_times_quotient_lower.product_13 row 0
    let lo_product_14 := air.cols.values.c_times_quotient_lower.product_14 row 0
    let lo_product_15 := air.cols.values.c_times_quotient_lower.product_15 row 0
    let lo_b_low_0 := air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_0 row 0
    let lo_b_low_1 := air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_1 row 0
    let lo_b_low_2 := air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_2 row 0
    let lo_b_low_3 := air.cols.values.c_times_quotient_lower.b_lower_byte.low_bytes_3 row 0
    let lo_c_low_0 := air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_0 row 0
    let lo_c_low_1 := air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_1 row 0
    let lo_c_low_2 := air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_2 row 0
    let lo_c_low_3 := air.cols.values.c_times_quotient_lower.c_lower_byte.low_bytes_3 row 0
    let lo_b_msb := air.cols.values.c_times_quotient_lower.b_msb row 0
    let lo_c_msb := air.cols.values.c_times_quotient_lower.c_msb row 0
    let lo_prd_msb := air.cols.values.c_times_quotient_lower.product_msb.msb row 0
    let hi_carry_0 := air.cols.values.c_times_quotient_upper.carry_0 row 0
    let hi_carry_1 := air.cols.values.c_times_quotient_upper.carry_1 row 0
    let hi_carry_2 := air.cols.values.c_times_quotient_upper.carry_2 row 0
    let hi_carry_3 := air.cols.values.c_times_quotient_upper.carry_3 row 0
    let hi_carry_4 := air.cols.values.c_times_quotient_upper.carry_4 row 0
    let hi_carry_5 := air.cols.values.c_times_quotient_upper.carry_5 row 0
    let hi_carry_6 := air.cols.values.c_times_quotient_upper.carry_6 row 0
    let hi_carry_7 := air.cols.values.c_times_quotient_upper.carry_7 row 0
    let hi_carry_8 := air.cols.values.c_times_quotient_upper.carry_8 row 0
    let hi_carry_9 := air.cols.values.c_times_quotient_upper.carry_9 row 0
    let hi_carry_10 := air.cols.values.c_times_quotient_upper.carry_10 row 0
    let hi_carry_11 := air.cols.values.c_times_quotient_upper.carry_11 row 0
    let hi_carry_12 := air.cols.values.c_times_quotient_upper.carry_12 row 0
    let hi_carry_13 := air.cols.values.c_times_quotient_upper.carry_13 row 0
    let hi_carry_14 := air.cols.values.c_times_quotient_upper.carry_14 row 0
    let hi_carry_15 := air.cols.values.c_times_quotient_upper.carry_15 row 0
    let hi_product_0 := air.cols.values.c_times_quotient_upper.product_0 row 0
    let hi_product_1 := air.cols.values.c_times_quotient_upper.product_1 row 0
    let hi_product_2 := air.cols.values.c_times_quotient_upper.product_2 row 0
    let hi_product_3 := air.cols.values.c_times_quotient_upper.product_3 row 0
    let hi_product_4 := air.cols.values.c_times_quotient_upper.product_4 row 0
    let hi_product_5 := air.cols.values.c_times_quotient_upper.product_5 row 0
    let hi_product_6 := air.cols.values.c_times_quotient_upper.product_6 row 0
    let hi_product_7 := air.cols.values.c_times_quotient_upper.product_7 row 0
    let hi_product_8 := air.cols.values.c_times_quotient_upper.product_8 row 0
    let hi_product_9 := air.cols.values.c_times_quotient_upper.product_9 row 0
    let hi_product_10 := air.cols.values.c_times_quotient_upper.product_10 row 0
    let hi_product_11 := air.cols.values.c_times_quotient_upper.product_11 row 0
    let hi_product_12 := air.cols.values.c_times_quotient_upper.product_12 row 0
    let hi_product_13 := air.cols.values.c_times_quotient_upper.product_13 row 0
    let hi_product_14 := air.cols.values.c_times_quotient_upper.product_14 row 0
    let hi_product_15 := air.cols.values.c_times_quotient_upper.product_15 row 0
    let hi_b_low_0 := air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_0 row 0
    let hi_b_low_1 := air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_1 row 0
    let hi_b_low_2 := air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_2 row 0
    let hi_b_low_3 := air.cols.values.c_times_quotient_upper.b_lower_byte.low_bytes_3 row 0
    let hi_c_low_0 := air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_0 row 0
    let hi_c_low_1 := air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_1 row 0
    let hi_c_low_2 := air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_2 row 0
    let hi_c_low_3 := air.cols.values.c_times_quotient_upper.c_lower_byte.low_bytes_3 row 0
    let hi_b_msb := air.cols.values.c_times_quotient_upper.b_msb row 0
    let hi_c_msb := air.cols.values.c_times_quotient_upper.c_msb row 0
    let hi_prd_msb := air.cols.values.c_times_quotient_upper.product_msb.msb row 0
    let lt_comparison_limbs_0 := air.cols.values.remainder_lt_gadget.comparison_limbs_0 row 0
    let lt_comparison_limbs_1 := air.cols.values.remainder_lt_gadget.comparison_limbs_1 row 0
    let lt_bit := air.cols.values.remainder_lt_gadget.bit row 0
    let c_neg_val_0 := air.cols.values.c_neg_gadget.value_0 row 0
    let c_neg_val_1 := air.cols.values.c_neg_gadget.value_1 row 0
    let c_neg_val_2 := air.cols.values.c_neg_gadget.value_2 row 0
    let c_neg_val_3 := air.cols.values.c_neg_gadget.value_3 row 0
    let rem_neg_val_0 := air.cols.values.rem_neg_gadget.value_0 row 0
    let rem_neg_val_1 := air.cols.values.rem_neg_gadget.value_1 row 0
    let rem_neg_val_2 := air.cols.values.rem_neg_gadget.value_2 row 0
    let rem_neg_val_3 := air.cols.values.rem_neg_gadget.value_3 row 0
    let carry_0 := air.cols.values.carry_0 row 0
    let carry_1 := air.cols.values.carry_1 row 0
    let carry_2 := air.cols.values.carry_2 row 0
    let carry_3 := air.cols.values.carry_3 row 0
    let carry_4 := air.cols.values.carry_4 row 0
    let carry_5 := air.cols.values.carry_5 row 0
    let carry_6 := air.cols.values.carry_6 row 0
    let carry_7 := air.cols.values.carry_7 row 0
    let is_div := air.cols.values.is_div row 0
    let is_divu := air.cols.values.is_divu row 0
    let is_rem := air.cols.values.is_rem row 0
    let is_remu := air.cols.values.is_remu row 0
    let is_divw := air.cols.values.is_divw row 0
    let is_remw := air.cols.values.is_remw row 0
    let is_divuw := air.cols.values.is_divuw row 0
    let is_remuw := air.cols.values.is_remuw row 0
    let b_msb := air.cols.values.b_msb.msb row 0
    let rem_msb := air.cols.values.rem_msb.msb row 0
    let c_msb := air.cols.values.c_msb.msb row 0
    let quot_msb := air.cols.values.quot_msb.msb row 0
    let is_real_not_word := air.cols.values.is_real_not_word row 0
    let rem_neg := air.cols.values.rem_neg row 0
    let abs_c_alu_event := air.cols.values.abs_c_alu_event row 0
    let abs_rem_alu_event := air.cols.values.abs_rem_alu_event row 0
    let is_real := air.cols.values.is_real row 0
    let remainder_check_multiplicity := air.cols.values.remainder_check_multiplicity row 0
    [
      -- `MulGadget` on `c · quotient_comp`, low 64 bits (`constraints.rs:254`):
      -- 8 `U16ToU8GadgetSafe` entries on `quotient_comp` and `c`, 2 MSB byte
      -- lookups, the (unconditioned, gate 0) product-MSB entry, 16 carry
      -- range checks and 8 product byte-pair checks.
      (is_real, [5, 7, 0, 0, lo_b_low_0, ((quotient_comp_0 - lo_b_low_0) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_b_low_1, ((quotient_comp_1 - lo_b_low_1) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_b_low_2, ((quotient_comp_2 - lo_b_low_2) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_b_low_3, ((quotient_comp_3 - lo_b_low_3) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_c_low_0, ((c_0 - lo_c_low_0) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_c_low_1, ((c_1 - lo_c_low_1) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_c_low_2, ((c_2 - lo_c_low_2) * 2122383361)]),
      (is_real, [5, 7, 0, 0, lo_c_low_3, ((c_3 - lo_c_low_3) * 2122383361)]),
      (is_real, [5, 6, lo_b_msb, 0, ((quotient_comp_3 - lo_b_low_3) * 2122383361), 0]),
      (is_real, [5, 6, lo_c_msb, 0, ((c_3 - lo_c_low_3) * 2122383361), 0]),
      (0, [5, 8, ((2 * c_times_quotient_1) - (lo_prd_msb * 65536)), 0, 0, 0]),
      (is_real, [5, 8, lo_carry_0, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_1, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_2, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_3, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_4, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_5, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_6, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_7, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_8, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_9, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_10, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_11, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_12, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_13, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_14, 0, 0, 0]),
      (is_real, [5, 8, lo_carry_15, 0, 0, 0]),
      (is_real, [5, 7, 0, 0, lo_product_0, lo_product_1]),
      (is_real, [5, 7, 0, 0, lo_product_2, lo_product_3]),
      (is_real, [5, 7, 0, 0, lo_product_4, lo_product_5]),
      (is_real, [5, 7, 0, 0, lo_product_6, lo_product_7]),
      (is_real, [5, 7, 0, 0, lo_product_8, lo_product_9]),
      (is_real, [5, 7, 0, 0, lo_product_10, lo_product_11]),
      (is_real, [5, 7, 0, 0, lo_product_12, lo_product_13]),
      (is_real, [5, 7, 0, 0, lo_product_14, lo_product_15]),
      -- `MulGadget` on `c · quotient_comp`, high 64 bits (`constraints.rs:273`),
      -- gated by `is_real_not_word`.
      (is_real_not_word, [5, 7, 0, 0, hi_b_low_0, ((quotient_comp_0 - hi_b_low_0) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_b_low_1, ((quotient_comp_1 - hi_b_low_1) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_b_low_2, ((quotient_comp_2 - hi_b_low_2) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_b_low_3, ((quotient_comp_3 - hi_b_low_3) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_c_low_0, ((c_0 - hi_c_low_0) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_c_low_1, ((c_1 - hi_c_low_1) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_c_low_2, ((c_2 - hi_c_low_2) * 2122383361)]),
      (is_real_not_word, [5, 7, 0, 0, hi_c_low_3, ((c_3 - hi_c_low_3) * 2122383361)]),
      (is_real_not_word, [5, 6, hi_b_msb, 0, ((quotient_comp_3 - hi_b_low_3) * 2122383361), 0]),
      (is_real_not_word, [5, 6, hi_c_msb, 0, ((c_3 - hi_c_low_3) * 2122383361), 0]),
      (0, [5, 8, ((2 * c_times_quotient_5) - (hi_prd_msb * 65536)), 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_0, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_1, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_2, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_3, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_4, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_5, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_6, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_7, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_8, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_9, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_10, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_11, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_12, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_13, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_14, 0, 0, 0]),
      (is_real_not_word, [5, 8, hi_carry_15, 0, 0, 0]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_0, hi_product_1]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_2, hi_product_3]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_4, hi_product_5]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_6, hi_product_7]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_8, hi_product_9]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_10, hi_product_11]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_12, hi_product_13]),
      (is_real_not_word, [5, 7, 0, 0, hi_product_14, hi_product_15]),
      -- u16 range checks on the `c · quotient + remainder` carry chain
      -- (`constraints.rs:423`).
      (is_real, [5, 8, ((c_times_quotient_0 + remainder_comp_0) - (carry_0 * 65536)), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_1 + remainder_comp_1) - (carry_1 * 65536)) + carry_0), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_2 + remainder_comp_2) - (carry_2 * 65536)) + carry_1), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_3 + remainder_comp_3) - (carry_3 * 65536)) + carry_2), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_4 + (rem_neg * 65535)) - (carry_4 * 65536)) + carry_3), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_5 + (rem_neg * 65535)) - (carry_5 * 65536)) + carry_4), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_6 + (rem_neg * 65535)) - (carry_6 * 65536)) + carry_5), 0, 0, 0]),
      (is_real, [5, 8, (((c_times_quotient_7 + (rem_neg * 65535)) - (carry_7 * 65536)) + carry_6), 0, 0, 0]),
      -- The two `looking_alu(ADD, 0, …)` sub-events that define `abs_c` and
      -- `abs_remainder` by `c + abs_c = 0` / `remainder + abs_remainder = 0`
      -- (`constraints.rs:501` and `:508`).
      (abs_c_alu_event, [4, 0, 0, 0, 0, 0, c_0, c_1, c_2, c_3, abs_c_0, abs_c_1, abs_c_2, abs_c_3]),
      (abs_rem_alu_event, [4, 0, 0, 0, 0, 0, remainder_0, remainder_1, remainder_2, remainder_3, abs_remainder_0, abs_remainder_1, abs_remainder_2, abs_remainder_3]),
      -- `AddGadget` on `c + abs_c` (`constraints.rs:552`).
      (abs_c_alu_event, [5, 8, c_neg_val_0, 0, 0, 0]),
      (abs_c_alu_event, [5, 8, c_neg_val_1, 0, 0, 0]),
      (abs_c_alu_event, [5, 8, c_neg_val_2, 0, 0, 0]),
      (abs_c_alu_event, [5, 8, c_neg_val_3, 0, 0, 0]),
      -- u16 range checks on `abs_c` (`constraints.rs:559`).
      (is_real, [5, 8, abs_c_0, 0, 0, 0]),
      (is_real, [5, 8, abs_c_1, 0, 0, 0]),
      (is_real, [5, 8, abs_c_2, 0, 0, 0]),
      (is_real, [5, 8, abs_c_3, 0, 0, 0]),
      -- `AddGadget` on `remainder_comp + abs_remainder` (`constraints.rs:563`).
      (abs_rem_alu_event, [5, 8, rem_neg_val_0, 0, 0, 0]),
      (abs_rem_alu_event, [5, 8, rem_neg_val_1, 0, 0, 0]),
      (abs_rem_alu_event, [5, 8, rem_neg_val_2, 0, 0, 0]),
      (abs_rem_alu_event, [5, 8, rem_neg_val_3, 0, 0, 0]),
      -- u16 range checks on `abs_remainder` (`constraints.rs:570`).
      (is_real, [5, 8, abs_remainder_0, 0, 0, 0]),
      (is_real, [5, 8, abs_remainder_1, 0, 0, 0]),
      (is_real, [5, 8, abs_remainder_2, 0, 0, 0]),
      (is_real, [5, 8, abs_remainder_3, 0, 0, 0]),
      -- `LtWordU16Gadget` on `abs_remainder < max(abs_c, 1)`
      -- (`constraints.rs:586`).
      (remainder_check_multiplicity, [5, 8, ((lt_comparison_limbs_0 - lt_comparison_limbs_1) + (lt_bit * 65536)), 0, 0, 0]),
      -- `U16MSBGadget` on the top limbs of `b`, `c`, `remainder`, for 64-bit
      -- operations (`constraints.rs:610`).
      (is_real_not_word, [5, 8, ((2 * b_3) - (b_msb * 65536)), 0, 0, 0]),
      (is_real_not_word, [5, 8, ((2 * c_3) - (c_msb * 65536)), 0, 0, 0]),
      (is_real_not_word, [5, 8, ((2 * remainder_3) - (rem_msb * 65536)), 0, 0, 0]),
      -- `U16MSBGadget` on limb 1 of `b`, `c`, `remainder` and `quotient`, for
      -- word operations (`constraints.rs:626` and `:635`).
      ((((is_divw + is_remw) + is_divuw) + is_remuw), [5, 8, ((2 * b_1) - (b_msb * 65536)), 0, 0, 0]),
      ((((is_divw + is_remw) + is_divuw) + is_remuw), [5, 8, ((2 * c_1) - (c_msb * 65536)), 0, 0, 0]),
      ((((is_divw + is_remw) + is_divuw) + is_remuw), [5, 8, ((2 * remainder_1) - (rem_msb * 65536)), 0, 0, 0]),
      ((((is_divw + is_remw) + is_divuw) + is_remuw), [5, 8, ((2 * quotient_1) - (quot_msb * 65536)), 0, 0, 0]),
      -- u16 range checks on `quotient` (`constraints.rs:645`).
      (is_real, [5, 8, quotient_0, 0, 0, 0]),
      (is_real, [5, 8, quotient_1, 0, 0, 0]),
      (is_real, [5, 8, quotient_2, 0, 0, 0]),
      (is_real, [5, 8, quotient_3, 0, 0, 0]),
      -- u16 range checks on `remainder` (`constraints.rs:646`).
      (is_real, [5, 8, remainder_0, 0, 0, 0]),
      (is_real, [5, 8, remainder_1, 0, 0, 0]),
      (is_real, [5, 8, remainder_2, 0, 0, 0]),
      (is_real, [5, 8, remainder_3, 0, 0, 0]),
      -- u16 range checks on `c_times_quotient` (`constraints.rs:652`).
      (is_real, [5, 8, c_times_quotient_0, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_1, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_2, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_3, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_4, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_5, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_6, 0, 0, 0]),
      (is_real, [5, 8, c_times_quotient_7, 0, 0, 0]),
      -- The chip's own `looked_alu` entry, with the selector-encoded opcode and
      -- the *raw* register operands `b_raw`, `c_raw` (`constraints.rs:717`).
      (-(is_real), [4, ((((((((is_divu * 35) + (is_remu * 37)) + (is_div * 34)) + (is_rem * 36)) + (is_divw * 49)) + (is_remw * 51)) + (is_divuw * 50)) + (is_remuw * 52)), a_0, a_1, a_2, a_3, b_raw_0, b_raw_1, b_raw_2, b_raw_3, c_raw_0, c_raw_1, c_raw_2, c_raw_3])
    ]

  @[constraint_and_interaction_simplification]
  def constrain_interactions (air : Valid_DivRemChip FKB ExtF) : Prop :=
    air.bus =
      List.flatMap
        (fun row ↦ raw_bus_row air row)
        (List.range (air.last_row + 1))

  /-- `Extraction.allHold` ↔ `constrain_interactions ∧ AbsConstraints`.
      For `MulChip` (5 selectors, 51 constraints) the analogous lemma
      closes by a single `simp` invocation. For `DivRemChip` (8
      selectors, 337 extracted constraints, 2 nested `MulGadget`s +
      `LtWordU16Gadget` + 2 `AddGadget`s + `IsZeroWordGadget` + 2
      `IsEqualWordGadget`s + 7 `U16MSBGadget`s) it is a heavyweight
      derivation — the same simp set, but expected to be much slower.
      Drives `allHold_abs` (and via it, the chip-level `spec`s). -/
  @[constraint_and_interaction_simplification]
  def allHold_simplified
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
  : Prop :=
    constrain_interactions air ∧ AbsConstraints air row

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

  set_option maxRecDepth 4_000_000 in
  /-- The typed `bus_row` is the extracted interaction list, entry for
      entry: deserialising `raw_bus_row` — the restatement of
      `Extraction.constrain_interactions`'s 121 entries that
      `allHold_iff_allHold_simplified` ties to the extraction — gives
      `AbsBuses`. As for `MulChip` and `LtChip`, both sides reduce to the
      same `BusRow` by `dsimp` alone. -/
  @[simp]
  lemma bus_row_equiv (air : Valid_DivRemChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (DivRemChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    dsimp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      BusRow.append_eq,
      DivRemChip.ConstraintsAndBuses.CarryChainBuses,
      DivRemChip.ConstraintsAndBuses.AbsAluEventBuses,
      DivRemChip.ConstraintsAndBuses.AbsCRangeBuses,
      DivRemChip.ConstraintsAndBuses.AbsRemainderRangeBuses,
      DivRemChip.ConstraintsAndBuses.SliceRangeBuses,
      DivRemChip.ConstraintsAndBuses.LookedAluBuses,
      MulGadget.AbsBuses,
      AddGadget.AbsBuses,
      LtWordU16Gadget.AbsBuses,
      U16MSBGadget.AbsBuses,
      U16ToU8GadgetSafe.AbsBuses,
      pico_encapsulation,
    ]

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

  set_option linter.constructorNameAsVariable false in
  /-- `b` and `c` in terms of the raw operands `b_raw`, `c_raw` that the ALU
      bus carries (`AbsConstraints` (3), `constraints.rs:178-195`): the low
      32 bits are equal; the upper limbs are the raw ones for 64-bit
      operations and `b_neg · 0xFFFF` / `c_neg · 0xFFFF` for word
      operations. -/
  lemma operands_of_raw
    [Field F] [Field ExtF]
    (air : Valid_DivRemChip F ExtF) (row : ℕ)
    (h_constraints : AbsConstraints air row)
  :
    air.cols.values.b_0 row 0 = air.cols.values.b_raw_0 row 0 ∧
    air.cols.values.b_1 row 0 = air.cols.values.b_raw_1 row 0 ∧
    air.cols.values.c_0 row 0 = air.cols.values.c_raw_0 row 0 ∧
    air.cols.values.c_1 row 0 = air.cols.values.c_raw_1 row 0 ∧
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
     air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 0 →
      air.cols.values.b_2 row 0 = air.cols.values.b_raw_2 row 0 ∧
      air.cols.values.b_3 row 0 = air.cols.values.b_raw_3 row 0 ∧
      air.cols.values.c_2 row 0 = air.cols.values.c_raw_2 row 0 ∧
      air.cols.values.c_3 row 0 = air.cols.values.c_raw_3 row 0) ∧
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
     air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      air.cols.values.b_2 row 0 = air.cols.values.b_neg row 0 * 65535 ∧
      air.cols.values.b_3 row 0 = air.cols.values.b_neg row 0 * 65535 ∧
      air.cols.values.c_2 row 0 = air.cols.values.c_neg row 0 * 65535 ∧
      air.cols.values.c_3 row 0 = air.cols.values.c_neg row 0 * 65535)
  := by
    simp only [AbsConstraints] at h_constraints
    obtain ⟨-, -, -, -, h_b_0, h_c_0, h_b_1, h_c_1, h_b_2, h_c_2, h_b_3, h_c_3, -⟩ :=
      h_constraints
    refine ⟨?_, ?_, ?_, ?_, fun h_w => ⟨?_, ?_, ?_, ?_⟩, fun h_w => ⟨?_, ?_, ?_, ?_⟩⟩
    · linear_combination -h_b_0
    · linear_combination -h_b_1
    · linear_combination -h_c_0
    · linear_combination -h_c_1
    · linear_combination h_b_2 +
        (air.cols.values.b_neg row 0 * 65535 - air.cols.values.b_raw_2 row 0) * h_w
    · linear_combination h_b_3 +
        (air.cols.values.b_neg row 0 * 65535 - air.cols.values.b_raw_3 row 0) * h_w
    · linear_combination h_c_2 +
        (air.cols.values.c_neg row 0 * 65535 - air.cols.values.c_raw_2 row 0) * h_w
    · linear_combination h_c_3 +
        (air.cols.values.c_neg row 0 * 65535 - air.cols.values.c_raw_3 row 0) * h_w
    · linear_combination h_b_2 -
        (air.cols.values.b_raw_2 row 0 - air.cols.values.b_neg row 0 * 65535) * h_w
    · linear_combination h_b_3 -
        (air.cols.values.b_raw_3 row 0 - air.cols.values.b_neg row 0 * 65535) * h_w
    · linear_combination h_c_2 -
        (air.cols.values.c_raw_2 row 0 - air.cols.values.c_neg row 0 * 65535) * h_w
    · linear_combination h_c_3 -
        (air.cols.values.c_raw_3 row 0 - air.cols.values.c_neg row 0 * 65535) * h_w

  set_option linter.constructorNameAsVariable false in
  /-- The raw operands `b_raw`, `c_raw` and the computational `b`, `c` are
      u16 limbs on a real row. The bus contract gives the raw ones: the
      DIV/REM opcodes are not in `ALUBus.operandsInternal`, so the ALU
      bus externals of the chip's looked entry carry their range. `b` and
      `c` follow by `operands_of_raw`, since `b_neg` and `c_neg` are
      boolean. -/
  lemma operand_range
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
  :
    ALUBus.operandRange
      (air.cols.values.b_raw_0 row 0) (air.cols.values.b_raw_1 row 0)
      (air.cols.values.b_raw_2 row 0) (air.cols.values.b_raw_3 row 0)
      (air.cols.values.c_raw_0 row 0) (air.cols.values.c_raw_1 row 0)
      (air.cols.values.c_raw_2 row 0) (air.cols.values.c_raw_3 row 0) ∧
    ALUBus.operandRange
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨b_div, b_divu, b_rem, b_remu, b_divw, b_remw, b_divuw, b_remuw, h_sum⟩ :=
      selector_breakdown air row h_constraints
    obtain ⟨h_b_0, h_b_1, h_c_0, h_c_1, h_not_word, h_word⟩ :=
      operands_of_raw air row h_constraints
    have h_neg : (air.cols.values.b_neg row 0 = 0 ∨ air.cols.values.b_neg row 0 = 1) ∧
        (air.cols.values.c_neg row 0 = 0 ∨ air.cols.values.c_neg row 0 = 1) := by
      have := h_constraints
      simp [AbsConstraints, sub_eq_zero] at this
      clear *- this; aesop
    have h_ext : bus_row_ext_asm (LookedAluBuses air row) := by
      simp [AbsBuses] at h_ext; aesop
    simp [bus_row_ext_asm, LookedAluBuses] at h_ext
    simp [ALUBus.externals, ALUBus.validOpcode, ALUBus.operandsInternal,
          ALUBus.operandRange, h_is_real] at h_ext
    have h_raw :
      ALUBus.operandRange
        (air.cols.values.b_raw_0 row 0) (air.cols.values.b_raw_1 row 0)
        (air.cols.values.b_raw_2 row 0) (air.cols.values.b_raw_3 row 0)
        (air.cols.values.c_raw_0 row 0) (air.cols.values.c_raw_1 row 0)
        (air.cols.values.c_raw_2 row 0) (air.cols.values.c_raw_3 row 0) := by
      simp only [ALUBus.operandRange]
      apply h_ext.2 <;> clear h_ext h_not_word h_word h_neg <;> grind
    refine ⟨h_raw, ?_⟩
    simp only [ALUBus.operandRange] at h_raw ⊢
    rw [h_b_0, h_b_1, h_c_0, h_c_1]
    have h_w : air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
               air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 0 ∨
               air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
               air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 := by
      clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum; grind
    rcases h_w with h_w | h_w
    · obtain ⟨h_b_2, h_b_3, h_c_2, h_c_3⟩ := h_not_word h_w
      rw [h_b_2, h_b_3, h_c_2, h_c_3]; exact h_raw
    · obtain ⟨h_b_2, h_b_3, h_c_2, h_c_3⟩ := h_word h_w
      rw [h_b_2, h_b_3, h_c_2, h_c_3]
      obtain ⟨h_b_neg, h_c_neg⟩ := h_neg
      rcases h_b_neg with h_b_neg | h_b_neg <;> rcases h_c_neg with h_c_neg | h_c_neg <;>
        simp [h_b_neg, h_c_neg, h_raw]

  -- =====================================================================
  -- Preprocessing lemma: bus split + gadget-spec application.
  --
  -- Every chip-level `spec_*` proof used to start with the same
  -- boilerplate:
  --   (i)  peel `bus_row_ext_asm` / `bus_row_wf_asm` over the 18-way
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
    -- (4) Lower `MulGadget` thunk — `c · quotient_comp` low 64 bits.
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
    -- (5) Upper `MulGadget` thunk — `c · quotient_comp` high 64 bits.
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
    -- (6) `IsEqualWordGadget` thunk: `b == #v[0,0,0,0x8000]` (i64::MIN),
    --     gated by `is_real_not_word = 1`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      let result := air.cols.values.is_overflow_b.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.b_0 row 0 = 0 ∧ air.cols.values.b_1 row 0 = 0 ∧
         air.cols.values.b_2 row 0 = 0 ∧ air.cols.values.b_3 row 0 = 32768))) ∧
    -- (7) `IsEqualWordGadget` thunk: `c == #v[0xFFFF,…]` (−1, 64-bit),
    --     gated by `is_real_not_word = 1`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      let result := air.cols.values.is_overflow_c.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.c_0 row 0 = 65535 ∧ air.cols.values.c_1 row 0 = 65535 ∧
         air.cols.values.c_2 row 0 = 65535 ∧ air.cols.values.c_3 row 0 = 65535))) ∧
    -- (8) `IsEqualWordGadget` thunk: 32-bit `b_lo == i32::MIN`, gated
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
    -- (9) `IsEqualWordGadget` thunk: 32-bit `c_lo == -1`, gated by
    --     `is_word_operation = 1`.
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0 +
     air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      let result := air.cols.values.is_overflow_c.is_diff_zero.result row 0
      (result = 0 ∨ result = 1) ∧
      (result = 1 ↔
        (air.cols.values.c_0 row 0 = 65535 ∧ air.cols.values.c_1 row 0 = 65535 ∧
         (0 : FKB) = 0 ∧ (0 : FKB) = 0))) ∧
    -- (10) `IsZeroWordGadget` thunk on `c`.
    (let result := air.cols.values.is_c_0.result row 0
     (result = 0 ∨ result = 1) ∧
     (result = 1 ↔
       (air.cols.values.c_0 row 0 = 0 ∧ air.cols.values.c_1 row 0 = 0 ∧
         air.cols.values.c_2 row 0 = 0 ∧ air.cols.values.c_3 row 0 = 0))) ∧
    -- (11) `AddGadget` thunk: `c + abs_c = c_neg_gadget.value`, gated
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
    -- (12) `AddGadget` thunk: `rc + abs_r = rem_neg_gadget.value`,
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
    -- (13) `LtWordU16Gadget` thunk: `abs_remainder < max_abs_c_or_1`,
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
    -- (14) `U16MSBGadget` thunk on `b_msb` for `b_3`, gated by
    --      `is_real_not_word = 1`. Needs `b_3 < 65536` (external from
    --      `ALUBus.operandRange`).
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.b_3 row 0).val < 65536 →
      let msb := air.cols.values.b_msb.msb row 0
      let value := air.cols.values.b_3 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (15) `U16MSBGadget` thunk on `c_msb` for `c_3`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.c_3 row 0).val < 65536 →
      let msb := air.cols.values.c_msb.msb row 0
      let value := air.cols.values.c_3 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (16) `U16MSBGadget` thunk on `r_msb` for `r_3`.
    (air.cols.values.is_real_not_word row 0 = 1 →
      (air.cols.values.remainder_3 row 0).val < 65536 →
      let msb := air.cols.values.rem_msb.msb row 0
      let value := air.cols.values.remainder_3 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (17) `U16MSBGadget` thunk on `b_msb` for `b_1` (word-variant mode).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.b_1 row 0).val < 65536 →
      let msb := air.cols.values.b_msb.msb row 0
      let value := air.cols.values.b_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (18) `U16MSBGadget` thunk on `c_msb` for `c_1` (word-variant mode).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.c_1 row 0).val < 65536 →
      let msb := air.cols.values.c_msb.msb row 0
      let value := air.cols.values.c_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (19) `U16MSBGadget` thunk on `r_msb` for `r_1` (word-variant mode).
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.remainder_1 row 0).val < 65536 →
      let msb := air.cols.values.rem_msb.msb row 0
      let value := air.cols.values.remainder_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val)) ∧
    -- (20) `U16MSBGadget` thunk on `quot_msb` for `q_1` (word-variant mode).
    --      (`constraints.rs:635-640`) so `quot_msb` is tied to bit-15
    --      of `quotient_1` rather than being a free witness.
    (air.cols.values.is_divw  row 0 + air.cols.values.is_remw  row 0
       + air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1 →
      (air.cols.values.quotient_1 row 0).val < 65536 →
      let msb := air.cols.values.quot_msb.msb row 0
      let value := air.cols.values.quotient_1 row 0
      (msb = 0 ∧ value.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ value.val))
  := by
    have h_breakdown := selector_breakdown air row h_constraints
    have h_exclusive := selector_exclusivity air row h_constraints
    have : bus_row_ext_asm (ChipExtraBuses air row) := by
      rw [ChipExtraBuses_split]; simp [AbsBuses] at h_ext_asm ⊢; aesop
    simp [this]; clear this
    have : bus_row_wf_asm (ChipExtraBuses air row) := by
      rw [ChipExtraBuses_split]; simp [AbsBuses] at h_wf_asm ⊢; aesop
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
          -- (3) b/c from the raw operands (8)
          eq_b_raw_0, eq_c_raw_0, eq_b_raw_1, eq_c_raw_1,
          eq_b_2_ext, eq_c_2_ext, eq_b_3_ext, eq_c_3_ext,
          -- (4) quotient_comp setup (10)
          eq_qc_0, eq_qc_1,
          eq_uw_qc2, eq_sw_qc2, eq_w_q2, eq_nw_qc2,
          eq_uw_qc3, eq_sw_qc3, eq_w_q3, eq_nw_qc3,
          -- (5) remainder_comp setup (10)
          eq_rc_0, eq_rc_1,
          eq_uw_rc2, eq_sw_rc2, eq_w_r2, eq_nw_rc2,
          eq_uw_rc3, eq_sw_rc3, eq_w_r3, eq_nw_rc3,
          -- (6)-(7) MulGadget × 2
          h_mul_lo, h_mul_hi,
          -- (8a) 64-bit IsEqualWord × 2
          h_overflow_b_64, h_overflow_c_64,
          -- (8b) 32-bit IsEqualWord × 2
          h_overflow_b_32, h_overflow_c_32,
          -- (8c) is_overflow + b_neg_not_overflow + b_not_neg_not_overflow
          eq_is_overflow, eq_b_neg_not_overflow, eq_b_not_neg_not_overflow,
          -- (8d) Overflow case clamp (8)
          eq_of_q0, eq_of_q1, eq_of_q2, eq_of_q3,
          eq_of_r0, eq_of_r1, eq_of_r2, eq_of_r3,
          -- (9) `b = c·q + r` carry chain (8)
          eq_cqr0, eq_cqr1, eq_cqr2, eq_cqr3,
          eq_cqr4, eq_cqr5, eq_cqr6, eq_cqr7,
          -- (10) a = q / r per opcode (8)
          eq_aq0, eq_aq1, eq_aq2, eq_aq3,
          eq_ar0, eq_ar1, eq_ar2, eq_ar3,
          -- (11) Sign consistency (2)
          eq_rn_bn, eq_rnz_bn,
          -- (12) IsZeroWordGadget on c
          h_iszero_c,
          -- (13) Div-by-zero clamps (8)
          eq_dbz_q0, eq_dbz_q1, eq_dbz_q2, eq_dbz_q3,
          eq_dbz_r0, eq_dbz_r1, eq_dbz_r2, eq_dbz_r3,
          -- (14) Abs-values when not negative (8)
          eq_abs_c0, eq_abs_c1, eq_abs_c2, eq_abs_c3,
          eq_abs_r0, eq_abs_r1, eq_abs_r2, eq_abs_r3,
          -- (15) max_abs_c_or_1 (4)
          eq_mc0, eq_mc1, eq_mc2, eq_mc3,
          -- (16) rcm, abs_c_event, abs_rem_event (3)
          eq_rcm, eq_abs_c_event, eq_abs_rem_event,
          -- (17) AddGadget × 2
          h_add_c, h_add_rem,
          -- (18) value=0 when alu event (8)
          eq_acneg0, eq_acneg1, eq_acneg2, eq_acneg3,
          eq_arneg0, eq_arneg1, eq_arneg2, eq_arneg3,
          -- (19) LtWordU16Gadget
          h_lt,
          -- (20) Enforcing lt
          h_is_lt,
          -- (21) U16MSBGadget × 6
          h_msb_b3, h_msb_c3, h_msb_rem3,
          h_msb_b1, h_msb_c1, h_msb_rem1, h_msb_q1,
          -- (22) Boolean checks (8 selectors + 10 flags + 8 carries)
          bool_is_div, bool_is_divu, bool_is_rem, bool_is_remu,
          bool_is_divw, bool_is_remw, bool_is_divuw, bool_is_remuw,
          bool_is_overflow, bool_is_real_not_word,
          bool_b_neg, bool_b_neg_not_overflow, bool_b_not_neg_not_overflow,
          bool_rem_neg, bool_c_neg, bool_is_real,
          bool_abs_c_event, bool_abs_rem_event,
          bool_cy0, bool_cy1, bool_cy2, bool_cy3,
          bool_cy4, bool_cy5, bool_cy6, bool_cy7,
          -- (23) exactly-one selector
          eq_one_selector
        ⟩ := h_constraints
      clear h_ext_asm h_wf_asm h_exclusive
            h_mul_lo h_mul_hi h_overflow_b_64 h_overflow_c_64 h_overflow_b_32 h_overflow_c_32
            h_add_c h_add_rem h_lt h_msb_b3 h_msb_c3 h_msb_rem3
            h_msb_b1 h_msb_c1 h_msb_rem1 h_msb_q1
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
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
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
    -- Past the upper `MulGadget`, the bus chain continues with the
    -- chip-own `CarryChainBuses` and `AbsAluEventBuses`, which the
    -- gadget specs do not consume.
    replace h_constraints := h_constraints.2
    replace h_ext_asm := h_ext_asm.2.2.2; replace h_wf_asm := h_wf_asm.2.2.2
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
    -- Skip the chip-own `AbsCRangeBuses` between the two `AddGadget`s.
    replace h_constraints := h_constraints.2
    replace h_ext_asm := h_ext_asm.2.2; replace h_wf_asm := h_wf_asm.2.2
    have := AddGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    simp at this
    constructor <;> [ (clear *- this; assumption); clear this]
    -- Skip the chip-own `AbsRemainderRangeBuses` before the `LtWordU16Gadget`.
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2
    replace h_ext_asm := h_ext_asm.2.2; replace h_wf_asm := h_wf_asm.2.2
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
    constructor <;> [ (clear *- this; assumption); clear this ]
    replace h_constraints := h_constraints.2; replace h_ext_asm := h_ext_asm.2; replace h_wf_asm := h_wf_asm.2
    have := U16MSBGadget.Spec.gadget_spec
              (h_gadget_constraints := h_constraints.1)
              (h_gadget_wf_asm := h_wf_asm.1)
    clear *- this; assumption

end DivRemChip.Interpretations
