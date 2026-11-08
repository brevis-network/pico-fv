import PicoFV.RV64IM.Constraints.DivRemChip
import PicoFV.RV64IM.Spec.MulGadget
import PicoFV.RV64IM.Spec.AddGadget
import PicoFV.RV64IM.Spec.IsZeroWordGadget
import PicoFV.RV64IM.Spec.IsEqualWordGadget
import PicoFV.RV64IM.Spec.LtWordU16Gadget
import PicoFV.RV64IM.Spec.U16MSBGadget
import PicoFV.RV64IM.RVSail.Execution
import PicoFV.RV64IM.RVSail.Buses

open Plonky3
open RV64IM

set_option maxHeartbeats 1_000_000_000
set_option linter.constructorNameAsVariable false

attribute [-simp]
  Int.tmod_eq_emod
  Int.natCast_tdiv_eq_ediv
  not_and
  Fin.val_pos_iff
  Fin.val_eq_zero_iff

/-!
# DivRemChip — semantic specification (RV64)

Eight per-opcode specs deriving `ALUBus.Spec OPCODE a b c` from the
chip's `AbsConstraints` + bus hypotheses + the active-selector
witness:

| Selector active | Opcode | Result                                                |
|-----------------|--------|-------------------------------------------------------|
| `is_div  = 1`   | 34     | signed   64-bit quotient  `b /ₛ c`                    |
| `is_divu = 1`   | 35     | unsigned 64-bit quotient  `b /ᵤ c`                    |
| `is_rem  = 1`   | 36     | signed   64-bit remainder `b %ₛ c`                    |
| `is_remu = 1`   | 37     | unsigned 64-bit remainder `b %ᵤ c`                    |
| `is_divw = 1`   | 49     | signed   32-bit quotient,  sign-extended to 64        |
| `is_divuw = 1`  | 50     | unsigned 32-bit quotient,  sign-extended to 64        |
| `is_remw = 1`   | 51     | signed   32-bit remainder, sign-extended to 64        |
| `is_remuw = 1`  | 52     | unsigned 32-bit remainder, sign-extended to 64        |

All W-form variants sign-extend their 32-bit result to 64 bits
(RV64 ISA convention), even for the unsigned `DIVUW`/`REMUW`
selectors. The chip encodes this via the `U16MSBGadget` on
`quotient_1` / `remainder_1` (gated by `is_word_operation`,
added in PR #101 commit `ddd0d96`): `quotient_2 = quotient_3 =
quot_msb · 0xFFFF` (resp. `remainder_*`).

## Proof approach (signed grouped `spec_DIV_REM` — proved)

The grouped proof has six phases:

1. **Selector cleanup** — `selector_breakdown` + `is_div + is_rem = 1`
   forces the other six selectors to 0 (six `clear *- … ; grind` calls).
2. **`gadget_specs_pack`** (in `Constraints/DivRemChip.lean`,
   `Interpretations` namespace) packages bus splitting + all 11
   sub-gadget `Spec.gadget_spec` invocations into one preprocessing
   call. Caller does
   `have := gadget_specs_pack air row; simp [*] at this; obtain
   ⟨h_ext, h_wf, h_constraints, gadget_specs⟩ := this`. After
   propagating `h_is_real = 1` and the zeroed selectors, the
   conditional thunks collapse to direct gadget conclusions.
3. **Range extraction**: unfold `ChipExtraBuses` on `h_ext` (ALU
   externals + `ALUBus.operandRange` at opcode 34/36) to get
   `b_*, c_* < 65536`; on `h_wf` (`ByteBus.Spec` opcode 8 = `U16Range`)
   to get `q_*, r_*, abs_c_*, abs_remainder_* < 65536`.
4. **Constraint specialisation**: `simp [AbsConstraints_NoGadgets, *]
   at h_constraints` extracts `is_real_not_word = 1` and the
   `*_comp = *` "not-word" identities.
5. **Mul gadget combination**: destructure `h_mul_lo`, `h_mul_hi`
   (each an `ALUBus.Spec`) and `RV64IM.combine_MUL_MULH` them into a
   128-bit product equation.
6. **Three-way case split** (on `IsZeroWordGadget` result for `c = 0`,
   then on `IsEqualWordGadget` results for `(b, c) = (INT_MIN, -1)`):
   * **c = 0**: AbsConstraints' DBZ clamps + `execute_DIV_REM_pure_int`
     close.
   * **overflow**: AbsConstraints' overflow clamps + executor's overflow
     branch close.
   * **normal case**: apply `Int.tdiv_tmod_unique_full` after `if_neg`
     on both special cases. Three conditions:
     a. **`b = q · c + r`** (over Int) — via `FKB_add_128` on the
        8 carry-chain equations + `combine_MUL_MULH` lifted through
        `BitVec.toInt_inj`.
     b. **`|r| < |c|`** — uses `LtWordU16Gadget` spec; depends on
        `remainder_lt_gadget.bit = 1`, pinned by PR #101 commit
        `0786b8b` (`builder.when(rem_check_mult).assert_one(bit)` in
        Pico Rust). The bridge between `ar.toNat`/`ac.toNat` and
        `|r|.natAbs` / `|c|.natAbs` goes through `U64w.msb_3_negative`
        + constraint-13 abs-value identities.
     c. **`sign(r) = sign(b) ∨ r = 0`** — by-cases on `r = 0`; else
        `Int.split_nzp` (3-way `< 0 / = 0 / > 0`) + sign-consistency
        constraints + the algebraic equation to rule out `b = 0`
        when `r ≠ 0`.

Each individual `spec_*` is a one-line projection from its
corresponding paired lemma: `spec_DIV` / `spec_REM` ← `spec_DIV_REM`,
`spec_DIVU` / `spec_REMU` ← `spec_DIVU_REMU`, `spec_DIVW` /
`spec_REMW` ← `spec_DIVW_REMW`, `spec_DIVUW` / `spec_REMUW` ←
`spec_DIVUW_REMUW`. The projection extracts `a = quotient`
(`div_active = 1` branch) or `a = remainder` (`rem_active = 1`
branch) from `AbsConstraints`, derives the u16 range on `q` / `r`
from the byte-bus, and closes `ALUBus.Spec OPCODE` by `grind`.

**Status:**
  * `spec_DIV_REM` — proven (the `bit = 1` Pico-soundness sorry
    was closed by PR #101 commit `0786b8b`).
  * `spec_DIVU_REMU` — proven.
  * `spec_DIVUW_REMUW` — proven.
  * `spec_DIVW_REMW` — proven.
  * All eight individual `spec_*` projections (`spec_DIV`, `spec_REM`,
    `spec_DIVU`, `spec_REMU`, `spec_DIVW`, `spec_REMW`, `spec_DIVUW`,
    `spec_REMUW`) — proven.
  * `ext_asrt` — proven.
  * `wf_asrt` — proven.
-/

namespace U32w

  @[simp]
  lemma ofNat_toNat {w : U32w} :
    BitVec.ofNat 32 w.toNat = w.toBV
  := by
    simp [← BitVec.toNat_inj]
    rw [← U32w.toBV_toNat]
    omega

  @[simp]
  lemma ofInt_toInt {w : U32w} :
    BitVec.ofInt 32 w.toInt = w.toBV
  := by
    simp [← BitVec.toInt_inj]
    have h_range := U32w.toInt_range w
    rw [Int.bmod_eq_of_le] <;> omega

end U32w

namespace DivRemChip.Spec

  open RV64IM_Interactions
  open DivRemChip.ConstraintsAndBuses
  open DivRemChip.Interactions
  open DivRemChip.Interpretations

  --
  -- Auxiliaries
  --

  -- =======================================================================
  -- Converts a field subtraction b - c * 65536 = a into Nat
  -- division/modulus: a = b % 65536 and c = b / 65536, given u16-range
  -- bounds. Used by `FKB_add_128` to peel each u16-limb carry equation
  -- down to a `%` / `/` pair on field naturals.
  -- =======================================================================

  lemma div_mod_decomposition {a b c : FKB} :
    a.val < 65536 → c.val < KB_prime / 65536 →
    (b - c * 65536 = a ↔ a = b % 65536 ∧ c = b / 65536) := by
    intro ub_a ub_c
    constructor
    . intro eq_a
      simp [Fin.ext_iff] at *
      have lb_b : c * 65536 ≤ b := by
        by_contra lb_b
        simp [Fin.lt_def, Fin.sub_def, Fin.mul_def] at *
        rw [Nat.mod_eq_of_lt (a := (c : ℕ) * 65536) (by omega)] at eq_a lb_b
        omega
      rw [Fin.sub_val_of_le lb_b] at eq_a
      simp [Fin.mul_def] at eq_a
      rw [Nat.mod_eq_of_lt (by omega)] at eq_a
      omega
    . intro ⟨ eq_a, eq_c ⟩
      simp_all
      rw [sub_eq_iff_eq_add]; symm
      rw [mul_comm, add_comm]
      simp [Fin.ext_iff, Fin.mul_def, Fin.add_def, Fin.mod_def]
      omega

  -- =========================================================================
  -- Given an 8-u16-limb carry chain in FKB (the field), proves that the
  -- corresponding U128w values satisfy a_128 = b_128 + c_128.
  -- Used to lift the per-limb constraint chain into a single 128-bit
  -- equation `b = c · quotient + remainder` (mod 2^128).
  -- =========================================================================

  lemma FKB_add_128
    {a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 : FKB}
    (ub_a0 : a0 < 65536) (ub_a1 : a1 < 65536)
    (ub_a2 : a2 < 65536) (ub_a3 : a3 < 65536)
    (ub_a4 : a4 < 65536) (ub_a5 : a5 < 65536)
    (ub_a6 : a6 < 65536) (ub_a7 : a7 < 65536)
    (ub_b0 : b0 < 65536) (ub_b1 : b1 < 65536)
    (ub_b2 : b2 < 65536) (ub_b3 : b3 < 65536)
    (ub_b4 : b4 < 65536) (ub_b5 : b5 < 65536)
    (ub_b6 : b6 < 65536) (ub_b7 : b7 < 65536)
    (ub_c0 : c0 < 65536) (ub_c1 : c1 < 65536)
    (ub_c2 : c2 < 65536) (ub_c3 : c3 < 65536)
    (ub_c4 : c4 < 65536) (ub_c5 : c5 < 65536)
    (ub_c6 : c6 < 65536) (ub_c7 : c7 < 65536)
    (eq_p0 : b0 + c0 - cry0 * 65536 = a0)
    (eq_p1 : b1 + c1 - cry1 * 65536 + cry0 = a1)
    (eq_p2 : b2 + c2 - cry2 * 65536 + cry1 = a2)
    (eq_p3 : b3 + c3 - cry3 * 65536 + cry2 = a3)
    (eq_p4 : b4 + c4 - cry4 * 65536 + cry3 = a4)
    (eq_p5 : b5 + c5 - cry5 * 65536 + cry4 = a5)
    (eq_p6 : b6 + c6 - cry6 * 65536 + cry5 = a6)
    (eq_p7 : b7 + c7 - cry7 * 65536 + cry6 = a7)
    (b_cr0 : cry0 = 0 ∨ cry0 = 1)
    (b_cr1 : cry1 = 0 ∨ cry1 = 1)
    (b_cr2 : cry2 = 0 ∨ cry2 = 1)
    (b_cr3 : cry3 = 0 ∨ cry3 = 1)
    (b_cr4 : cry4 = 0 ∨ cry4 = 1)
    (b_cr5 : cry5 = 0 ∨ cry5 = 1)
    (b_cr6 : cry6 = 0 ∨ cry6 = 1)
    (b_cr7 : cry7 = 0 ∨ cry7 = 1)
  :
    U128w.toBV #v[a0, a1, a2, a3, a4, a5, a6, a7] =
      U128w.toBV #v[b0, b1, b2, b3, b4, b5, b6, b7] +
      U128w.toBV #v[c0, c1, c2, c3, c4, c5, c6, c7]
  := by
    rw [add_comm_sub] at eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
    rw [← add_sub_assoc] at eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
    rw [div_mod_decomposition (by assumption)
          (by clear *- b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7; omega)]
      at eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
    simp [← BitVec.toNat_inj, U128w.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by assumption)]
    have joins : forall (i : Fin 8) (a b : ℕ),
      a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) =
      (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
    have divs : forall (i : Fin 8) (a b : ℕ),
      (a + b / (65536 ^ i.val)) / 65536 =
      (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
    have j1 := joins 1; have j2 := joins 2; have j3 := joins 3
    have j4 := joins 4; have j5 := joins 5; have j6 := joins 6
    have j7 := joins 7
    have d1 := divs 1; have d2 := divs 2; have d3 := divs 3
    have d4 := divs 4; have d5 := divs 5; have d6 := divs 6
    have d7 := divs 7
    simp at j1 j2 j3 j4 j5 j6 j7 d1 d2 d3 d4 d5 d6 d7
    clear joins divs
    simp_all [Fin.val_add]
    repeat rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)]
    rw [j1, d1, j2, d2, j3, d3, j4, d4, j5, d5, j6, d6, j7]
    ring_nf

  lemma FKB_add_64
    {a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 cry0 cry1 cry2 cry3 : FKB}
    (ub_a0 : a0 < 65536) (ub_a1 : a1 < 65536)
    (ub_a2 : a2 < 65536) (ub_a3 : a3 < 65536)
    (ub_b0 : b0 < 65536) (ub_b1 : b1 < 65536)
    (ub_b2 : b2 < 65536) (ub_b3 : b3 < 65536)
    (ub_c0 : c0 < 65536) (ub_c1 : c1 < 65536)
    (ub_c2 : c2 < 65536) (ub_c3 : c3 < 65536)
    (eq_p0 : b0 + c0 - cry0 * 65536 = a0)
    (eq_p1 : b1 + c1 - cry1 * 65536 + cry0 = a1)
    (eq_p2 : b2 + c2 - cry2 * 65536 + cry1 = a2)
    (eq_p3 : b3 + c3 - cry3 * 65536 + cry2 = a3)
    (b_cr0 : cry0 = 0 ∨ cry0 = 1)
    (b_cr1 : cry1 = 0 ∨ cry1 = 1)
    (b_cr2 : cry2 = 0 ∨ cry2 = 1)
    (b_cr3 : cry3 = 0 ∨ cry3 = 1)
  :
    U64w.toBV #v[a0, a1, a2, a3] =
      U64w.toBV #v[b0, b1, b2, b3] + U64w.toBV #v[c0, c1, c2, c3]
  := by
    rw [add_comm_sub] at eq_p1 eq_p2 eq_p3
    rw [← add_sub_assoc] at eq_p1 eq_p2 eq_p3
    rw [div_mod_decomposition (by assumption)
          (by clear *- b_cr0 b_cr1 b_cr2 b_cr3; omega)]
      at eq_p0 eq_p1 eq_p2 eq_p3
    simp [← BitVec.toNat_inj, U64w.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by assumption)]
    have joins : forall (i : Fin 4) (a b : ℕ),
      a % (65536 ^ i.val) + (b + a / (65536 ^ i.val)) % 65536 * (65536 ^ i.val) =
      (a + b * (65536 ^ i.val)) % (65536 ^ (i.val + 1)) := by
      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
    have divs : forall (i : Fin 4) (a b : ℕ),
      (a + b / (65536 ^ i.val)) / 65536 =
      (b + a * (65536 ^ i.val)) / (65536 ^ (i.val + 1)) := by
      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
    have j1 := joins 1; have j2 := joins 2; have j3 := joins 3;
    have d1 := divs 1; have d2 := divs 2;
    simp at j1 j2 j3 d1 d2
    clear joins divs
    simp_all [Fin.val_add]
    repeat rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)]
    rw [j1, d1, j2, d2, j3]
    ring_nf

  -- ========================================================================
  -- spec_DIV_REM  (paired): both signed 64-bit DIV/REM selectors at once.
  -- Result: the chip's `(quotient, remainder)` columns are the pair
  -- `RV64IM.execute_DIV_REM_pure b c .DRS` (RV64 signed semantics, with
  -- the divide-by-zero and overflow special cases handled by Pico's
  -- `execute_DIV_REM_pure_int .DRS`).
  --
  -- Proof structure (six phases):
  --   1. **Selector cleanup** — `selector_breakdown` + `is_div + is_rem
  --      = 1` forces the other six selectors to 0 (six grind calls).
  --   2. **`gadget_specs_pack`** packages bus splitting + all 11
  --      sub-gadget `Spec.gadget_spec` invocations into one
  --      preprocessing call. After `simp [*]` propagates `h_is_real
  --      = 1` and the zeroed selectors, the conditional thunks
  --      collapse to direct gadget conclusions.
  --   3. **Range extraction**: unfold `ChipExtraBuses` on `h_ext`
  --      (ALU externals + `ALUBus.operandRange` at opcode 34/36) to
  --      get `b_*, c_* < 65536`; on `h_wf` (`ByteBus.Spec` opcode
  --      8 = `U16Range`) to get `q_*, r_*, abs_c_*, abs_remainder_*
  --      < 65536`.
  --   4. **Constraint specialisation** from `AbsConstraints_NoGadgets`:
  --      `is_real_not_word = 1`, `quotient_comp_i = quotient_i`,
  --      `remainder_comp_i = remainder_i` (the not-word branch of the
  --      `*_comp` setup).
  --   5. **Mul gadget combination**: destructure `h_mul_lo`, `h_mul_hi`
  --      (each an `ALUBus.Spec`) and `RV64IM.combine_MUL_MULH` them
  --      into a 128-bit product equation `b = c · quotient` over `U128w`.
  --   6. **Three-way case split** on `IsZeroWordGadget` result for
  --      `c = 0`, then on the `IsEqualWordGadget` results for
  --      `(b, c) = (INT_MIN_64, -1)`:
  --      * **c = 0**: AbsConstraints' DBZ clamps + `execute_DIV_REM_pure_int`
  --        close the goal directly.
  --      * **overflow**: AbsConstraints' overflow clamps + executor's
  --        overflow branch close.
  --      * **normal case**: apply `Int.tdiv_tmod_unique_full` after
  --        `if_neg` on both special cases. Three conditions:
  --        a. **`b = q · c + r`** (over Int) — via `FKB_add_128` on
  --           the 8 carry-chain equations + `combine_MUL_MULH` lifted
  --           through `BitVec.toInt_inj`.
  --        b. **`|r| < |c|`** — uses `LtWordU16Gadget` spec; depends
  --           on `remainder_lt_gadget.bit = 1` (post-PR #101 fix to
  --           Pico).
  --        c. **`sign(r) = sign(b) ∨ r = 0`** — by-cases on `r = 0`;
  --           else `Int.split_nzp` + sign-consistency constraints +
  --           the algebraic equation to rule out `b = 0` when `r ≠ 0`.
  -- ========================================================================

  lemma spec_DIV_REM
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_div_rem :
      air.cols.values.is_div row 0 + air.cols.values.is_rem row 0 = 1)
  :
    ⟨ U64w.toBV #v[air.cols.values.quotient_0  row 0,
                   air.cols.values.quotient_1  row 0,
                   air.cols.values.quotient_2  row 0,
                   air.cols.values.quotient_3  row 0],
      U64w.toBV #v[air.cols.values.remainder_0 row 0,
                   air.cols.values.remainder_1 row 0,
                   air.cols.values.remainder_2 row 0,
                   air.cols.values.remainder_3 row 0] ⟩ =
    RV64IM.execute_DIV_REM_pure
      (U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                    air.cols.values.b_2 row 0, air.cols.values.b_3 row 0])
      (U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                    air.cols.values.c_2 row 0, air.cols.values.c_3 row 0])
      .DRS
  := by
    -- Step 1: Selector exclusivity. The chip's at-most-one constraint
    -- plus `is_div + is_rem = 1` forces the other six selectors to 0.
    obtain ⟨b_div, b_divu, b_rem, b_remu, b_divw, b_remw, b_divuw, b_remuw, h_sum⟩
      := selector_breakdown air row h_constraints
    have eq_divu  : air.cols.values.is_divu  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_div_rem; grind
    have eq_remu  : air.cols.values.is_remu  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_div_rem; grind
    have eq_divw  : air.cols.values.is_divw  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_div_rem; grind
    have eq_remw  : air.cols.values.is_remw  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_div_rem; grind
    have eq_divuw : air.cols.values.is_divuw row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_div_rem; grind
    have eq_remuw : air.cols.values.is_remuw row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_div_rem; grind
    clear b_divu b_remu b_divw b_remw b_divuw b_remuw h_sum
    -- Move to gadget specs
    have := gadget_specs_pack air row
    simp only [h_ext, h_wf, h_constraints, h_is_real] at this
    simp [*] at this; clear h_ext h_wf h_constraints
    obtain ⟨ h_ext, h_wf, h_constraints, gadget_specs ⟩ := this
    -- Stabilise h_ext
    obtain ⟨ ub_b_0, ub_b_1, ub_b_2, ub_b_3, ub_c_0, ub_c_1, ub_c_2, ub_c_3 ⟩ :
      (air.cols.values.b_0 row 0).val < 65536 ∧ (air.cols.values.b_1 row 0).val < 65536 ∧ (air.cols.values.b_2 row 0).val < 65536 ∧ (air.cols.values.b_3 row 0).val < 65536 ∧
      (air.cols.values.c_0 row 0).val < 65536 ∧ (air.cols.values.c_1 row 0).val < 65536 ∧ (air.cols.values.c_2 row 0).val < 65536 ∧ (air.cols.values.c_3 row 0).val < 65536
    := by
      clear h_wf h_constraints gadget_specs
      simp [bus_row_ext_asm, ChipExtraBuses] at h_ext; replace h_ext := h_ext.2.2
      simp [ALUBus.externals, ALUBus.validOpcode, ALUBus.operandsInternal, ALUBus.operandRange, *] at h_ext
      apply h_ext.2 <;> clear h_ext <;> grind
    clear h_ext
    -- Get various upper bounds and equalities
    obtain ⟨ ub_q_0, ub_q_1, ub_q_2, ub_q_3, ub_r_0, ub_r_1, ub_r_2, ub_r_3,
             ub_ac_0, ub_ac_1, ub_ac_2, ub_ac_3, ub_ar_0, ub_ar_1, ub_ar_2, ub_ar_3 ⟩ :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧ (air.cols.values.quotient_1 row 0).val < 65536 ∧ (air.cols.values.quotient_2 row 0).val < 65536 ∧ (air.cols.values.quotient_3 row 0).val < 65536 ∧
      (air.cols.values.remainder_0 row 0).val < 65536 ∧ (air.cols.values.remainder_1 row 0).val < 65536 ∧ (air.cols.values.remainder_2 row 0).val < 65536 ∧ (air.cols.values.remainder_3 row 0).val < 65536 ∧
      (air.cols.values.abs_c_0 row 0).val < 65536 ∧ (air.cols.values.abs_c_1 row 0).val < 65536 ∧ (air.cols.values.abs_c_2 row 0).val < 65536 ∧ (air.cols.values.abs_c_3 row 0).val < 65536 ∧
      (air.cols.values.abs_remainder_0 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_1 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_2 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_3 row 0).val < 65536
    := by
      clear gadget_specs
      simp [bus_row_wf_asm, ChipExtraBuses, ByteBus.Spec, *] at h_wf
      simp [h_wf]
    obtain ⟨ eq_rnw, eq_qc_0, eq_qc_1, eq_qc_2, eq_qc_3, eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3 ⟩ :
      air.cols.values.is_real_not_word row 0 = 1 ∧
      air.cols.values.quotient_comp_0 row 0 = air.cols.values.quotient_0 row 0 ∧ air.cols.values.quotient_comp_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.quotient_comp_2 row 0 = air.cols.values.quotient_2 row 0 ∧ air.cols.values.quotient_comp_3 row 0 = air.cols.values.quotient_3 row 0 ∧
      air.cols.values.remainder_comp_0 row 0 = air.cols.values.remainder_0 row 0 ∧ air.cols.values.remainder_comp_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.remainder_comp_2 row 0 = air.cols.values.remainder_2 row 0 ∧ air.cols.values.remainder_comp_3 row 0 = air.cols.values.remainder_3 row 0
    := by
      clear gadget_specs
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      simp [h_constraints]
    -- Stabilise gadget specifications
    simp [*] at gadget_specs
    obtain ⟨ h_mul_lo, h_mul_hi,
             ⟨ b_b_overflow, h_b_overflow ⟩, ⟨ b_c_overflow, h_c_overflow ⟩, ⟨ b_c_zero, h_c_zero ⟩,
             h_abs_c, h_abs_rem, h_rem_check, h_b_msb, h_c_msb, h_rem_msb ⟩ := gadget_specs
    simp [ALUBus.Spec] at h_mul_lo h_mul_hi
    obtain ⟨ ⟨ ub_cq_0, ub_cq_1, ub_cq_2, ub_cq_3 ⟩, h_op_range, h_mul_lo ⟩ := h_mul_lo; clear h_op_range
    obtain ⟨ ⟨ ub_cq_4, ub_cq_5, ub_cq_6, ub_cq_7 ⟩, h_op_range, h_mul_hi ⟩ := h_mul_hi; clear h_op_range
    have mul_spec := RV64IM.combine_MUL_MULH h_mul_lo h_mul_hi; simp at mul_spec; clear h_mul_lo h_mul_hi
    -- Case : c = 0
    obtain eq_cz | eq_cz := b_c_zero <;> simp [eq_cz] at h_c_zero; rotate_left
    . have h_eqz : U64w.toInt #v[0#16, 0#16, 0#16, 0#16] = 0 := by clear *-; decide
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, *]
      split_ands <;> clear *- <;> [ skip; simp [← BitVec.toInt_inj] ]
      . unfold U64w.toBV; simp [-BitVec.reduceAppend]; rfl
      . rw [Int.bmod_eq_of_le] <;> grind [U64w.toInt_range]
    -- Case: ¬ (c == 0)
    . set c_BV : U64w := #v[
        BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_2 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_3 row 0)] with eq_c_BV
      have h_c_neq_0_bv : ¬ (c_BV.toBV = 0)
      := by
        -- Commented proof
        clear *- h_c_zero ub_c_0 ub_c_1 ub_c_2 ub_c_3
        subst c_BV; intro h_c_bv_zero; apply h_c_zero; clear h_c_zero
        simp [← BitVec.toNat_inj, U64w.toNat] at h_c_bv_zero
        grind
      clear h_c_zero
      have b_overflow : air.cols.values.is_overflow row 0 = 0 ∨ air.cols.values.is_overflow row 0 = 1
      := by
        simp [AbsConstraints_NoGadgets, sub_eq_zero, *] at h_constraints
        clear *- h_constraints; grind
      have h_overflow := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      obtain eq_overflow | eq_overflow := b_overflow <;> simp [*] at h_overflow; rotate_left
      -- Case : overflow
      . have h_eq : air.cols.values.is_overflow_b.is_diff_zero.result row 0 = 1 ∧ air.cols.values.is_overflow_c.is_diff_zero.result row 0 = 1
          := by clear *- b_b_overflow b_c_overflow h_overflow; grind
        clear h_overflow; simp [h_eq] at h_b_overflow h_c_overflow
        simp [AbsConstraints_NoGadgets, sub_eq_zero, *] at h_constraints
        replace h_constraints := h_constraints.2.2.2.2.2.1
        simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, eq_c_BV]
        unfold U64w.toBV U64w.toInt U64w.negative U64w.toNat
        simp [h_constraints, h_b_overflow, h_c_overflow]
      -- Case : No overflow
      . set b_BV : U64w := #v[
          BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.b_2 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.b_3 row 0)] with eq_b_BV
        have h_no_overflow_bv : ¬ (b_BV.toBV = 9223372036854775808#64 ∧ c_BV.toBV = 18446744073709551615#64)
        := by
          clear *- h_b_overflow h_c_overflow h_overflow
                   ub_b_0 ub_b_1 ub_b_2 ub_b_3 ub_c_0 ub_c_1 ub_c_2 ub_c_3
          subst b_BV c_BV; simp [← BitVec.toNat_inj, U64w.toNat]
          grind
        clear b_b_overflow h_b_overflow b_c_overflow h_c_overflow h_overflow
        simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
        set q_BV : U64w := #v[
          BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.quotient_2 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.quotient_3 row 0)] with eq_q_BV
        set r_BV : U64w := #v[
          BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.remainder_2 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.remainder_3 row 0)] with eq_r_BV
        rw [if_neg (by simp [← BitVec.toInt_inj] at h_c_neq_0_bv; exact h_c_neq_0_bv)]
        rw [if_neg (by simp [← BitVec.toInt_inj] at h_no_overflow_bv; exact h_no_overflow_bv)]
        simp [← BitVec.toInt_inj]
        have b_range := U64w.toInt_range b_BV; have c_range := U64w.toInt_range c_BV
        have range_tmod := Int.tmod_range_64 b_range c_range
        have range_tdiv := Int.tdiv_range_64
               (by simp [← BitVec.toInt_inj] at h_c_neq_0_bv; exact h_c_neq_0_bv)
               (by simp [← BitVec.toInt_inj] at h_no_overflow_bv; exact h_no_overflow_bv)
               b_range
        rw [Int.bmod_eq_of_le (by clear *- range_tdiv; tauto) (by clear *- range_tdiv; tauto)]
        rw [Int.bmod_eq_of_le (by clear *- range_tmod; tauto) (by clear *- range_tmod; tauto)]
        rw [Int.tdiv_tmod_unique_full (by simp [← BitVec.toInt_inj] at h_c_neq_0_bv; exact h_c_neq_0_bv)]
        have h_is_msb_b : air.cols.values.b_msb.msb row 0 = air.cols.values.b_neg row 0
          := by have := h_constraints.2.1; simp [*] at this; clear *- this; omega
        have h_is_msb_r : air.cols.values.rem_msb.msb row 0 = air.cols.values.rem_neg row 0
          := by have := h_constraints.2.2.1; simp [*] at this; clear *- this; omega
        have h_is_msb_c : air.cols.values.c_msb.msb row 0 = air.cols.values.c_neg row 0
          := by have := h_constraints.2.2.2.1; simp [*] at this; clear *- this; omega
        simp [h_is_msb_b, h_is_msb_r, h_is_msb_c] at h_b_msb h_rem_msb h_c_msb
        have cond_b_eq_qc_plus_r : b_BV.toInt = q_BV.toInt * c_BV.toInt + r_BV.toInt
        := by
          have cond_bv :
            U128w.toBV
              #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                 air.cols.values.b_2 row 0, air.cols.values.b_3 row 0,
                 (air.cols.values.b_neg row 0 * 65535 : FKB),
                 (air.cols.values.b_neg row 0 * 65535 : FKB),
                 (air.cols.values.b_neg row 0 * 65535 : FKB),
                 (air.cols.values.b_neg row 0 * 65535 : FKB)] =
            U128w.toBV
                #v[air.cols.values.c_times_quotient_0 row 0,
                   air.cols.values.c_times_quotient_1 row 0,
                   air.cols.values.c_times_quotient_2 row 0,
                   air.cols.values.c_times_quotient_3 row 0,
                   air.cols.values.c_times_quotient_4 row 0,
                   air.cols.values.c_times_quotient_5 row 0,
                   air.cols.values.c_times_quotient_6 row 0,
                   air.cols.values.c_times_quotient_7 row 0] +
              U128w.toBV
                #v[air.cols.values.remainder_0 row 0, air.cols.values.remainder_1 row 0,
                   air.cols.values.remainder_2 row 0, air.cols.values.remainder_3 row 0,
                   (air.cols.values.rem_neg row 0 * 65535 : FKB),
                   (air.cols.values.rem_neg row 0 * 65535 : FKB),
                   (air.cols.values.rem_neg row 0 * 65535 : FKB),
                   (air.cols.values.rem_neg row 0 * 65535 : FKB)]
          := by
            replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            have carries := h_constraints.1
            simp [eq_overflow, eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3] at carries
            obtain ⟨ eq_cry_0, eq_cry_1, eq_cry_2, eq_cry_3, eq_cry_4, eq_cry_5, eq_cry_6, eq_cry_7 ⟩ := carries
            have ub_sign_ext_b : (air.cols.values.b_neg row 0 * 65535).val < 65536
              := by clear *- h_b_msb; grind
            have ub_rem_ext_b : (air.cols.values.rem_neg row 0 * 65535).val < 65536
              := by clear *- h_rem_msb; grind
            replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            obtain ⟨ b_cry_0, b_cry_1, b_cry_2, b_cry_3, b_cry_4, b_cry_5, b_cry_6, b_cry_7, rest ⟩ := h_constraints; clear rest
            simp [sub_eq_zero] at b_cry_0 b_cry_1 b_cry_2 b_cry_3 b_cry_4 b_cry_5 b_cry_6 b_cry_7
            exact
              FKB_add_128
                ub_b_0 ub_b_1 ub_b_2 ub_b_3 ub_sign_ext_b ub_sign_ext_b ub_sign_ext_b ub_sign_ext_b
                ub_cq_0 ub_cq_1 ub_cq_2 ub_cq_3 ub_cq_4 ub_cq_5 ub_cq_6 ub_cq_7
                ub_r_0 ub_r_1 ub_r_2 ub_r_3 ub_rem_ext_b ub_rem_ext_b ub_rem_ext_b ub_rem_ext_b
                eq_cry_0 eq_cry_1 eq_cry_2 eq_cry_3 eq_cry_4 eq_cry_5 eq_cry_6 eq_cry_7
                b_cry_0 b_cry_1 b_cry_2 b_cry_3 b_cry_4 b_cry_5 b_cry_6 b_cry_7
          have h_b_ext :
            (#v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                air.cols.values.b_2 row 0, air.cols.values.b_3 row 0,
                (air.cols.values.b_neg row 0 * 65535 : FKB),
                (air.cols.values.b_neg row 0 * 65535 : FKB),
                (air.cols.values.b_neg row 0 * 65535 : FKB),
                (air.cols.values.b_neg row 0 * 65535 : FKB)] : U128w) = b_BV.extend true
          := by
            clear *- h_b_msb ub_b_3
            subst b_BV; simp [U64w.extend, -Vector.mk_eq]; congr
            simp [U64w.ext, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
            grind
          have h_r_ext :
            (#v[air.cols.values.remainder_0 row 0, air.cols.values.remainder_1 row 0,
                air.cols.values.remainder_2 row 0, air.cols.values.remainder_3 row 0,
                (air.cols.values.rem_neg row 0 * 65535 : FKB),
                (air.cols.values.rem_neg row 0 * 65535 : FKB),
                (air.cols.values.rem_neg row 0 * 65535 : FKB),
                (air.cols.values.rem_neg row 0 * 65535 : FKB)] : U128w) = r_BV.extend true
          := by
            clear *- h_rem_msb ub_r_3
            subst r_BV; simp [U64w.extend, -Vector.mk_eq]; congr
            simp [U64w.ext, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
            grind
          rw [h_b_ext, mul_spec, h_r_ext] at cond_bv; clear h_b_ext h_r_ext mul_spec
          simp [← BitVec.toInt_inj] at cond_bv; rw [cond_bv]
          have q_range := U64w.toInt_range q_BV; have r_range := U64w.toInt_range r_BV
          clear *- b_range c_range q_range r_range
          rw [Int.bmod_eq_of_le (by simp; nlinarith) (by simp; nlinarith)]
        refine ⟨by exact cond_b_eq_qc_plus_r, ?_⟩
        have cond_abs : |r_BV.toInt| < |c_BV.toInt|
        := by
          set ac_BV : U64w := #v[
            BitVec.ofNat 16 ↑(air.cols.values.abs_c_0 row 0),
            BitVec.ofNat 16 ↑(air.cols.values.abs_c_1 row 0),
            BitVec.ofNat 16 ↑(air.cols.values.abs_c_2 row 0),
            BitVec.ofNat 16 ↑(air.cols.values.abs_c_3 row 0)] with eq_ac_BV
          set ar_BV : U64w := #v[
            BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_0 row 0),
            BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_1 row 0),
            BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_2 row 0),
            BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_3 row 0)] with eq_ar_BV
          have relevant_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          simp [*, sub_eq_zero] at relevant_constraints
          obtain ⟨ h_eq_negs, h_rem_z, h_c_neg_abs, h_rem_neg_abs,
                   h_eq_max_0, h_eq_max_1, h_eq_max_2, h_eq_max_3, h_eq_rem_check,
                   h_abs_c_alu, h_abs_rem_alu, h_c_neg_gadget, h_rem_neg_gadget, h_is_lt, rest ⟩ := relevant_constraints; clear rest
          rw [h_abs_c_alu] at h_abs_c h_c_neg_gadget; rw [h_abs_rem_alu] at h_abs_rem h_rem_neg_gadget
          simp [*] at h_rem_check
          suffices h_natAbs : r_BV.toInt.natAbs < c_BV.toInt.natAbs
          . clear *- h_natAbs; (iterate 2 rw [Int.abs_eq_natAbs]); omega
          . have eq_ar : ar_BV.toNat = r_BV.toInt.natAbs
            := by
              clear *- ub_r_0 ub_r_1 ub_r_2 ub_r_3
                       h_rem_msb h_abs_rem h_rem_neg_abs h_rem_neg_gadget
              obtain ⟨ h_rem_zero, h_pos ⟩ | ⟨ h_rem_one, h_neg ⟩ := h_rem_msb
              . clear h_abs_rem h_rem_neg_gadget
                simp [h_rem_zero] at h_rem_neg_abs; subst ar_BV; simp [h_rem_neg_abs]
                subst r_BV; simp [U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
                rw [if_neg (by omega), sub_zero, Int.natAbs_natCast]
              . clear h_rem_neg_abs
                simp [h_rem_one] at h_abs_rem h_rem_neg_gadget
                simp [h_rem_neg_gadget, ← BitVec.toNat_inj] at h_abs_rem
                have ar_range : ar_BV.toNat < 18446744073709551616 := by clear *-; subst ar_BV; simp [U64w.toNat]; omega
                have r_range : r_BV.toNat < 18446744073709551616 := by clear *-; subst r_BV; simp [U64w.toNat]; omega
                conv at h_abs_rem => lhs; simp [U64w.toNat]
                by_cases h_r_zero : r_BV.toBV = 0
                . have h_eq_abs_rem : ar_BV.toNat = 0 := by simp [← BitVec.toNat_inj] at h_r_zero; omega
                  rw [← U64w.toBV_toInt, h_r_zero, h_eq_abs_rem]; rfl
                . have h_eq_abs_c : ar_BV.toNat = 18446744073709551616 - r_BV.toNat
                  := by
                    clear *- h_r_zero h_abs_rem ar_range r_range
                    simp [← BitVec.toNat_inj] at h_r_zero
                    omega
                  simp [h_eq_abs_c, U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
                  rw [if_pos (by subst r_BV; simp; omega)]
                  obtain ⟨ r, eq_r ⟩ : ∃ r, r = r_BV := by simp
                  rw [← eq_r] at r_range ⊢; clear *- r_range; omega
            have eq_ac : ac_BV.toNat = c_BV.toInt.natAbs
            := by
              clear *- ub_c_0 ub_c_1 ub_c_2 ub_c_3
                       h_c_neq_0_bv h_c_msb h_abs_c h_c_neg_abs h_c_neg_gadget
              obtain ⟨ h_c_zero, h_pos ⟩ | ⟨ h_c_one, h_neg ⟩ := h_c_msb
              . clear h_abs_c h_c_neg_gadget
                simp [h_c_zero] at h_c_neg_abs; subst ac_BV; simp [h_c_neg_abs]
                subst c_BV; simp [U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
                rw [if_neg (by omega), sub_zero, Int.natAbs_natCast]
              . clear h_c_neg_abs
                simp [h_c_one] at h_abs_c h_c_neg_gadget
                simp [h_c_neg_gadget, ← BitVec.toNat_inj] at h_abs_c
                have ac_range : ac_BV.toNat < 18446744073709551616 := by clear *-; subst ac_BV; simp [U64w.toNat]; omega
                have c_range : c_BV.toNat < 18446744073709551616 := by clear *-; subst c_BV; simp [U64w.toNat]; omega
                have h_eq_abs_c : ac_BV.toNat = 18446744073709551616 - c_BV.toNat
                := by
                  clear *- h_c_neq_0_bv h_abs_c ac_range c_range
                  conv at h_abs_c => lhs; simp [U64w.toNat]
                  simp [← BitVec.toNat_inj] at h_c_neq_0_bv
                  omega
                simp [h_eq_abs_c, U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
                rw [if_pos (by subst c_BV; simp; omega)]
                obtain ⟨ c, eq_c ⟩ : ∃ c, c = c_BV := by simp
                rw [← eq_c] at c_range ⊢; clear *- c_range; omega
            clear *- h_rem_check eq_ar eq_ac; grind
        refine ⟨by exact cond_abs, ?_⟩
        have h_sign : r_BV.toInt = 0 ∨ r_BV.toInt.sign = b_BV.toInt.sign
        := by
          have q_range := U64w.toInt_range q_BV; have r_range := U64w.toInt_range r_BV
          have relevant_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          simp [*, sub_eq_zero] at relevant_constraints
          obtain ⟨ h_eq_negs, h_rem_z, rest ⟩ := relevant_constraints; clear rest
          clear *- ub_b_3 ub_r_0 ub_r_1 ub_r_2 ub_r_3
                   b_range c_range q_range r_range h_b_msb h_rem_msb
                   h_c_neq_0_bv h_no_overflow_bv cond_b_eq_qc_plus_r cond_abs h_eq_negs h_rem_z
          by_cases h_r_zero : r_BV.toBV = 0
          . left; rw [← U64w.toBV_toInt, h_r_zero]; rfl
          . have h_not_rz : ¬ (air.cols.values.remainder_0 row 0 + air.cols.values.remainder_1 row 0 + air.cols.values.remainder_2 row 0 + air.cols.values.remainder_3 row 0 = 0)
            := by
              clear *- h_r_zero ub_r_0 ub_r_1 ub_r_2 ub_r_3
              intro h_rem_z; apply h_r_zero; clear h_r_zero
              subst r_BV; simp [← BitVec.toNat_inj, U64w.toNat]
              omega
            simp [h_not_rz] at h_rem_z
            right; apply Int.split_nzp r_BV.toInt <;> intro h_r_sgn
            . suffices ub_b : b_BV.toInt < 0
              . simp [Int.sign_cases]; clear *- ub_b h_r_sgn; omega
              . have h_rem_neg : air.cols.values.rem_neg row 0 = 1
                := by
                  subst r_BV; clear *- ub_r_0 ub_r_1 ub_r_2 ub_r_3 h_rem_msb h_r_sgn
                  simp [U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide] at h_r_sgn
                  simp [U64w.toNat] at h_r_sgn
                  omega
                simp [h_rem_neg] at h_eq_negs
                simp [h_eq_negs] at h_b_msb
                clear *- ub_b_3 h_b_msb
                subst b_BV; simp [U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
                rw [if_pos (by omega)]
                simp [U64w.toNat]; omega
            . exfalso; clear *- h_r_zero h_r_sgn; apply h_r_zero
              simpa [← BitVec.toInt_inj]
            . suffices lb_b : 0 < b_BV.toInt
              . simp [Int.sign_cases]; clear *- lb_b h_r_sgn; omega
              . have h_rem_neg : air.cols.values.rem_neg row 0 = 0
                := by
                  subst r_BV; clear *- ub_r_0 ub_r_1 ub_r_2 ub_r_3 h_rem_msb h_r_sgn
                  simp [U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide] at h_r_sgn
                  simp [U64w.toNat] at h_r_sgn
                  omega
                simp [h_rem_neg] at h_rem_z
                simp [h_rem_z] at h_b_msb
                simp [U64w.toInt, ← U64w.msb_3_negative, BitVec.msb_eq_decide]
                rw [if_neg (by subst b_BV; simp; omega)]; simp
                suffices h_b_nz : ¬ (b_BV.toBV = 0)
                . clear *- h_b_nz; simp [← BitVec.toNat_inj] at h_b_nz; omega
                . intro h_b_z; simp [← BitVec.toInt_inj] at h_b_z h_c_neq_0_bv; rw [h_b_z] at cond_b_eq_qc_plus_r
                  clear *- cond_b_eq_qc_plus_r cond_abs h_c_neq_0_bv cond_abs h_r_sgn
                  replace cond_b_eq_qc_plus_r : r_BV.toInt = - (q_BV.toInt * c_BV.toInt) := by omega
                  simp [cond_b_eq_qc_plus_r] at cond_abs h_r_sgn
                  have h_q_neq_0 : ¬ q_BV.toInt = 0 := by grind
                  clear h_r_sgn cond_b_eq_qc_plus_r
                  obtain ⟨ q, c, eq_q, eq_c ⟩ : ∃ q c, q = q_BV.toInt ∧ c = c_BV.toInt := by simp
                  simp [← eq_q, ← eq_c] at cond_abs h_q_neq_0; clear *- cond_abs h_q_neq_0
                  have h_lt : ∀ {a b : ℤ}, 0 < b → a * b < b → a ≤ 0
                    := by clear *-; intro a b lb_b ub_prod; nlinarith
                  specialize @h_lt |q| |c| (by grind) cond_abs
                  grind
        exact h_sign

  -- ========================================================================
  -- spec_DIVU_REMU  (paired): both unsigned 64-bit DIV/REM selectors at
  -- once. Result: the chip's `(quotient, remainder)` columns equal
  -- `RV64IM.execute_DIV_REM_pure b c .DRU` (unsigned-64 semantics with
  -- the divide-by-zero special case `c = 0 → q = u64::MAX, r = b`).
  --
  -- Proof structure mirrors `spec_DIV_REM` but is materially simpler:
  --   * **No overflow case** — unsigned division can't overflow
  --     (the `INT_MIN / -1` corner case is signed-only), so the
  --     overflow `IsEqualWordGadget`s collapse to vacuous truth and
  --     the proof has just two branches: c = 0 vs c ≠ 0.
  --   * **No sign reasoning** — `is_signed_type = 0` forces
  --     `b_neg = c_neg = rem_neg = 0`, eliminating the
  --     sign-consistency case analysis entirely.
  --
  -- Phases:
  --   1. **Selector cleanup** (mirror of `spec_DIV_REM`).
  --   2. **`gadget_specs_pack`** + simp propagation.
  --   3. **Range extraction** (same ALU-externals + byte-bus pattern).
  --   4. **Constraint specialisation** from `AbsConstraints_NoGadgets`:
  --      same `is_real_not_word = 1` + `*_comp = *` identities.
  --   5. **Mul gadget combination**: use `combine_MUL_MULHU` (unsigned
  --      MULH variant) instead of `combine_MUL_MULH`.
  --   6. **Two-way case split** on `c = 0`:
  --      * **c = 0**: DBZ clamps + `execute_DIV_REM_pure_int .DRU` close.
  --      * **c ≠ 0**: derive `b.toNat = q.toNat * c.toNat + r.toNat`
  --        via `FKB_add_128` (with `b_neg = rem_neg = 0`, the upper
  --        half of the carry chain collapses to `0 = 0`), then
  --        `r.toNat < c.toNat` from the `LtWordU16Gadget` thunk, and
  --        apply `Nat.div_mod_unique` to conclude.
  -- ========================================================================

  lemma spec_DIVU_REMU
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_divu_remu :
      air.cols.values.is_divu row 0 + air.cols.values.is_remu row 0 = 1)
  :
    ⟨ U64w.toBV #v[air.cols.values.quotient_0  row 0,
                   air.cols.values.quotient_1  row 0,
                   air.cols.values.quotient_2  row 0,
                   air.cols.values.quotient_3  row 0],
      U64w.toBV #v[air.cols.values.remainder_0 row 0,
                   air.cols.values.remainder_1 row 0,
                   air.cols.values.remainder_2 row 0,
                   air.cols.values.remainder_3 row 0] ⟩ =
    RV64IM.execute_DIV_REM_pure
      (U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                    air.cols.values.b_2 row 0, air.cols.values.b_3 row 0])
      (U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                    air.cols.values.c_2 row 0, air.cols.values.c_3 row 0])
      .DRU
  := by
    -- Step 1: Selector exclusivity. The chip's at-most-one constraint
    -- plus `is_div + is_rem = 1` forces the other six selectors to 0.
    obtain ⟨b_div, b_divu, b_rem, b_remu, b_divw, b_remw, b_divuw, b_remuw, h_sum⟩
      := selector_breakdown air row h_constraints
    have eq_div   : air.cols.values.is_div   row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divu_remu; grind
    have eq_rem   : air.cols.values.is_rem   row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divu_remu; grind
    have eq_divw  : air.cols.values.is_divw  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divu_remu; grind
    have eq_remw  : air.cols.values.is_remw  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divu_remu; grind
    have eq_divuw : air.cols.values.is_divuw row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divu_remu; grind
    have eq_remuw : air.cols.values.is_remuw row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divu_remu; grind
    clear b_div b_rem b_divw b_remw b_divuw b_remuw h_sum
    -- Move to gadget specs
    have := gadget_specs_pack air row
    simp only [h_ext, h_wf, h_constraints, h_is_real] at this
    simp [*] at this; clear h_ext h_wf h_constraints
    obtain ⟨ h_ext, h_wf, h_constraints, gadget_specs ⟩ := this
    -- Stabilise h_ext
    obtain ⟨ ub_b_0, ub_b_1, ub_b_2, ub_b_3, ub_c_0, ub_c_1, ub_c_2, ub_c_3 ⟩ :
      (air.cols.values.b_0 row 0).val < 65536 ∧ (air.cols.values.b_1 row 0).val < 65536 ∧ (air.cols.values.b_2 row 0).val < 65536 ∧ (air.cols.values.b_3 row 0).val < 65536 ∧
      (air.cols.values.c_0 row 0).val < 65536 ∧ (air.cols.values.c_1 row 0).val < 65536 ∧ (air.cols.values.c_2 row 0).val < 65536 ∧ (air.cols.values.c_3 row 0).val < 65536
    := by
      clear h_wf h_constraints gadget_specs
      simp [bus_row_ext_asm, ChipExtraBuses] at h_ext; replace h_ext := h_ext.2.2
      simp [ALUBus.externals, ALUBus.validOpcode, ALUBus.operandsInternal, ALUBus.operandRange, *] at h_ext
      apply h_ext.2 <;> clear h_ext <;> grind
    clear h_ext
    -- Get various upper bounds and equalities
    obtain ⟨ ub_q_0, ub_q_1, ub_q_2, ub_q_3, ub_r_0, ub_r_1, ub_r_2, ub_r_3,
             ub_ac_0, ub_ac_1, ub_ac_2, ub_ac_3, ub_ar_0, ub_ar_1, ub_ar_2, ub_ar_3 ⟩ :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧ (air.cols.values.quotient_1 row 0).val < 65536 ∧ (air.cols.values.quotient_2 row 0).val < 65536 ∧ (air.cols.values.quotient_3 row 0).val < 65536 ∧
      (air.cols.values.remainder_0 row 0).val < 65536 ∧ (air.cols.values.remainder_1 row 0).val < 65536 ∧ (air.cols.values.remainder_2 row 0).val < 65536 ∧ (air.cols.values.remainder_3 row 0).val < 65536 ∧
      (air.cols.values.abs_c_0 row 0).val < 65536 ∧ (air.cols.values.abs_c_1 row 0).val < 65536 ∧ (air.cols.values.abs_c_2 row 0).val < 65536 ∧ (air.cols.values.abs_c_3 row 0).val < 65536 ∧
      (air.cols.values.abs_remainder_0 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_1 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_2 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_3 row 0).val < 65536
    := by
      clear gadget_specs
      simp [bus_row_wf_asm, ChipExtraBuses, ByteBus.Spec, *] at h_wf
      simp [h_wf]
    obtain ⟨ eq_rnw, eq_qc_0, eq_qc_1, eq_qc_2, eq_qc_3, eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3 ⟩ :
      air.cols.values.is_real_not_word row 0 = 1 ∧
      air.cols.values.quotient_comp_0 row 0 = air.cols.values.quotient_0 row 0 ∧ air.cols.values.quotient_comp_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.quotient_comp_2 row 0 = air.cols.values.quotient_2 row 0 ∧ air.cols.values.quotient_comp_3 row 0 = air.cols.values.quotient_3 row 0 ∧
      air.cols.values.remainder_comp_0 row 0 = air.cols.values.remainder_0 row 0 ∧ air.cols.values.remainder_comp_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.remainder_comp_2 row 0 = air.cols.values.remainder_2 row 0 ∧ air.cols.values.remainder_comp_3 row 0 = air.cols.values.remainder_3 row 0
    := by
      clear gadget_specs
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      simp [h_constraints]
    -- Stabilise gadget specifications
    simp [*] at gadget_specs
    obtain ⟨ h_mul_lo, h_mul_hi,
             ⟨ b_b_overflow, h_b_overflow ⟩, ⟨ b_c_overflow, h_c_overflow ⟩, ⟨ b_c_zero, h_c_zero ⟩,
             h_abs_c, h_abs_rem, h_rem_check, h_b_msb, h_c_msb, h_rem_msb ⟩ := gadget_specs
    simp [ALUBus.Spec] at h_mul_lo h_mul_hi
    obtain ⟨ ⟨ ub_cq_0, ub_cq_1, ub_cq_2, ub_cq_3 ⟩, h_op_range, h_mul_lo ⟩ := h_mul_lo; clear h_op_range
    obtain ⟨ ⟨ ub_cq_4, ub_cq_5, ub_cq_6, ub_cq_7 ⟩, h_op_range, h_mul_hi ⟩ := h_mul_hi; clear h_op_range
    have mul_spec := RV64IM.combine_MUL_MULHU h_mul_lo h_mul_hi; simp at mul_spec; clear h_mul_lo h_mul_hi
    clear h_abs_rem h_abs_c
    -- Case : c = 0
    obtain eq_cz | eq_cz := b_c_zero <;> simp [eq_cz] at h_c_zero; rotate_left
    . have h_eqz : U64w.toInt #v[0#16, 0#16, 0#16, 0#16] = 0 := by clear *-; decide
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int, ← BitVec.toNat_inj]
      simp [U64w.toNat, *]
      clear *- ub_b_0 ub_b_1 ub_b_2 ub_b_3
      omega
    -- Case: ¬ (c == 0)
    . set c_BV : U64w := #v[
        BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_2 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_3 row 0)] with eq_c_BV
      have h_c_neq_0_bv : ¬ (c_BV.toBV = 0)
      := by
        clear *- h_c_zero ub_c_0 ub_c_1 ub_c_2 ub_c_3
        subst c_BV; intro h_c_bv_zero; apply h_c_zero; clear h_c_zero
        simp [← BitVec.toNat_inj, U64w.toNat] at h_c_bv_zero
        grind
      clear h_c_zero
      have b_overflow : air.cols.values.is_overflow row 0 = 0 ∨ air.cols.values.is_overflow row 0 = 1
      := by
        simp [AbsConstraints_NoGadgets, sub_eq_zero, *] at h_constraints
        clear *- h_constraints; grind
      have h_overflow := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp [*] at h_overflow
      . set b_BV : U64w := #v[
          BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.b_2 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.b_3 row 0)] with eq_b_BV
        simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
        set q_BV : U64w := #v[
          BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.quotient_2 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.quotient_3 row 0)] with eq_q_BV
        set r_BV : U64w := #v[
          BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.remainder_2 row 0),
          BitVec.ofNat 16 ↑(air.cols.values.remainder_3 row 0)] with eq_r_BV
        rw [if_neg (by simp [← BitVec.toNat_inj] at h_c_neq_0_bv; exact h_c_neq_0_bv)]
        simp [← BitVec.toNat_inj, Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg]
        suffices h_div_mod :
          b_BV.toNat / c_BV.toNat = q_BV.toNat ∧
          b_BV.toNat % c_BV.toNat = r_BV.toNat
        . clear *- h_div_mod
          rw [Nat.mod_eq_of_lt (b := 18446744073709551616)]
          . rw [Nat.mod_eq_of_lt (b := 18446744073709551616)]
            . omega
            . apply lt_of_eq_of_lt (b := b_BV.toNat % c_BV.toNat)
              . omega
              . rw [← U64w.toBV_toNat, ← U64w.toBV_toNat]
                grind
          . rw [← U64w.toBV_toNat, ← U64w.toBV_toNat]
            grind
        . rw [Nat.div_mod_unique (by clear *- h_c_neq_0_bv; simp [← BitVec.toNat_inj] at h_c_neq_0_bv; omega), eq_comm]
          obtain ⟨ h_rnw, h_b_neg, h_rem_neg, h_c_neg, h_constraints ⟩ := h_constraints
          simp [h_is_real, eq_div, eq_rem, eq_divw, eq_remw, eq_divuw, eq_remuw] at h_rnw h_b_neg h_rem_neg h_c_neg
          have cond_b_eq_qc_plus_r : b_BV.toNat = q_BV.toNat * c_BV.toNat + r_BV.toNat
          := by
            have cond_bv :
              U128w.toBV
                #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                   air.cols.values.b_2 row 0, air.cols.values.b_3 row 0,
                   0, 0, 0, 0] =
              U128w.toBV
                  #v[air.cols.values.c_times_quotient_0 row 0,
                     air.cols.values.c_times_quotient_1 row 0,
                     air.cols.values.c_times_quotient_2 row 0,
                     air.cols.values.c_times_quotient_3 row 0,
                     air.cols.values.c_times_quotient_4 row 0,
                     air.cols.values.c_times_quotient_5 row 0,
                     air.cols.values.c_times_quotient_6 row 0,
                     air.cols.values.c_times_quotient_7 row 0] +
                U128w.toBV
                  #v[air.cols.values.remainder_0 row 0, air.cols.values.remainder_1 row 0,
                     air.cols.values.remainder_2 row 0, air.cols.values.remainder_3 row 0,
                     0, 0, 0, 0]
            := by
              replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2
              have carries := h_constraints.1
              simp [h_overflow, h_b_neg, h_rem_neg, eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3] at carries
              obtain ⟨ eq_cry_0, eq_cry_1, eq_cry_2, eq_cry_3, eq_cry_4, eq_cry_5, eq_cry_6, eq_cry_7 ⟩ := carries
              replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              obtain ⟨ b_cry_0, b_cry_1, b_cry_2, b_cry_3, b_cry_4, b_cry_5, b_cry_6, b_cry_7, rest ⟩ := h_constraints; clear rest
              simp [sub_eq_zero] at b_cry_0 b_cry_1 b_cry_2 b_cry_3 b_cry_4 b_cry_5 b_cry_6 b_cry_7
              have cond_bv :=
                FKB_add_128 (a4 := 0) (a5 := 0) (a6 := 0) (a7 := 0) (c4 := 0) (c5 := 0) (c6 := 0) (c7 := 0)
                  ub_b_0 ub_b_1 ub_b_2 ub_b_3 (by simp) (by simp) (by simp) (by simp)
                  ub_cq_0 ub_cq_1 ub_cq_2 ub_cq_3 ub_cq_4 ub_cq_5 ub_cq_6 ub_cq_7
                  ub_r_0 ub_r_1 ub_r_2 ub_r_3 (by simp) (by simp) (by simp) (by simp)
                  (by clear *- eq_cry_0; omega) (by clear *- eq_cry_1; omega) (by clear *- eq_cry_2; omega) (by clear *- eq_cry_3; omega)
                  (by clear *- eq_cry_4; omega) (by clear *- eq_cry_5; omega) (by clear *- eq_cry_6; omega) (by clear *- eq_cry_7; omega)
                  b_cry_0 b_cry_1 b_cry_2 b_cry_3 b_cry_4 b_cry_5 b_cry_6 b_cry_7
              simp at cond_bv; exact cond_bv
            clear h_constraints
            have h_b_ext :
              (#v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                  air.cols.values.b_2 row 0, air.cols.values.b_3 row 0,
                  0, 0, 0, 0] : U128w) = b_BV.extend false
              := by subst b_BV; simp [U64w.extend, U64w.ext]
            have h_r_ext :
              (#v[air.cols.values.remainder_0 row 0, air.cols.values.remainder_1 row 0,
                  air.cols.values.remainder_2 row 0, air.cols.values.remainder_3 row 0,
                  0, 0, 0, 0] : U128w) = r_BV.extend false
              := by subst r_BV; simp [U64w.extend, U64w.ext]
            rw [h_b_ext, mul_spec, h_r_ext] at cond_bv; clear h_b_ext h_r_ext mul_spec
            simp [← BitVec.toNat_inj] at cond_bv; rw [cond_bv]
            apply Nat.mod_eq_of_lt
            have ub_q : q_BV.toNat < 18446744073709551616 := by clear *-; simp [U64w.toNat]; omega
            have ub_r : r_BV.toNat < 18446744073709551616 := by clear *-; simp [U64w.toNat]; omega
            have ub_c : c_BV.toNat < 18446744073709551616 := by clear *-; simp [U64w.toNat]; omega
            clear *- ub_q ub_r ub_c; nlinarith
          have cond_lt : r_BV.toNat < c_BV.toNat
          := by
            replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            simp [*] at h_constraints
            obtain ⟨ eq_abs_c, eq_abs_rem, eq_m_0, eq_m_1, eq_m_2, eq_m_3, eq_rem_check, h_constraints ⟩ := h_constraints
            replace h_constraints := h_constraints.2.2.2.2.1
            simp [eq_rem_check] at h_constraints
            simp [*] at h_rem_check
            clear *- h_rem_check; subst r_BV c_BV; exact h_rem_check
          clear *- cond_b_eq_qc_plus_r cond_lt
          grind

  -- ========================================================================
  -- spec_DIVW_REMW  (paired): both signed 32-bit W selectors at once.
  -- Result: the chip's `(quotient, remainder)` limbs (sign-extended to
  -- 64 bits per `q_i = quot_msb · 0xFFFF`, `r_i = rem_msb · 0xFFFF`
  -- for `i ∈ {2,3}`) equal the pair
  -- `execute_DIVW_REMW_pure (b.setWidth 32) (c.setWidth 32) .DRS`.

  -- Proof structure mirrors `spec_DIVUW_REMUW` (lower `MulGadget`
  -- only, 32-bit carry-chain identity), with three substantive
  -- additions from the signed 64-bit case:
  --   * **Overflow clamp** — `INT_MIN_32 / -1` is identified via the
  --     32-bit `IsEqualWordGadget` thunks (`is_overflow_b` /
  --     `is_overflow_c` gated by `is_word_operation = 1`), and the
  --     chip clamps `q = b.setWidth 32`, `r = 0` in that case.
  --   * **Sign reasoning** — `is_signed_type = 1` so `b_neg`,
  --     `c_neg`, `rem_neg` are nonzero in general; sign-consistency
  --     (`rem_neg = 1 → b_neg = 1`) and `b_msb` / `r_msb` /
  --     `c_msb` couplings via the `U16MSBGadget`s on `b_1` / `r_1` /
  --     `c_1` (gated by `is_word_operation`).
  --   * **Equation lifted is signed**: `Int.tdiv_tmod_unique_full`
  --     applies to the 32-bit signed product `b32 = q32 · c32 + r32`
  --     with `|r32| < |c32|` from the `LtWordU16Gadget` thunk.
  -- ========================================================================

  lemma spec_DIVW_REMW
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_divw_remw :
      air.cols.values.is_divw row 0 + air.cols.values.is_remw row 0 = 1)
  :
    ⟨ U64w.toBV #v[air.cols.values.quotient_0  row 0,
                   air.cols.values.quotient_1  row 0,
                   air.cols.values.quotient_2  row 0,
                   air.cols.values.quotient_3  row 0],
      U64w.toBV #v[air.cols.values.remainder_0 row 0,
                   air.cols.values.remainder_1 row 0,
                   air.cols.values.remainder_2 row 0,
                   air.cols.values.remainder_3 row 0] ⟩ =
    RV64IM.execute_DIVW_REMW_pure
      ((U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                     air.cols.values.b_2 row 0, air.cols.values.b_3 row 0]).setWidth 32)
      ((U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                     air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]).setWidth 32)
      .DRS
  := by
    -- Step 1: Selector cleanup. `is_divw + is_remw = 1` forces the other
    -- six selectors to 0 via `selector_breakdown` + the exact-one constraint.
    obtain ⟨b_div, b_divu, b_rem, b_remu, b_divw, b_remw, b_divuw, b_remuw, h_sum⟩
      := selector_breakdown air row h_constraints
    have eq_div   : air.cols.values.is_div   row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divw_remw; grind
    have eq_divu  : air.cols.values.is_divu  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divw_remw; grind
    have eq_rem   : air.cols.values.is_rem   row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divw_remw; grind
    have eq_remu  : air.cols.values.is_remu  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divw_remw; grind
    have eq_divuw : air.cols.values.is_divuw row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divw_remw; grind
    have eq_remuw : air.cols.values.is_remuw row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divw_remw; grind
    clear b_div b_divu b_rem b_remu b_divuw b_remuw h_sum
    -- Step 2: Move to gadget specs via `gadget_specs_pack`.
    have := gadget_specs_pack air row
    simp only [h_ext, h_wf, h_constraints, h_is_real] at this
    simp [*] at this; clear h_ext h_wf h_constraints
    obtain ⟨ h_ext, h_wf, h_constraints, gadget_specs ⟩ := this
    -- Step 3: Operand bounds on b, c from the chip's ALU bus externals
    -- (opcodes 49 = DIVW and 51 = REMW are NOT in `operandsInternal`,
    -- so externals supply the operand range).
    obtain ⟨ ub_b_0, ub_b_1, ub_b_2, ub_b_3, ub_c_0, ub_c_1, ub_c_2, ub_c_3 ⟩ :
      (air.cols.values.b_0 row 0).val < 65536 ∧ (air.cols.values.b_1 row 0).val < 65536 ∧ (air.cols.values.b_2 row 0).val < 65536 ∧ (air.cols.values.b_3 row 0).val < 65536 ∧
      (air.cols.values.c_0 row 0).val < 65536 ∧ (air.cols.values.c_1 row 0).val < 65536 ∧ (air.cols.values.c_2 row 0).val < 65536 ∧ (air.cols.values.c_3 row 0).val < 65536
    := by
      clear h_wf h_constraints gadget_specs
      simp [bus_row_ext_asm, ChipExtraBuses] at h_ext; replace h_ext := h_ext.2.2
      simp [ALUBus.externals, ALUBus.validOpcode, ALUBus.operandsInternal, ALUBus.operandRange, *] at h_ext
      apply h_ext.2 <;> clear h_ext <;> grind
    clear h_ext
    -- Step 4: u16 bounds on q, r, ac, ar via `ChipExtraBuses`' byte bus.
    obtain ⟨ ub_q_0, ub_q_1, ub_q_2, ub_q_3, ub_r_0, ub_r_1, ub_r_2, ub_r_3,
             ub_ac_0, ub_ac_1, ub_ac_2, ub_ac_3, ub_ar_0, ub_ar_1, ub_ar_2, ub_ar_3 ⟩ :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧ (air.cols.values.quotient_1 row 0).val < 65536 ∧ (air.cols.values.quotient_2 row 0).val < 65536 ∧ (air.cols.values.quotient_3 row 0).val < 65536 ∧
      (air.cols.values.remainder_0 row 0).val < 65536 ∧ (air.cols.values.remainder_1 row 0).val < 65536 ∧ (air.cols.values.remainder_2 row 0).val < 65536 ∧ (air.cols.values.remainder_3 row 0).val < 65536 ∧
      (air.cols.values.abs_c_0 row 0).val < 65536 ∧ (air.cols.values.abs_c_1 row 0).val < 65536 ∧ (air.cols.values.abs_c_2 row 0).val < 65536 ∧ (air.cols.values.abs_c_3 row 0).val < 65536 ∧
      (air.cols.values.abs_remainder_0 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_1 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_2 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_3 row 0).val < 65536
    := by
      clear gadget_specs
      simp [bus_row_wf_asm, ChipExtraBuses, ByteBus.Spec, *] at h_wf
      simp [h_wf]
    -- Step 5: From `AbsConstraints_NoGadgets`, derive the signed-W identities.
    -- Word-op branch fires (`is_word_operation = is_divw + is_remw = 1`),
    -- signed-word branch fires too (`is_signed_word_operation = 1`,
    -- `is_signed_type = 1`):
    --   * `is_real_not_word = 0`,
    --   * sign pairings collapse to `b_neg = b_msb`, `rem_neg = r_msb`,
    --     `c_neg = c_msb`,
    --   * `qc_0 = q_0`, `qc_1 = q_1`,
    --     `qc_2 = qc_3 = quot_msb · 0xFFFF`,
    --   * `rc_0 = r_0`, `rc_1 = r_1`,
    --     `rc_2 = rc_3 = rem_msb · 0xFFFF`,
    --   * `q_2 = q_3 = quot_msb · 0xFFFF`,
    --     `r_2 = r_3 = rem_msb · 0xFFFF`,
    --   * `b_2 = b_3 = b_neg · 0xFFFF` (new b-extension constraint),
    --   * `c_2 = c_3 = c_neg · 0xFFFF` (c-extension constraint).
    obtain ⟨ eq_rnw,
             eq_b_neg_msb, eq_rem_neg_msb, eq_c_neg_msb,
             eq_qc_0, eq_qc_1, eq_qc_2, eq_qc_3,
             eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3,
             eq_b_2, eq_b_3, eq_c_2, eq_c_3,
             eq_q_msb_2, eq_q_msb_3, eq_r_msb_2, eq_r_msb_3 ⟩ :
      air.cols.values.is_real_not_word row 0 = 0 ∧
      air.cols.values.b_neg   row 0 = air.cols.values.b_msb.msb   row 0 ∧
      air.cols.values.rem_neg row 0 = air.cols.values.rem_msb.msb row 0 ∧
      air.cols.values.c_neg   row 0 = air.cols.values.c_msb.msb   row 0 ∧
      air.cols.values.quotient_comp_0 row 0 = air.cols.values.quotient_0 row 0 ∧
      air.cols.values.quotient_comp_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.quotient_comp_2 row 0 = air.cols.values.quot_msb.msb row 0 * 65535 ∧
      air.cols.values.quotient_comp_3 row 0 = air.cols.values.quot_msb.msb row 0 * 65535 ∧
      air.cols.values.remainder_comp_0 row 0 = air.cols.values.remainder_0 row 0 ∧
      air.cols.values.remainder_comp_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.remainder_comp_2 row 0 = air.cols.values.rem_msb.msb row 0 * 65535 ∧
      air.cols.values.remainder_comp_3 row 0 = air.cols.values.rem_msb.msb row 0 * 65535 ∧
      air.cols.values.b_2 row 0 = air.cols.values.b_neg row 0 * 65535 ∧
      air.cols.values.b_3 row 0 = air.cols.values.b_neg row 0 * 65535 ∧
      air.cols.values.c_2 row 0 = air.cols.values.c_neg row 0 * 65535 ∧
      air.cols.values.c_3 row 0 = air.cols.values.c_neg row 0 * 65535 ∧
      air.cols.values.quotient_2  row 0 = air.cols.values.quot_msb.msb row 0 * 65535 ∧
      air.cols.values.quotient_3  row 0 = air.cols.values.quot_msb.msb row 0 * 65535 ∧
      air.cols.values.remainder_2 row 0 = air.cols.values.rem_msb.msb  row 0 * 65535 ∧
      air.cols.values.remainder_3 row 0 = air.cols.values.rem_msb.msb  row 0 * 65535
    := by
      clear gadget_specs
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      simp [h_constraints]
    -- Step 6: Stabilise gadget specs. With `is_real = 1`, lower `MulGadget`
    -- thunk fires. With `is_real_not_word = 0`, the upper `MulGadget`, the
    -- two 64-bit `IsEqualWord` thunks, and the three 64-bit `U16MSB`
    -- thunks collapse to `True`. The two 32-bit `IsEqualWord` thunks
    -- (gated by `is_word_operation = 1`) and the four 32-bit `U16MSB`
    -- thunks DO fire. The `AddGadget` × 2 and `LtWordU16` thunks remain
    -- conditional (on `*_event` gates).
    simp [*] at gadget_specs
    obtain ⟨ h_mul_lo,
             ⟨ b_b_overflow_w, h_b_overflow_w ⟩,
             ⟨ b_c_overflow_w, h_c_overflow_w ⟩,
             ⟨ b_c_zero, h_c_zero ⟩,
             h_abs_c, h_abs_rem, h_rem_check,
             h_b_msb_w, h_c_msb_w, h_rem_msb_w, h_quot_msb_w ⟩
      := gadget_specs
    -- Unpack `h_mul_lo : ALUBus.Spec 30 cq_low qc c` into its parts.
    simp [ALUBus.Spec] at h_mul_lo
    obtain ⟨ ⟨ ub_cq_0, ub_cq_1, ub_cq_2, ub_cq_3 ⟩, h_op_range, h_mul_lo ⟩
      := h_mul_lo
    clear h_op_range
    -- Step 7: Sign-extension setup. Define `q_BV / r_BV / b_BV / c_BV :
    -- U32w` as the low 32-bit halves; then prove each chip 64-bit
    -- column equals the *signed* 64-bit extension of its `U32w`
    -- counterpart. The U16MSB gadgets on `q_1` / `r_1` / `b_1` / `c_1`
    -- pin the relevant high-bit, and the chip's `_2`/`_3` columns are
    -- `*_msb · 0xFFFF` (q, r) or `*_neg · 0xFFFF` (b, c, with
    -- `*_neg = *_msb` from `eq_*_neg_msb`).
    set q_BV : U32w := #v[
      BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0),
      BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0)] with eq_q_BV
    set r_BV : U32w := #v[
      BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0),
      BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0)] with eq_r_BV
    set b_BV : U32w := #v[
      BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
      BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)] with eq_b_BV
    set c_BV : U32w := #v[
      BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0),
      BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0)] with eq_c_BV
    have h_q_ext_t :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.quotient_2 row 0), BitVec.ofNat 16 ↑(air.cols.values.quotient_3 row 0)] =
        (q_BV.extend true).toBV
    := by
      simp [eq_q_msb_2, eq_q_msb_3]
      subst q_BV; clear *- h_quot_msb_w ub_q_1
      simp [U32w.extend, U32w.ext]; congr 3; simp
      simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
      grind
    have h_r_ext_t :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.remainder_2 row 0), BitVec.ofNat 16 ↑(air.cols.values.remainder_3 row 0)] =
        (r_BV.extend true).toBV
    := by
      simp [eq_r_msb_2, eq_r_msb_3]
      subst r_BV; clear *- h_rem_msb_w ub_r_1
      simp [U32w.extend, U32w.ext]; congr 3; simp
      simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
      grind
    have h_b_ext_t :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.b_2 row 0), BitVec.ofNat 16 ↑(air.cols.values.b_3 row 0)] =
        (b_BV.extend true).toBV
    := by
      simp [eq_b_2, eq_b_3, eq_b_neg_msb]
      subst b_BV; clear *- h_b_msb_w ub_b_1
      simp [U32w.extend, U32w.ext]; congr 3; simp
      simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
      grind
    have h_c_ext_t :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.c_2 row 0), BitVec.ofNat 16 ↑(air.cols.values.c_3 row 0)] =
        (c_BV.extend true).toBV
    := by
      simp [eq_c_2, eq_c_3, eq_c_neg_msb]
      subst c_BV; clear *- h_c_msb_w ub_c_1
      simp [U32w.extend, U32w.ext]; congr 3; simp
      simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
      grind
    -- Rewrite the goal in terms of the `U32w`-extended forms. The
    -- executor's `BitVec.setWidth 32 (x.extend true).toBV = x.toBV`
    -- (low 32 bits of a sign-extension is the original).
    rw [h_q_ext_t, h_r_ext_t, h_b_ext_t, h_c_ext_t]
    trans execute_DIVW_REMW_pure b_BV.toBV c_BV.toBV drop.DRS; rotate_left
    . subst b_BV c_BV; simp [U32w.extend]
    . simp [execute_DIVW_REMW_pure, U32w.extend_BitVec_extend, BitVec.extend]
      suffices h_int_eq :
        q_BV.toInt = (execute_DIVW_REMW_pure_int b_BV.toBV c_BV.toBV drop.DRS).1 ∧
        r_BV.toInt = (execute_DIVW_REMW_pure_int b_BV.toBV c_BV.toBV drop.DRS).2
      . clear *- h_int_eq
        have q_range := U32w.toInt_range q_BV; have r_range := U32w.toInt_range r_BV
        simp [← BitVec.toInt_inj, BitVec.toInt_signExtend_of_le]
        iterate 2 rw [Int.bmod_eq_of_le (by omega) (by omega)]
        assumption
      -- Three-way case split on (c = 0) / overflow / normal.
      . simp [execute_DIVW_REMW_pure_int]
        -- Case 1: `is_c_0.result = 1` ⇒ c_lo = 0, DBZ clamp fires.
        -- Case 2: `is_c_0.result = 0`, then case-split on `is_overflow`:
        --   2a: `is_overflow = 1` ⇒ b_lo = INT_MIN_32, c_lo = -1, overflow clamp.
        --   2b: `is_overflow = 0` ⇒ apply `Int.tdiv_tmod_unique_full`
        --       at 32-bit width on the lower MulGadget identity + LtWordU16
        --       + sign-consistency.
        obtain eq_cz | eq_cz := b_c_zero <;> simp [eq_cz] at h_c_zero; rotate_left
        . -- c = 0: `is_c_0.result = 1`.
          obtain ⟨ eq_c_0, eq_c_1, eq_c_msb_0 ⟩ := h_c_zero
          have h_c_zero_int : c_BV.toInt = 0
          := by
            subst c_BV
            clear *- eq_c_0 eq_c_1
            simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat, eq_c_0, eq_c_1]
          rw [if_pos h_c_zero_int]
          -- DBZ clamp from `AbsConstraints_NoGadgets` section 13.
          simp [AbsConstraints_NoGadgets, *] at h_constraints
          replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.1
          obtain ⟨ eq_q_0, eq_q_1, eq_q_msb, eq_b_0, eq_b_1 ⟩ := h_constraints
          refine ⟨?_, ?_⟩
          . -- q_BV.toInt = -1
            subst q_BV
            clear *- eq_q_0 eq_q_1
            simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                  U32w.toNat, eq_q_0, eq_q_1]
          . subst r_BV b_BV
            simp [h_c_zero_int, eq_b_0, eq_b_1]
        . -- c ≠ 0: case-split on overflow.
          have h_c_nz : c_BV.toInt ≠ 0
          := by
            subst c_BV
            clear *- h_c_zero ub_c_0 ub_c_1 h_c_msb_w
            simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
            grind
          have b_overflow : air.cols.values.is_overflow row 0 = 0 ∨ air.cols.values.is_overflow row 0 = 1
          := by
            simp [AbsConstraints_NoGadgets, sub_eq_zero, *] at h_constraints
            clear *- h_constraints; grind
          obtain eq_overflow | eq_overflow := b_overflow; rotate_left
          . -- 2a: Overflow case (is_overflow = 1).
            -- From `is_overflow = is_overflow_b · is_overflow_c · is_signed_type`
            -- (sec 8c) plus the booleans on the result columns:
            --   is_overflow_b.result = 1 ∧ is_overflow_c.result = 1
            -- which via `h_b_overflow_w` / `h_c_overflow_w` gives:
            --   b_0 = 0, b_1 = 32768 (b_lo = INT_MIN_32)
            --   c_0 = 65535, c_1 = 65535 (c_lo = -1_32)
            -- The overflow clamp (sec 8d) then gives:
            --   q_0 = b_0 = 0, q_1 = b_1 = 32768
            --   r_0 = r_1 = 0
            -- so q_BV.toInt = -2^31 and r_BV.toInt = 0, both of which
            -- match the executor's overflow branch (q = -2^31, r = 0).
            . simp [AbsConstraints_NoGadgets, *, sub_eq_zero] at h_constraints
              have h_iof :
                air.cols.values.is_overflow_b.is_diff_zero.result row 0 = 1 ∧
                air.cols.values.is_overflow_c.is_diff_zero.result row 0 = 1
              := by
                clear *- h_constraints eq_overflow b_b_overflow_w b_c_overflow_w
                grind
              simp [h_iof.1, h_iof.2] at h_b_overflow_w h_c_overflow_w
              obtain ⟨ eq_b_0, eq_b_1 ⟩ := h_b_overflow_w
              obtain ⟨ eq_c_0, eq_c_1 ⟩ := h_c_overflow_w
              have h_clamp :
                air.cols.values.quotient_0 row 0 = air.cols.values.b_0 row 0 ∧
                air.cols.values.quotient_1 row 0 = air.cols.values.b_1 row 0 ∧
                air.cols.values.remainder_0 row 0 = 0 ∧
                air.cols.values.remainder_1 row 0 = 0
              := by
                clear *- h_constraints eq_overflow
                aesop
              obtain ⟨ eq_q_0, eq_q_1, eq_r_0, eq_r_1 ⟩ := h_clamp
              have h_b_int : b_BV.toInt = -2147483648
              := by
                subst b_BV
                clear *- eq_b_0 eq_b_1
                simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                      U32w.toNat, eq_b_0, eq_b_1]
              have h_c_int : c_BV.toInt = -1
              := by
                subst c_BV
                clear *- eq_c_0 eq_c_1
                simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                      U32w.toNat, eq_c_0, eq_c_1]
              rw [if_neg (by rw [h_c_int]; decide),
                  if_pos ⟨h_b_int, h_c_int⟩]
              simp [h_b_int, h_c_int]
              refine ⟨?_, ?_⟩
              . -- q_BV.toInt = -2^31
                subst q_BV
                clear *- eq_q_0 eq_q_1 eq_b_0 eq_b_1
                simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                      U32w.toNat, eq_q_0, eq_q_1, eq_b_0, eq_b_1]
              . -- r_BV.toInt = 0
                subst r_BV
                clear *- eq_r_0 eq_r_1
                simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                      U32w.toNat, eq_r_0, eq_r_1]
          . -- 2b: Normal case (c ≠ 0 and is_overflow = 0).
            simp [AbsConstraints_NoGadgets, *, sub_eq_zero] at h_constraints
            -- Step 1: discharge the executor's two `if`s.
            --   (a) `c ≠ 0` via the outer-scope `h_c_nz`.
            --   (b) `¬ (b = -2^31 ∧ c = -1)` from `eq_overflow = 0`
            --       (sec 8c): if both held, `b_0 = 0 ∧ b_1 = 32768` and
            --       `c_0 = 65535 ∧ c_1 = 65535`, which via
            --       `h_b_overflow_w.mpr` / `h_c_overflow_w.mpr` force
            --       `is_overflow_b.result = 1` and
            --       `is_overflow_c.result = 1`. Combined with
            --       `is_signed_type = is_divw + is_remw = 1` and the
            --       sec 8c definition `is_overflow = is_signed_type ·
            --       is_overflow_b.result · is_overflow_c.result`,
            --       this gives `is_overflow = 1`, contradicting
            --       `eq_overflow = 0`.
            have h_not_ovf : ¬ (b_BV.toInt = -2147483648 ∧ c_BV.toInt = -1)
            := by
              intro ⟨h_b_int, h_c_int⟩
              have eq_b : air.cols.values.b_0 row 0 = 0 ∧
                          air.cols.values.b_1 row 0 = 32768
              := by
                subst b_BV
                clear *- ub_b_0 ub_b_1 h_b_int
                simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                      U32w.toNat] at h_b_int
                split_ifs at h_b_int <;> grind
              have eq_c : air.cols.values.c_0 row 0 = 65535 ∧
                          air.cols.values.c_1 row 0 = 65535
              := by
                subst c_BV
                clear *- ub_c_0 ub_c_1 h_c_int
                simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide,
                      U32w.toNat] at h_c_int
                split_ifs at h_c_int <;> grind
              have iob_result :
                air.cols.values.is_overflow_b.is_diff_zero.result row 0 = 1
                := h_b_overflow_w.mpr eq_b
              have ioc_result :
                air.cols.values.is_overflow_c.is_diff_zero.result row 0 = 1
                := h_c_overflow_w.mpr eq_c
              clear *- h_constraints eq_overflow iob_result ioc_result
              grind
            rw [if_neg h_c_nz, if_neg h_not_ovf]
            -- Step 2: invoke `Int.tdiv_tmod_unique_full` to convert the
            -- goal from `q = tdiv b c ∧ r = tmod b c` to the
            -- three-condition form:
            --   `b = q·c + r ∧ |r| < |c| ∧ (r = 0 ∨ sign r = sign b)`.
            -- We prove the three conditions as separate `have`s rather
            -- than via `refine ⟨?_, ?_, ?_⟩`, because cond_2 / cond_3
            -- depend on cond_1 (the integer equation `b = q·c + r`).
            rw [Int.tdiv_tmod_unique_full h_c_nz]
            -- 3a: integer equation b_BV.toInt = q_BV.toInt · c_BV.toInt + r_BV.toInt.
            --
            -- Strategy (mirrors `spec_DIVUW_REMUW` and the signed RV32IM
            -- proof):
            --   (a) Extract the four lower carry equations (sec 9, branch
            --       `is_overflow = 0`) and the four lower carry-bit
            --       booleans (sec 22) from `h_constraints`.
            --   (b) Apply `FKB_add_64` to get a U64w identity at column
            --       level: `U64w[b_0..3] = U64w[cq_0..3] + U64w[r_0..3]`.
            --   (c) Align `h_q_ext_t` / `h_c_ext_t` with the column form
            --       used in `h_mul_lo` (which uses `quot_msb · 0xFFFF` /
            --       `c_msb · 0xFFFF` in the upper limbs), then substitute
            --       `h_mul_lo` to land at the BitVec-64 product form.
            --   (d) Lift to integer equation via `BitVec.toInt_inj` +
            --       `Int.bmod_eq_of_le` (bounds:
            --       `|q.toInt · c.toInt + r.toInt| ≤ 2^62 + 2^31 < 2^63`).
            --   (e) Use `U32w.extend_toInt` (sign-extension preserves
            --       `toInt`) to collapse extended `toInt`s back to U32w.
            have cond_1 :
              b_BV.toInt = q_BV.toInt * c_BV.toInt + r_BV.toInt
            := by
              -- Step (a)+(b): U64w identity at column level via FKB_add_64.
              have alu_sum :
                U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.b_2 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.b_3 row 0)] =
                U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.c_times_quotient_0 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.c_times_quotient_1 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.c_times_quotient_2 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.c_times_quotient_3 row 0)] +
                U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.remainder_2 row 0),
                             BitVec.ofNat 16 ↑(air.cols.values.remainder_3 row 0)]
              := by
                have ⟨ eq_p_0, eq_p_1, eq_p_2, eq_p_3,
                       b_cry_0, b_cry_1, b_cry_2, b_cry_3 ⟩ :
                  (air.cols.values.c_times_quotient_0 row 0 + air.cols.values.remainder_0 row 0
                   - air.cols.values.carry_0 row 0 * 65536 = air.cols.values.b_0 row 0) ∧
                  (air.cols.values.c_times_quotient_1 row 0 + air.cols.values.remainder_1 row 0
                   - air.cols.values.carry_1 row 0 * 65536 + air.cols.values.carry_0 row 0
                   = air.cols.values.b_1 row 0) ∧
                  (air.cols.values.c_times_quotient_2 row 0 + air.cols.values.remainder_2 row 0
                   - air.cols.values.carry_2 row 0 * 65536 + air.cols.values.carry_1 row 0
                   = air.cols.values.b_2 row 0) ∧
                  (air.cols.values.c_times_quotient_3 row 0 + air.cols.values.remainder_3 row 0
                   - air.cols.values.carry_3 row 0 * 65536 + air.cols.values.carry_2 row 0
                   = air.cols.values.b_3 row 0) ∧
                  (air.cols.values.carry_0 row 0 = 0 ∨ air.cols.values.carry_0 row 0 = 1) ∧
                  (air.cols.values.carry_1 row 0 = 0 ∨ air.cols.values.carry_1 row 0 = 1) ∧
                  (air.cols.values.carry_2 row 0 = 0 ∨ air.cols.values.carry_2 row 0 = 1) ∧
                  (air.cols.values.carry_3 row 0 = 0 ∨ air.cols.values.carry_3 row 0 = 1)
                := by
                  clear *- h_constraints eq_overflow
                            eq_rc_0 eq_rc_1 eq_rc_2 eq_rc_3
                            eq_r_msb_2 eq_r_msb_3 eq_b_2 eq_b_3
                            eq_rem_neg_msb eq_b_neg_msb eq_c_neg_msb
                  grind
                exact FKB_add_64
                  ub_b_0 ub_b_1 ub_b_2 ub_b_3
                  ub_cq_0 ub_cq_1 ub_cq_2 ub_cq_3
                  ub_r_0 ub_r_1 ub_r_2 ub_r_3
                  eq_p_0 eq_p_1 eq_p_2 eq_p_3
                  b_cry_0 b_cry_1 b_cry_2 b_cry_3
              clear h_constraints
              -- Step (c): align h_q_ext_t / h_c_ext_t with the inner U64w
              -- forms of h_mul_lo (which use `quot_msb · 65535` and
              -- `c_msb · 65535` in the upper limbs).
              simp only [eq_q_msb_2, eq_q_msb_3] at h_q_ext_t
              simp only [eq_c_2, eq_c_3, eq_c_neg_msb] at h_c_ext_t
              -- Substitute h_mul_lo + h_q_ext_t + h_c_ext_t + h_b_ext_t +
              -- h_r_ext_t into alu_sum.
              rw [h_b_ext_t, h_r_ext_t, h_mul_lo, h_q_ext_t, h_c_ext_t] at alu_sum
              -- Unfold execute_MUL_pure (.MUL = lower 64 bits of 128-bit product).
              have h_eq_extract :
                forall (x y : BitVec 64),
                  BitVec.extractLsb 63 0 (BitVec.setWidth 128 x * BitVec.setWidth 128 y) = x * y
                := by clear *-; intro x y; bv_decide
              simp [execute_MUL_pure, BitVec.extend, ← BitVec.toInt_inj, h_eq_extract,-BitVec.toInt_extractLsb] at alu_sum
              -- Step (d)+(e): lift the 64-bit BitVec equation to integers.
              rw [alu_sum]
              have q_range := U32w.toInt_range q_BV
              have c_range := U32w.toInt_range c_BV
              have r_range := U32w.toInt_range r_BV
              clear *- q_range c_range r_range
              exact Int.bmod_eq_of_le (by simp; nlinarith) (by simp; nlinarith)
            -- 3b: |r_BV.toInt| < |c_BV.toInt|.
            --
            -- Strategy (mirrors the 64-bit signed `cond_abs` block of
            -- `spec_DIV_REM`):
            --   (a) Set up U64w-storage `ac_BV`, `ar_BV` from the chip's
            --       `abs_c_*` and `abs_remainder_*` columns.
            --   (b) Extract the relevant identities from `h_constraints`:
            --       sec 14 abs identities (when not negative), sec 15
            --       `max_abs_c_or_1_i = abs_c_i` (since `is_c_0 = 0`),
            --       sec 16 `remainder_check_multiplicity = 1`, sec 16
            --       alu-event tags, sec 18 `value = 0` clamp, sec 20
            --       PR #101 `bit = 1` pin.
            --   (c) Specialize `h_abs_c` / `h_abs_rem` (the AddGadget
            --       thunks) with the alu events and `value = 0` to get
            --       `U64w[c.ext_t] + U64w[abs_c] = 0` (and same for r).
            --   (d) Specialize `h_rem_check` (LtWordU16Gadget thunk)
            --       with `bit = 1` and `max = abs_c` to get
            --       `ar_BV.toNat < ac_BV.toNat`.
            --   (e) Prove `ar_BV.toNat = r_BV.toInt.natAbs` and
            --       `ac_BV.toNat = c_BV.toInt.natAbs` by case-split on
            --       `h_rem_msb_w` / `h_c_msb_w` (which give the sign of
            --       r / c).
            --   (f) Combine and convert `< natAbs` to `|.| < |.|`.
            have cond_2 : |r_BV.toInt| < |c_BV.toInt|
            := by
              set ac_BV : U64w := #v[
                BitVec.ofNat 16 ↑(air.cols.values.abs_c_0 row 0),
                BitVec.ofNat 16 ↑(air.cols.values.abs_c_1 row 0),
                BitVec.ofNat 16 ↑(air.cols.values.abs_c_2 row 0),
                BitVec.ofNat 16 ↑(air.cols.values.abs_c_3 row 0)] with eq_ac_BV
              set ar_BV : U64w := #v[
                BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_0 row 0),
                BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_1 row 0),
                BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_2 row 0),
                BitVec.ofNat 16 ↑(air.cols.values.abs_remainder_3 row 0)] with eq_ar_BV
              -- (b) Extract identities from h_constraints by direct
              -- destructure. The top-level layout of h_constraints
              -- (post the top-of-2b simp) is:
              --   1. `iob.result = 0 ∨ ioc.result = 0`             (sec 8c)
              --   2. `b_neg_not_overflow = b_msb.msb`              (sec 8c)
              --   3. `b_not_neg_not_overflow = 1 - b_msb.msb`      (sec 8c)
              --   4. carry-chain conjunction (8 limbs of cqr = b)  (sec 9)
              --   5. `is_divw = 1 → ...`                            (sec 10)
              --   6. `is_remw = 1 → ...`                            (sec 10)
              --   7. `rem_msb.msb = 1 → b_msb.msb = 1`              (sec 11)
              --   8. sec 11 disjunction
              --      `(r_sum = 0 ∨ rem_msb = 1) ∨ b_msb = 0`
              --   9. `c_msb.msb = 0 → abs_c = c …`                  (sec 14 c)
              --   10. `rem_msb.msb = 0 → abs_r = r …`               (sec 14 r)
              --   11-14. `max_abs_c_or_1_i = abs_c_i` for i=0..3    (sec 15)
              --   15. `remainder_check_multiplicity = 1`            (sec 16)
              --   16. `abs_c_alu_event = c_msb.msb`                 (sec 16)
              --   17. `abs_rem_alu_event = rem_msb.msb`             (sec 16)
              --   18. `abs_c_alu_event = 1 → c_neg_gadget.value_* = 0` (sec 18)
              --   19. `abs_rem_alu_event = 1 → rem_neg_gadget.value_* = 0`
              --   20. `remainder_check_multiplicity = 1 → bit = 1`  (sec 20)
              --   …then the carry-bit booleans + selector booleans  (sec 22).
              obtain ⟨ _, _, _, _, _, _, _, _,
                       h_c_neg_abs, h_r_neg_abs,
                       h_eq_max_0, h_eq_max_1, h_eq_max_2, h_eq_max_3,
                       h_eq_rem_check,
                       h_abs_c_alu, h_abs_rem_alu,
                       h_c_neg_gadget_val, h_rem_neg_gadget_val,
                       h_is_lt, _ ⟩ := h_constraints
              -- (c) Specialize h_abs_c, h_abs_rem with the alu events.
              rw [h_abs_c_alu] at h_abs_c h_c_neg_gadget_val
              rw [h_abs_rem_alu] at h_abs_rem h_rem_neg_gadget_val
              -- (d) Fire h_rem_check with rem_check_multiplicity = 1 + max = abs_c + bit = 1.
              simp [h_eq_rem_check, h_is_lt, h_eq_max_0, h_eq_max_1, h_eq_max_2, h_eq_max_3,
                    ub_ac_0, ub_ac_1, ub_ac_2, ub_ac_3] at h_rem_check
              -- h_rem_check now: ar_BV.toNat < ac_BV.toNat.
              -- (f) Convert |.| to natAbs and reduce to a natural comparison.
              suffices h_natAbs : r_BV.toInt.natAbs < c_BV.toInt.natAbs
              . clear *- h_natAbs; (iterate 2 rw [Int.abs_eq_natAbs]); omega
              -- (e) Prove ar_BV.toNat = r_BV.toInt.natAbs.
              have eq_ar : ar_BV.toNat = r_BV.toInt.natAbs
              := by
                clear *- ub_r_0 ub_r_1 ub_r_2 ub_r_3 ub_ar_0 ub_ar_1 ub_ar_2 ub_ar_3
                         h_rem_msb_w eq_r_msb_2 eq_r_msb_3 eq_rem_neg_msb
                         h_abs_rem h_r_neg_abs h_rem_neg_gadget_val
                obtain ⟨ h_rem_zero, h_pos ⟩ | ⟨ h_rem_one, h_neg ⟩ := h_rem_msb_w
                . -- rem_msb = 0 ⇒ r ≥ 0 ⇒ abs_r = r.
                  -- The alu event branch is gated by `rem_neg = rem_msb = 0`,
                  -- so abs_r is forced via sec 14 (alternative branch).
                  -- But we used `abs_rem_alu_event = 1` (post sec 11
                  -- specialization), which contradicts rem_msb = 0 only when
                  -- r ≠ 0 — and when r = 0, ar_BV.toNat trivially equals 0.
                  clear h_abs_rem; subst ar_BV r_BV
                  simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide]
                  rw [if_neg (by omega)]
                  simp_all [U64w.toNat, U32w.toNat]
                  omega
                . -- rem_msb = 1 ⇒ r < 0 ⇒ abs_r = -r (mod 2^64).
                  simp [h_rem_one] at h_rem_neg_gadget_val h_abs_rem
                  obtain ⟨ rv0, rv1, rv2, rv3 ⟩ := h_rem_neg_gadget_val
                  simp [rv0, rv1, rv2, rv3, ← BitVec.toNat_inj] at h_abs_rem
                  -- h_abs_rem : U64w[0,0,0,0].toBV = U64w[r_0, r_1, 0xFFFF, 0xFFFF].toBV + ar_BV.toBV
                  -- → ar_BV.toBV = -U64w[r_0, r_1, 0xFFFF, 0xFFFF].toBV (mod 2^64).
                  have ar_range : ar_BV.toNat < 18446744073709551616
                    := by clear *-; subst ar_BV; simp [U64w.toNat]; omega
                  have r_range : r_BV.toNat < 4294967296
                    := by clear *-; subst r_BV; simp [U32w.toNat]; omega
                  conv at h_abs_rem => lhs; simp [U64w.toNat]
                  suffices h_eq_abs_r : ar_BV.toNat = 4294967296 - r_BV.toNat
                  . simp [h_eq_abs_r, U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
                    rw [if_pos (by subst r_BV; simp; omega)]
                    obtain ⟨ r, eq_r ⟩ : ∃ r, r = r_BV := by simp
                    rw [← eq_r] at r_range ⊢
                    clear *- r_range
                    omega
                  . clear h_r_neg_abs; symm at h_abs_rem
                    suffices h_eq :
                      U64w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0), 65535#16, 65535#16]
                        + ar_BV.toNat = 18446744073709551616
                    . subst r_BV ar_BV
                      simp [U64w.toNat, U32w.toNat] at h_eq ⊢
                      ring_nf at h_eq ⊢
                      omega
                    . subst r_BV ar_BV
                      simp [U64w.toNat] at h_abs_rem ⊢
                      ring_nf at h_abs_rem ⊢
                      omega
              -- Prove ac_BV.toNat = c_BV.toInt.natAbs.
              have eq_ac : ac_BV.toNat = c_BV.toInt.natAbs
              := by
                clear *- ub_c_0 ub_c_1 ub_c_2 ub_c_3 ub_ac_0 ub_ac_1 ub_ac_2 ub_ac_3
                         h_c_nz h_c_msb_w eq_c_2 eq_c_3 eq_c_neg_msb
                         h_abs_c h_c_neg_abs h_c_neg_gadget_val
                obtain ⟨ h_c_zero, h_pos ⟩ | ⟨ h_c_one, h_neg ⟩ := h_c_msb_w
                . -- c_msb = 0 ⇒ c ≥ 0 ⇒ abs_c = c.
                  clear h_abs_c; subst ac_BV c_BV
                  simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide]
                  rw [if_neg (by omega)]
                  simp_all [U64w.toNat, U32w.toNat]
                  omega
                . -- c_msb = 1 ⇒ c < 0 ⇒ abs_c = -c (mod 2^64).
                  simp [h_c_one] at h_c_neg_gadget_val h_abs_c
                  obtain ⟨ cv0, cv1, cv2, cv3 ⟩ := h_c_neg_gadget_val
                  simp [cv0, cv1, cv2, cv3, ← BitVec.toNat_inj] at h_abs_c
                  have ac_range : ac_BV.toNat < 18446744073709551616
                    := by clear *-; subst ac_BV; simp [U64w.toNat]; omega
                  have c_range : c_BV.toNat < 4294967296
                    := by clear *-; subst c_BV; simp [U32w.toNat]; omega
                  conv at h_abs_c => lhs; simp [U64w.toNat]
                  suffices h_eq_abs_c : ac_BV.toNat = 4294967296 - c_BV.toNat
                  . simp [h_eq_abs_c, U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
                    rw [if_pos (by subst c_BV; simp; omega)]
                    obtain ⟨ c, eq_c ⟩ : ∃ c, c = c_BV := by simp
                    rw [← eq_c] at c_range ⊢
                    clear *- c_range
                    omega
                  . clear h_c_neg_abs; symm at h_abs_c
                    suffices h_eq :
                      U64w.toNat #v[BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0), 65535#16, 65535#16]
                        + ac_BV.toNat = 18446744073709551616
                    . subst c_BV ac_BV
                      simp [U64w.toNat, U32w.toNat] at h_eq ⊢
                      ring_nf at h_eq ⊢
                      omega
                    . subst c_BV ac_BV
                      simp [U64w.toNat] at h_abs_c ⊢
                      ring_nf at h_abs_c ⊢
                      omega
              -- (f) Combine: ar.toNat < ac.toNat gives natAbs comparison.
              clear *- h_rem_check eq_ar eq_ac
              grind
            -- 3c: r_BV.toInt = 0 ∨ r_BV.toInt.sign = b_BV.toInt.sign.
            --
            -- Strategy (mirrors the 64-bit signed `h_sign` block):
            --   * Case-split on `r_BV.toBV = 0`. If r = 0, take the left
            --     disjunct.
            --   * Otherwise, case-split on `h_rem_msb_w`:
            --     - **rem_msb = 0** (r ≥ 0). With r ≠ 0, r > 0, so
            --       sign(r) = 1. We need sign(b) = 1, i.e. b > 0.
            --       From sec 11's disjunction
            --       `(r_sum + rem_msb·0xFFFF + rem_msb·0xFFFF = 0 ∨
            --         rem_msb = 1) ∨ b_msb = 0` with `rem_msb = 0` and
            --       `r ≠ 0` (so the first two disjuncts fail), we get
            --       `b_msb = 0`, i.e. b ≥ 0. We then rule out `b = 0`:
            --       if `b = 0`, `cond_1` gives `r = -q · c`, and `cond_2`
            --       `|r| < |c|` forces `|q| < 1`, so `q = 0`, hence
            --       `r = 0` — contradiction.
            --     - **rem_msb = 1** (r < 0). sign(r) = -1. From sec 11's
            --       implication `rem_msb = 1 → b_msb = 1`, b_msb = 1,
            --       so b < 0 and sign(b) = -1.
            have cond_3 :
              r_BV.toInt = 0 ∨ r_BV.toInt.sign = b_BV.toInt.sign
            := by
              by_cases h_r_zero : r_BV.toBV = 0
              . left; rw [← U32w.toBV_toInt, h_r_zero]; rfl
              right
              obtain ⟨ h_rem_zero, h_pos ⟩ | ⟨ h_rem_one, h_neg ⟩ := h_rem_msb_w
              . -- rem_msb = 0: r > 0 (r ≥ 0 from MSB + r ≠ 0).
                have h_r_pos : 0 < r_BV.toInt
                := by
                  subst r_BV; clear *- h_rem_zero h_pos h_r_zero
                  simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
                  rw [if_neg (by omega)]
                  simp [← BitVec.toNat_inj, U32w.toNat] at h_r_zero
                  omega
                -- Derive b_msb = 0 from h_constraints sec 11.
                have h_b_msb_zero : air.cols.values.b_msb.msb row 0 = 0
                := by
                  clear *- h_constraints h_rem_zero h_r_zero ub_r_0 ub_r_1 ub_r_2 ub_r_3
                  simp [h_rem_zero] at h_constraints
                  have h_r_sum_nz :
                    air.cols.values.remainder_0 row 0 + air.cols.values.remainder_1 row 0 ≠ 0
                  := by
                    clear h_constraints
                    intro h_sum; apply h_r_zero
                    simp [← BitVec.toNat_inj, U32w.toNat]
                    subst r_BV; simp; grind
                  grind
                -- Derive b ≠ 0 from cond_1 + cond_2.
                have h_b_nz : b_BV.toInt ≠ 0
                := by
                  intro h_b_zero
                  rw [h_b_zero] at cond_1
                  -- cond_1: 0 = q · c + r ⇒ r = -q · c
                  -- cond_2: |r| < |c|
                  -- h_r_pos: r > 0
                  -- Hence |q · c| < |c| ⇒ |q| < 1 (since c ≠ 0) ⇒ q = 0
                  -- Hence r = 0, contradicting h_r_pos.
                  have h_r_eq : r_BV.toInt = -(q_BV.toInt * c_BV.toInt) := by linarith
                  rw [h_r_eq] at cond_2 h_r_pos
                  simp [abs_neg, abs_mul] at cond_2
                  have h_c_pos : 0 < |c_BV.toInt|
                    := by clear *- h_c_nz; positivity
                  have h_q_zero : q_BV.toInt = 0
                  := by
                    clear h_constraints
                    by_contra h_q_nz
                    have h_q_pos : 0 < |q_BV.toInt| := by positivity
                    have h_q_ge_one : 1 ≤ |q_BV.toInt|
                      := by clear *- h_q_pos; omega
                    have : |c_BV.toInt| ≤ |q_BV.toInt| * |c_BV.toInt|
                      := by clear *- h_q_ge_one h_c_pos; nlinarith
                    clear *- h_c_pos h_q_ge_one cond_2
                    nlinarith
                  apply h_r_zero
                  rw [h_q_zero, zero_mul, neg_zero] at h_r_eq
                  simpa [← BitVec.toInt_inj]
                -- Now b_msb = 0 ⇒ b ≥ 0, plus b ≠ 0 ⇒ b > 0.
                have h_b_pos : 0 < b_BV.toInt
                := by
                  have h_b1_low : (air.cols.values.b_1 row 0).val < 32768
                  := by
                    obtain ⟨ _, h_b1 ⟩ | ⟨ h_b0, _ ⟩ := h_b_msb_w
                    . exact h_b1
                    . simp [h_b0] at h_b_msb_zero
                  have h_b_ge : 0 ≤ b_BV.toInt
                  := by
                    subst b_BV; clear *- ub_b_0 ub_b_1 h_b1_low
                    simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
                    rw [if_neg (by omega)]
                    omega
                  clear *- h_b_ge h_b_nz; omega
                rw [Int.sign_eq_one_of_pos h_r_pos, Int.sign_eq_one_of_pos h_b_pos]
              . -- rem_msb = 1: r < 0.
                have h_r_neg : r_BV.toInt < 0
                := by
                  subst r_BV; clear *- h_rem_one h_neg ub_r_0 ub_r_1
                  simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
                  rw [if_pos (by omega)]
                  omega
                -- Derive b_msb = 1 from sec 11 implication.
                have h_b_msb_one : air.cols.values.b_msb.msb row 0 = 1
                := by
                  clear *- h_constraints h_rem_one; grind
                -- b_msb = 1 ⇒ b < 0.
                have h_b_neg : b_BV.toInt < 0
                := by
                  have h_b1_high : 32768 ≤ (air.cols.values.b_1 row 0).val
                  := by
                    obtain ⟨ h_b0, _ ⟩ | ⟨ _, h_b1 ⟩ := h_b_msb_w
                    . simp [h_b0] at h_b_msb_one
                    . exact h_b1
                  subst b_BV; clear *- ub_b_0 ub_b_1 h_b1_high
                  simp [U32w.toInt, ← U32w.msb_1_negative, BitVec.msb_eq_decide, U32w.toNat]
                  rw [if_pos (by omega)]
                  omega
                rw [Int.sign_eq_neg_one_of_neg h_r_neg, Int.sign_eq_neg_one_of_neg h_b_neg]
            exact ⟨cond_1, cond_2, cond_3⟩

  -- ========================================================================
  -- spec_DIVUW_REMUW  (paired): both unsigned 32-bit W selectors at once.
  -- Result: the chip's (`quotient`, `remainder`) limbs (sign-extended to
  -- 64 bits per `q_i = quot_msb * 65535` etc.) equal the pair
  -- `execute_DIVW_REMW_pure (b.setWidth 32) (c.setWidth 32) .DRU`.
  --
  -- Proof structure mirrors `spec_DIVU_REMU` (no overflow, no sign), with
  -- three substantive changes:
  --   * Word-op branch: `is_real_not_word = 0`, so upper `MulGadget`
  --     gate doesn't fire. Only lower `MulGadget` is used, giving
  --     `cq_low = c · qc` mod 2^64 with `qc = q.setWidth 32`
  --     (zero-extended; `qc_2 = qc_3 = 0`).
  --   * `q_2 = q_3 = quot_msb · 0xFFFF`, `r_2 = r_3 = rem_msb · 0xFFFF`
  --     (sign-extension to 64 bits, even though the chip executes the
  --     unsigned variant — RISC-V semantics).
  --   * Equation lifted from the carry chain is over 32-bit:
  --     `b.setWidth 32 = q.setWidth 32 * c.setWidth 32 + r.setWidth 32`
  --     (mod 2^32), then `Nat.div_mod_unique` closes.
  -- ========================================================================

  lemma spec_DIVUW_REMUW
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_divuw_remuw :
      air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1)
  :
    ⟨ U64w.toBV #v[air.cols.values.quotient_0  row 0,
                   air.cols.values.quotient_1  row 0,
                   air.cols.values.quotient_2  row 0,
                   air.cols.values.quotient_3  row 0],
      U64w.toBV #v[air.cols.values.remainder_0 row 0,
                   air.cols.values.remainder_1 row 0,
                   air.cols.values.remainder_2 row 0,
                   air.cols.values.remainder_3 row 0] ⟩ =
    RV64IM.execute_DIVW_REMW_pure
      ((U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                     air.cols.values.b_2 row 0, air.cols.values.b_3 row 0]).setWidth 32)
      ((U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                     air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]).setWidth 32)
      .DRU
  := by
    -- Step 1: Selector cleanup. `is_divuw + is_remuw = 1` forces the other
    -- six selectors to 0 via `selector_breakdown` + the exact-one constraint.
    obtain ⟨b_div, b_divu, b_rem, b_remu, b_divw, b_remw, b_divuw, b_remuw, h_sum⟩
      := selector_breakdown air row h_constraints
    have eq_div   : air.cols.values.is_div   row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divuw_remuw; grind
    have eq_divu  : air.cols.values.is_divu  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divuw_remuw; grind
    have eq_rem   : air.cols.values.is_rem   row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divuw_remuw; grind
    have eq_remu  : air.cols.values.is_remu  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divuw_remuw; grind
    have eq_divw  : air.cols.values.is_divw  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divuw_remuw; grind
    have eq_remw  : air.cols.values.is_remw  row 0 = 0 := by clear *- b_div b_divu b_rem b_remu b_divw b_remw b_divuw b_remuw h_sum h_is_divuw_remuw; grind
    clear b_div b_divu b_rem b_remu b_divw b_remw h_sum
    -- Step 2: Move to gadget specs via `gadget_specs_pack`.
    have := gadget_specs_pack air row
    simp only [h_ext, h_wf, h_constraints, h_is_real] at this
    simp [*] at this; clear h_ext h_wf h_constraints
    obtain ⟨ h_ext, h_wf, h_constraints, gadget_specs ⟩ := this
    -- Step 3: Operand bounds on b, c from the chip's ALU bus externals
    -- (opcode 50 = DIVUW, opcode 52 = REMUW both are in `operandsInternal` —
    -- wait, MULW=48 is in operandsInternal; DIVUW=50 is NOT in operandsInternal,
    -- so externals supply the operand range).
    obtain ⟨ ub_b_0, ub_b_1, ub_b_2, ub_b_3, ub_c_0, ub_c_1, ub_c_2, ub_c_3 ⟩ :
      (air.cols.values.b_0 row 0).val < 65536 ∧ (air.cols.values.b_1 row 0).val < 65536 ∧ (air.cols.values.b_2 row 0).val < 65536 ∧ (air.cols.values.b_3 row 0).val < 65536 ∧
      (air.cols.values.c_0 row 0).val < 65536 ∧ (air.cols.values.c_1 row 0).val < 65536 ∧ (air.cols.values.c_2 row 0).val < 65536 ∧ (air.cols.values.c_3 row 0).val < 65536
    := by
      clear h_wf h_constraints gadget_specs
      simp [bus_row_ext_asm, ChipExtraBuses] at h_ext; replace h_ext := h_ext.2.2
      simp [ALUBus.externals, ALUBus.validOpcode, ALUBus.operandsInternal, ALUBus.operandRange, *] at h_ext
      apply h_ext.2 <;> clear h_ext <;> grind
    clear h_ext
    -- Step 4: u16 bounds on q, r, ac, ar via `ChipExtraBuses`' byte bus.
    obtain ⟨ ub_q_0, ub_q_1, ub_q_2, ub_q_3, ub_r_0, ub_r_1, ub_r_2, ub_r_3,
             ub_ac_0, ub_ac_1, ub_ac_2, ub_ac_3, ub_ar_0, ub_ar_1, ub_ar_2, ub_ar_3 ⟩ :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧ (air.cols.values.quotient_1 row 0).val < 65536 ∧ (air.cols.values.quotient_2 row 0).val < 65536 ∧ (air.cols.values.quotient_3 row 0).val < 65536 ∧
      (air.cols.values.remainder_0 row 0).val < 65536 ∧ (air.cols.values.remainder_1 row 0).val < 65536 ∧ (air.cols.values.remainder_2 row 0).val < 65536 ∧ (air.cols.values.remainder_3 row 0).val < 65536 ∧
      (air.cols.values.abs_c_0 row 0).val < 65536 ∧ (air.cols.values.abs_c_1 row 0).val < 65536 ∧ (air.cols.values.abs_c_2 row 0).val < 65536 ∧ (air.cols.values.abs_c_3 row 0).val < 65536 ∧
      (air.cols.values.abs_remainder_0 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_1 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_2 row 0).val < 65536 ∧ (air.cols.values.abs_remainder_3 row 0).val < 65536
    := by
      clear gadget_specs
      simp [bus_row_wf_asm, ChipExtraBuses, ByteBus.Spec, *] at h_wf
      simp [h_wf]
    -- Step 5: From `AbsConstraints_NoGadgets`, derive the W-op identities.
    -- Word-op branch fires (`is_word_operation = is_divuw + is_remuw = 1`),
    -- so:
    --   * `is_real_not_word = 0` (since `is_not_word_operation = 0`),
    --   * `qc_0 = q_0`, `qc_1 = q_1`, `qc_2 = qc_3 = 0` (unsigned word op),
    --   * `rc_0 = r_0`, `rc_1 = r_1`, `rc_2 = rc_3 = 0`,
    --   * `q_2 = q_3 = quot_msb * 0xFFFF`,
    --   * `r_2 = r_3 = rem_msb * 0xFFFF`  (sign-extend `q` / `r` from 32 to 64).
    obtain ⟨ eq_rnw, eq_qc_0, eq_qc_1, eq_qc_2, eq_qc_3,
             eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3,
             eq_b_msb_2, eq_b_msb_3, eq_c_msb_2, eq_c_msb_3,
             eq_q_msb_2, eq_q_msb_3, eq_r_msb_2, eq_r_msb_3 ⟩ :
      air.cols.values.is_real_not_word row 0 = 0 ∧
      air.cols.values.quotient_comp_0 row 0 = air.cols.values.quotient_0 row 0 ∧
      air.cols.values.quotient_comp_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.quotient_comp_2 row 0 = 0 ∧
      air.cols.values.quotient_comp_3 row 0 = 0 ∧
      air.cols.values.remainder_comp_0 row 0 = air.cols.values.remainder_0 row 0 ∧
      air.cols.values.remainder_comp_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.remainder_comp_2 row 0 = 0 ∧
      air.cols.values.remainder_comp_3 row 0 = 0 ∧
      air.cols.values.b_2 row 0 = 0 ∧
      air.cols.values.b_3 row 0 = 0 ∧
      air.cols.values.c_2 row 0 = 0 ∧
      air.cols.values.c_3 row 0 = 0 ∧
      air.cols.values.quotient_2 row 0 = air.cols.values.quot_msb.msb row 0 * 65535 ∧
      air.cols.values.quotient_3 row 0 = air.cols.values.quot_msb.msb row 0 * 65535 ∧
      air.cols.values.remainder_2 row 0 = air.cols.values.rem_msb.msb row 0 * 65535 ∧
      air.cols.values.remainder_3 row 0 = air.cols.values.rem_msb.msb row 0 * 65535
    := by
      clear gadget_specs
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      simp [h_constraints]
    -- Step 6: Stabilise gadget specs. With `is_real = 1`, the lower
    -- MulGadget thunk fires. With `is_real_not_word = 0`, the upper
    -- MulGadget, the two 64-bit `IsEqualWord` thunks (`b == INT_MIN_64`
    -- / `c == −1_64`), and the three 64-bit `U16MSB` thunks collapse
    -- to `True` and are absorbed by simp. The two 32-bit `IsEqualWord`
    -- thunks (gated by `is_word_operation = 1`) and the three 32-bit
    -- `U16MSB` thunks DO fire. The `AddGadget` × 2 and `LtWordU16`
    -- thunks remain conditional (on the respective `*_event` gates).
    simp [*] at gadget_specs
    -- Residual tuple (11 top-level slots, same arity as `spec_DIVU_REMU`
    -- but with the 64-bit `IsEqualWord` × 2 and `U16MSB` × 3 swapped for
    -- the 32-bit `IsEqualWord` × 2 and `U16MSB` × 4 — note the extra
    -- `quot_msb`-on-`q_1` thunk added by Pico PR #101). Note: `simp [*]`
    -- eagerly case-splits the U16MSB disjunctions and AndSplits the
    -- inner conjuncts, so we use `all_goals` afterwards.
    obtain ⟨ h_mul_lo,
             ⟨ b_b_overflow_w, h_b_overflow_w ⟩,
             ⟨ b_c_overflow_w, h_c_overflow_w ⟩,
             ⟨ b_c_zero, h_c_zero ⟩,
             h_abs_c, h_abs_rem, h_rem_check,
             h_b_msb_w, h_c_msb_w, h_rem_msb_w, h_quot_msb_w ⟩
      := gadget_specs
    -- Unpack `h_mul_lo : ALUBus.Spec 30 cq_low qc c` into its
    --   (cq_low range) ∧ (operand range on qc, c) ∧ (cq_low = qc · c) parts.
    simp [ALUBus.Spec] at h_mul_lo
    obtain ⟨ ⟨ ub_cq_0, ub_cq_1, ub_cq_2, ub_cq_3 ⟩, h_op_range, h_mul_lo ⟩
      := h_mul_lo
    clear h_op_range h_abs_rem h_abs_c
    -- Set up the meaning of MSBs
    set r_BV : U32w := #v[
      BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0),
      BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0)] with eq_r_BV
    set q_BV : U32w := #v[
      BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0),
      BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0)] with eq_r_BV
    have h_q_ext_t :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.quotient_2 row 0), BitVec.ofNat 16 ↑(air.cols.values.quotient_3 row 0)] =
        (q_BV.extend true).toBV
    := by
      simp [eq_q_msb_2, eq_q_msb_3]
      subst q_BV; clear *- h_quot_msb_w ub_q_1
      simp [U32w.extend, U32w.ext]; congr 3; simp
      simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
      grind
    have h_q_ext_f :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.quotient_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.quotient_1 row 0),
                   0#16, 0#16] =
        (q_BV.extend false).toBV
      := by subst q_BV; simp [U32w.extend, U32w.ext]
    have h_r_ext_t :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0),
                   BitVec.ofNat 16 ↑(air.cols.values.remainder_2 row 0), BitVec.ofNat 16 ↑(air.cols.values.remainder_3 row 0)] =
        (r_BV.extend true).toBV
    := by
      simp [eq_r_msb_2, eq_r_msb_3]
      subst r_BV; clear *- h_rem_msb_w ub_r_1
      simp [U32w.extend, U32w.ext]; congr 3; simp
      simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
      grind
    have h_r_ext_f :
      U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.remainder_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.remainder_1 row 0),
                   0#16, 0#16] =
        (r_BV.extend false).toBV
      := by subst r_BV; simp [U32w.extend, U32w.ext]
    -- Case split (driven by `IsZeroWordGadget` result on `c`):
    --   * `is_c_0 = 1`: chip says `c_0 = c_1 = c_2 = c_3 = 0`, hence
    --     `c.setWidth 32 = 0`, so the executor's `.DRU` returns
    --     `q = 0xFFFFFFFF` and `r = b.setWidth 32`.
    --   * `is_c_0 = 0`: normal unsigned word division.
    -- Case : c = 0
    obtain eq_cz | eq_cz := b_c_zero <;> simp [eq_cz] at h_c_zero; rotate_left
    . have h_eq_z : U32w.toBV #v[0#16, 0#16] = 0#32 := by clear *-; decide
      have h_eq_max : U32w.toBV #v[65535#16, 65535#16] = 4294967295#32 := by decide
      simp [AbsConstraints_NoGadgets, *] at h_constraints
      replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨ eq_q_0, eq_q_1, eq_q_msb, eq_b_0, eq_b_1 ⟩ := h_constraints
      simp [h_c_zero, eq_c_msb_2, eq_c_msb_3, h_eq_z]
      rw [h_q_ext_t, h_r_ext_t]
      simp [execute_DIVW_REMW_pure, execute_DIVW_REMW_pure_int]
      subst q_BV r_BV; rw [eq_q_0, eq_q_1, eq_b_0, eq_b_1]
      simp [U32w.extend_BitVec_extend, BitVec.extend, h_eq_max]
    . simp [h_q_ext_t, h_r_ext_t]
      set b_BV : U32w := #v[
        BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0)] with eq_b_BV
      set c_BV : U32w := #v[
        BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0),
        BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0)] with eq_c_BV
      have h_b_ext_f :
        U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.b_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.b_1 row 0),
                    0#16, 0#16] =
          (b_BV.extend false).toBV
        := by subst b_BV; simp [U32w.extend, U32w.ext]
      have h_c_ext_f :
        U64w.toBV #v[BitVec.ofNat 16 ↑(air.cols.values.c_0 row 0), BitVec.ofNat 16 ↑(air.cols.values.c_1 row 0),
                    0#16, 0#16] =
          (c_BV.extend false).toBV
        := by subst c_BV; simp [U32w.extend, U32w.ext]
      have h_c_nz : ¬ (c_BV.toBV = 0) := by
        subst c_BV; clear *- h_c_zero ub_c_0 ub_c_1
        intro h_c_bv_z; apply h_c_zero; clear h_c_zero
        simp [← BitVec.toNat_inj, U32w.toNat] at h_c_bv_z
        omega
      simp [execute_DIVW_REMW_pure, execute_DIVW_REMW_pure_int, -U32w.toBV_toNat]
      simp [U32w.extend_BitVec_extend, BitVec.extend, -U32w.toBV_toNat]
      rw [if_neg (by simp [← BitVec.toNat_inj] at h_c_nz ⊢; assumption)]
      simp [Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg, -U32w.toBV_toNat]
      suffices h_div_mod :
        b_BV.toBV.toNat / c_BV.toBV.toNat = q_BV.toBV.toNat ∧
        b_BV.toBV.toNat % c_BV.toBV.toNat = r_BV.toBV.toNat
      . clear *- h_div_mod; split_ands
        . suffices h_q : q_BV.toBV = BitVec.ofNat 32 ((b_BV.toBV.toNat : ℤ) / c_BV.toBV.toNat).toNat
          . simp [h_q]
          . simp [← BitVec.toNat_inj, -U32w.toBV_toNat, ← h_div_mod.1]
            omega
        . suffices h_r : r_BV.toBV = BitVec.ofNat 32 ((b_BV.toBV.toNat : ℤ) % c_BV.toBV.toNat).toNat
          . simp [h_r]
          . simp [← BitVec.toNat_inj, -U32w.toBV_toNat, ← h_div_mod.2]
            omega
      . simp; rw [Nat.div_mod_unique (by clear *- h_c_nz; simp [← BitVec.toNat_inj] at h_c_nz; omega), eq_comm, add_comm, mul_comm]
        have h_eqs := h_constraints
        obtain ⟨ h_rnw, h_b_neg, h_rem_neg, h_c_neg, h_eqs ⟩ := h_eqs; clear h_eqs
        have h_overflow := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp [*] at h_rnw h_b_neg h_rem_neg h_c_neg h_overflow
        have cond_b_eq_qc_plus_r : b_BV.toNat = q_BV.toNat * c_BV.toNat + r_BV.toNat
        := by
          have cond_bv :
            U64w.toBV
              #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                 0, 0] =
            U64w.toBV
                #v[air.cols.values.c_times_quotient_0 row 0,
                   air.cols.values.c_times_quotient_1 row 0,
                   air.cols.values.c_times_quotient_2 row 0,
                   air.cols.values.c_times_quotient_3 row 0] +
              U64w.toBV
                #v[air.cols.values.remainder_0 row 0, air.cols.values.remainder_1 row 0,
                   0, 0]
          := by
            replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            have carries := h_constraints.1
            simp [h_overflow, h_b_neg, h_rem_neg, eq_rc_0, eq_rc_1, eq_rc_2, eq_rc_3, eq_b_msb_2, eq_b_msb_3] at carries
            obtain ⟨ eq_cry_0, eq_cry_1, eq_cry_2, eq_cry_3, eq_cry_4, eq_cry_5, eq_cry_6, eq_cry_7 ⟩ := carries
            replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            obtain ⟨ b_cry_0, b_cry_1, b_cry_2, b_cry_3, b_cry_4, b_cry_5, b_cry_6, b_cry_7, rest ⟩ := h_constraints; clear rest
            simp [sub_eq_zero] at b_cry_0 b_cry_1 b_cry_2 b_cry_3 b_cry_4 b_cry_5 b_cry_6 b_cry_7
            have cond_bv :=
              FKB_add_64 (a2 := 0) (a3 := 0) (c2 := 0) (c3 := 0)
                ub_b_0 ub_b_1 (by simp) (by simp)
                ub_cq_0 ub_cq_1 ub_cq_2 ub_cq_3
                ub_r_0 ub_r_1 (by simp) (by simp)
                (by clear *- eq_cry_0; omega) (by clear *- eq_cry_1; omega) (by clear *- eq_cry_2; omega) (by clear *- eq_cry_3; omega)
                b_cry_0 b_cry_1 b_cry_2 b_cry_3
            simp at cond_bv; exact cond_bv
          simp [h_b_ext_f, h_r_ext_f, ← BitVec.toNat_inj] at cond_bv
          simp [cond_bv]; clear cond_bv
          simp [execute_MUL_pure, ← BitVec.toNat_inj] at h_mul_lo
          rw [← U64w.extend_BitVec_extend, U128w.toBV_toNat, U64w.extend_toNat] at h_mul_lo
          rw [← U64w.extend_BitVec_extend, U128w.toBV_toNat, U64w.extend_toNat] at h_mul_lo
          rw [← U64w.toBV_toNat, ← U64w.toBV_toNat, ← U64w.toBV_toNat] at h_mul_lo
          simp [h_c_ext_f, h_q_ext_f, -U64w.toBV_toNat] at h_mul_lo
          simp at h_mul_lo
          simp [h_mul_lo]
          have ub_q : q_BV.toNat < 4294967296 := by clear *-; simp [U32w.toNat]; omega
          have ub_c : c_BV.toNat < 4294967296 := by clear *-; simp [U32w.toNat]; omega
          have ub_r : r_BV.toNat < 4294967296 := by clear *-; simp [U32w.toNat]; omega
          clear *- ub_q ub_c ub_r; nlinarith
        have cond_lt : r_BV.toNat < c_BV.toNat
        := by
          replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          simp [*] at h_constraints
          obtain ⟨ eq_abs_c, eq_abs_rem, eq_m_0, eq_m_1, eq_m_2, eq_m_3, eq_rem_check, h_constraints ⟩ := h_constraints
          replace h_constraints := h_constraints.2.2.2.2.1
          simp [eq_rem_check] at h_constraints
          simp [*] at h_rem_check
          clear *- h_rem_check h_rem_msb_w h_r_ext_f h_c_ext_f
          obtain h_rem_msb_w | h_rem_msb_w := h_rem_msb_w <;> simp [h_rem_msb_w] at h_rem_check
          . rw [← U64w.toBV_toNat, ← U64w.toBV_toNat, h_r_ext_f, h_c_ext_f] at h_rem_check
            simp at h_rem_check; exact h_rem_check
          . exfalso; clear *- h_rem_check
            simp [U64w.toNat] at h_rem_check
            omega
        clear *- cond_b_eq_qc_plus_r cond_lt
        grind

  -- ========================================================================
  -- spec_DIV  (ALU opcode 34): signed 64-bit quotient. One-line projection
  -- from `spec_DIV_REM` via `a = quotient` (the `div_active = 1` branch
  -- of `AbsConstraints` section 10).
  -- ========================================================================

  lemma spec_DIV
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_is_div  : air.cols.values.is_div  row 0 = 1)
  :
    ALUBus.Spec 34
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_divu, eq_rem, eq_remu, eq_divw, eq_remw, eq_divuw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).1 h_is_div
    have h_is_div_rem :
      air.cols.values.is_div row 0 + air.cols.values.is_rem row 0 = 1
      := by rw [h_is_div, eq_rem]; ring
    have h_pair := @spec_DIV_REM _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_div_rem] at h_pair
    have h_aq :
      air.cols.values.a_0 row 0 = air.cols.values.quotient_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.quotient_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.quotient_3 row 0
    := by
      simp [AbsConstraints, h_is_div, eq_divu, eq_rem, eq_remu, eq_divw,
            eq_remw, eq_divuw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; aesop
    have h_q_range :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧
      (air.cols.values.quotient_1 row 0).val < 65536 ∧
      (air.cols.values.quotient_2 row 0).val < 65536 ∧
      (air.cols.values.quotient_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_div, eq_divu, eq_rem,
            eq_remu, eq_divw, eq_remw, eq_divuw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_REM  (ALU opcode 36): signed 64-bit remainder. One-line projection
  -- from `spec_DIV_REM` via `a = remainder` (the `rem_active = 1` branch
  -- of `AbsConstraints` section 10).
  -- ========================================================================

  lemma spec_REM
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_is_rem  : air.cols.values.is_rem  row 0 = 1)
  :
    ALUBus.Spec 36
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_divu, eq_remu, eq_divw, eq_remw, eq_divuw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).2.2.1 h_is_rem
    have h_is_div_rem :
      air.cols.values.is_div row 0 + air.cols.values.is_rem row 0 = 1
      := by rw [h_is_rem, eq_div]; ring
    have h_pair := @spec_DIV_REM _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_div_rem] at h_pair
    have h_ar :
      air.cols.values.a_0 row 0 = air.cols.values.remainder_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.remainder_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.remainder_3 row 0
    := by
      simp [AbsConstraints, h_is_rem, eq_div, eq_divu, eq_remu, eq_divw,
            eq_remw, eq_divuw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; aesop
    have h_r_range :
      (air.cols.values.remainder_0 row 0).val < 65536 ∧
      (air.cols.values.remainder_1 row 0).val < 65536 ∧
      (air.cols.values.remainder_2 row 0).val < 65536 ∧
      (air.cols.values.remainder_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_rem, eq_div, eq_divu,
            eq_remu, eq_divw, eq_remw, eq_divuw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_DIVU  (ALU opcode 35): unsigned 64-bit quotient. One-line
  -- projection from `spec_DIVU_REMU` via `a = quotient` (the
  -- `div_active = 1` branch of `AbsConstraints` section 10).
  -- ========================================================================

  lemma spec_DIVU
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_is_divu : air.cols.values.is_divu row 0 = 1)
  :
    ALUBus.Spec 35
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_rem, eq_remu, eq_divw, eq_remw, eq_divuw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).2.1 h_is_divu
    have h_is_divu_remu :
      air.cols.values.is_divu row 0 + air.cols.values.is_remu row 0 = 1
      := by rw [h_is_divu, eq_remu]; ring
    have h_pair := @spec_DIVU_REMU _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_divu_remu] at h_pair
    have h_aq :
      air.cols.values.a_0 row 0 = air.cols.values.quotient_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.quotient_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.quotient_3 row 0
    := by
      simp [AbsConstraints, h_is_divu, eq_div, eq_rem, eq_remu, eq_divw,
            eq_remw, eq_divuw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; aesop
    have h_q_range :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧
      (air.cols.values.quotient_1 row 0).val < 65536 ∧
      (air.cols.values.quotient_2 row 0).val < 65536 ∧
      (air.cols.values.quotient_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_divu, eq_div, eq_rem,
            eq_remu, eq_divw, eq_remw, eq_divuw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_REMU  (ALU opcode 37): unsigned 64-bit remainder. One-line
  -- projection from `spec_DIVU_REMU` via `a = remainder` (the
  -- `rem_active = 1` branch of `AbsConstraints` section 10).
  -- ========================================================================

  lemma spec_REMU
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_is_remu : air.cols.values.is_remu row 0 = 1)
  :
    ALUBus.Spec 37
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_divu, eq_rem, eq_divw, eq_remw, eq_divuw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).2.2.2.1 h_is_remu
    have h_is_divu_remu :
      air.cols.values.is_divu row 0 + air.cols.values.is_remu row 0 = 1
      := by rw [h_is_remu, eq_divu]; ring
    have h_pair := @spec_DIVU_REMU _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_divu_remu] at h_pair
    have h_ar :
      air.cols.values.a_0 row 0 = air.cols.values.remainder_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.remainder_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.remainder_3 row 0
    := by
      simp [AbsConstraints, h_is_remu, eq_div, eq_divu, eq_rem, eq_divw,
            eq_remw, eq_divuw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; aesop
    have h_r_range :
      (air.cols.values.remainder_0 row 0).val < 65536 ∧
      (air.cols.values.remainder_1 row 0).val < 65536 ∧
      (air.cols.values.remainder_2 row 0).val < 65536 ∧
      (air.cols.values.remainder_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_remu, eq_div, eq_divu,
            eq_rem, eq_divw, eq_remw, eq_divuw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_DIVW  (ALU opcode 49): signed 32-bit quotient, sign-extended to
  -- 64 bits. One-line projection from `spec_DIVW_REMW` via
  -- `a = quotient` (the `div_active = 1` branch of `AbsConstraints`
  -- section 10).
  -- ========================================================================

  lemma spec_DIVW
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_is_divw : air.cols.values.is_divw row 0 = 1)
  :
    ALUBus.Spec 49
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_divu, eq_rem, eq_remu, eq_remw, eq_divuw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).2.2.2.2.1 h_is_divw
    have h_is_divw_remw :
      air.cols.values.is_divw row 0 + air.cols.values.is_remw row 0 = 1
      := by rw [h_is_divw, eq_remw]; ring
    have h_pair := @spec_DIVW_REMW _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_divw_remw] at h_pair
    have h_aq :
      air.cols.values.a_0 row 0 = air.cols.values.quotient_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.quotient_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.quotient_3 row 0
    := by
      simp [AbsConstraints, h_is_divw, eq_div, eq_divu, eq_rem, eq_remu, eq_remw,
            eq_divuw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; aesop
    have h_q_range :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧
      (air.cols.values.quotient_1 row 0).val < 65536 ∧
      (air.cols.values.quotient_2 row 0).val < 65536 ∧
      (air.cols.values.quotient_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_divw, eq_div, eq_divu, eq_rem,
            eq_remu, eq_remw, eq_divuw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_REMW  (ALU opcode 51): signed 32-bit remainder, sign-extended to
  -- 64 bits. One-line projection from `spec_DIVW_REMW` via
  -- `a = remainder` (the `rem_active = 1` branch of `AbsConstraints`
  -- section 10).
  -- ========================================================================

  lemma spec_REMW
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_is_remw : air.cols.values.is_remw row 0 = 1)
  :
    ALUBus.Spec 51
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_divu, eq_rem, eq_remu, eq_divw, eq_divuw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).2.2.2.2.2.1 h_is_remw
    have h_is_divw_remw :
      air.cols.values.is_divw row 0 + air.cols.values.is_remw row 0 = 1
      := by rw [h_is_remw, eq_divw]; ring
    have h_pair := @spec_DIVW_REMW _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_divw_remw] at h_pair
    have h_ar :
      air.cols.values.a_0 row 0 = air.cols.values.remainder_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.remainder_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.remainder_3 row 0
    := by
      simp [AbsConstraints, h_is_remw, eq_div, eq_divu, eq_rem, eq_remu, eq_divw,
            eq_divuw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; aesop
    have h_r_range :
      (air.cols.values.remainder_0 row 0).val < 65536 ∧
      (air.cols.values.remainder_1 row 0).val < 65536 ∧
      (air.cols.values.remainder_2 row 0).val < 65536 ∧
      (air.cols.values.remainder_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_remw, eq_div, eq_divu, eq_rem,
            eq_remu, eq_divw, eq_divuw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_DIVUW  (ALU opcode 50): unsigned 32-bit quotient, sign-extended
  -- to 64 bits (RV64 ISA convention). One-line projection from
  -- `spec_DIVUW_REMUW` via `a = quotient` (the `div_active = 1` branch
  -- of `AbsConstraints` section 10).
  -- ========================================================================

  lemma spec_DIVUW
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real  : air.cols.values.is_real  row 0 = 1)
    (h_is_divuw : air.cols.values.is_divuw row 0 = 1)
  :
    ALUBus.Spec 50
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_divu, eq_rem, eq_remu, eq_divw, eq_remw, eq_remuw⟩
      := (selector_exclusivity air row h_constraints).2.2.2.2.2.2.1 h_is_divuw
    have h_is_divuw_remuw :
      air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1
      := by rw [h_is_divuw, eq_remuw]; ring
    have h_pair := @spec_DIVUW_REMUW _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_divuw_remuw] at h_pair
    have h_aq :
      air.cols.values.a_0 row 0 = air.cols.values.quotient_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.quotient_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.quotient_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.quotient_3 row 0
    := by
      simp [AbsConstraints, h_is_divuw, eq_div, eq_divu, eq_rem, eq_remu, eq_divw,
            eq_remw, eq_remuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; grind
    have h_q_range :
      (air.cols.values.quotient_0 row 0).val < 65536 ∧
      (air.cols.values.quotient_1 row 0).val < 65536 ∧
      (air.cols.values.quotient_2 row 0).val < 65536 ∧
      (air.cols.values.quotient_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_divuw, eq_div, eq_divu, eq_rem,
            eq_remu, eq_divw, eq_remw, eq_remuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  -- ========================================================================
  -- spec_REMUW  (ALU opcode 52): unsigned 32-bit remainder, sign-extended
  -- to 64 bits (RV64 ISA convention). One-line projection from
  -- `spec_DIVUW_REMUW` via `a = remainder` (the `rem_active = 1` branch
  -- of `AbsConstraints` section 10).
  -- ========================================================================

  lemma spec_REMUW
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
    (h_is_real  : air.cols.values.is_real  row 0 = 1)
    (h_is_remuw : air.cols.values.is_remuw row 0 = 1)
  :
    ALUBus.Spec 52
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨eq_div, eq_divu, eq_rem, eq_remu, eq_divw, eq_remw, eq_divuw⟩
      := (selector_exclusivity air row h_constraints).2.2.2.2.2.2.2 h_is_remuw
    have h_is_divuw_remuw :
      air.cols.values.is_divuw row 0 + air.cols.values.is_remuw row 0 = 1
      := by rw [h_is_remuw, eq_divuw]; ring
    have h_pair := @spec_DIVUW_REMUW _ _ air row h_is_real
    set ext := bus_row_ext_asm (bus_row air row)
    set wf := bus_row_wf_asm (bus_row air row)
    simp [h_ext, h_wf, h_constraints, h_is_divuw_remuw] at h_pair
    have h_ar :
      air.cols.values.a_0 row 0 = air.cols.values.remainder_0 row 0 ∧
      air.cols.values.a_1 row 0 = air.cols.values.remainder_1 row 0 ∧
      air.cols.values.a_2 row 0 = air.cols.values.remainder_2 row 0 ∧
      air.cols.values.a_3 row 0 = air.cols.values.remainder_3 row 0
    := by
      simp [AbsConstraints, h_is_remuw, eq_div, eq_divu, eq_rem, eq_remu, eq_divw,
            eq_remw, eq_divuw, sub_eq_zero] at h_constraints
      clear *- h_constraints; grind
    have h_r_range :
      (air.cols.values.remainder_0 row 0).val < 65536 ∧
      (air.cols.values.remainder_1 row 0).val < 65536 ∧
      (air.cols.values.remainder_2 row 0).val < 65536 ∧
      (air.cols.values.remainder_3 row 0).val < 65536
    := by
      subst wf
      simp [bus_row, AbsBuses, ChipExtraBuses, bus_row_wf_asm,
            ByteBus.Spec, h_is_real, h_is_remuw, eq_div, eq_divu, eq_rem,
            eq_remu, eq_divw, eq_remw, eq_divuw]
        at h_wf
      clear *- h_wf; aesop
    simp [ALUBus.Spec]
    grind

  --
  -- Externals
  --

  -- =====================================================================
  -- Externality assertions for the DivRemChip bus row.
  -- The chip emits sub-gadget byte/ALU entries (MulGadget × 2,
  -- AddGadget × 2, LtWordU16Gadget, U16MSBGadget × 6, plus
  -- IsZeroWord/IsEqualWord internals) along with three chip-own
  -- ALU events: two looking ADD entries (multiplicities
  -- `-abs_c_alu_event`, `-abs_rem_alu_event` ∈ {0, -1}) and one
  -- looked entry for the selector-encoded DIV/REM opcode
  -- (multiplicity `is_real`). Byte bus has no externals; the looking
  -- ADDs have no externality obligation (`ADD ∈ ALUBus.validOpcode`,
  -- not in `ALUBus.operandsInternal` — but operand-range is
  -- discharged from the chip's own u16 slice checks via the
  -- `MulGadget.Spec`-supplied range facts). The looked DIV/REM ALU
  -- opcode `is_div·34 + is_divu·35 + … + is_remuw·52` lies in
  -- `Finset.Icc 30 37 ∪ Finset.Icc 48 52 ⊆ ALUBus.operandsInternal`,
  -- so it has no operand-range obligation either.
  -- =====================================================================

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    -- h_ext separation
    simp [AbsBuses, and_assoc] at h_ext
    replace h_ext := h_ext.1
    -- h_wf separation
    simp [AbsBuses] at h_wf; have h_rest := h_wf.2
    simp [bus_row_wf_asm, ChipExtraBuses, ByteBus.Spec, h_is_real] at h_rest
    simp [and_assoc] at h_wf; replace h_wf := h_wf.1
    -- constraints separation
    simp [AbsConstraints] at h_constraints
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have mul_spec :=
      MulGadget.Spec.gadget_spec
        (h_gadget_ext_asm := h_ext)
        (h_gadget_wf_asm := h_wf)
        (h_gadget_constraints := h_constraints)
    clear h_ext h_wf h_constraints
    simp [h_is_real, ALUBus.Spec, ALUBus.operandRange] at mul_spec
    -- Simplify_goal
    simp [
      AbsBuses,
      AddGadget.AbsBuses,
      LtWordU16Gadget.AbsBuses,
      MulGadget.AbsBuses,
      U16MSBGadget.AbsBuses,
      U16ToU8GadgetSafe.AbsBuses
    ]
    simp [bus_row_ext_asrt, ChipExtraBuses, h_is_real]
    split_ands <;> intro h_alu <;>
      simp [
        ALUBus.externals,
        ALUBus.validOpcode,
        ALUBus.operandsInternal,
        ALUBus.operandRange,
        *
      ]

  --
  -- Well-formedness — every vacuously-gated bus entry is discharged
  -- by refuting `x = -1` for boolean `x`; the single live ALU
  -- emission is dispatched to the active `spec_*` projection.
  --

  -- =====================================================================
  -- Every looking bus entry has a binary selector (or a sum of booleans)
  -- as multiplicity, so its `wf_assert_cond` (multiplicity = -1) is
  -- unsatisfiable in FKB: `0` and `1` are not `-1 = KB_prime - 1`. The
  -- `h_neg_*` auxiliaries discharge the distinct shapes:
  --   * `abs_c_alu_event = -1` (`c_neg_gadget` ALU + 4 byte buses)
  --   * `abs_rem_alu_event = -1` (`rem_neg_gadget` ALU + 4 byte buses)
  --   * `is_real_not_word = -1` (the `c_times_quotient_upper`
  --     MulGadget block ≈ 30 byte buses, plus 3 top-limb U16MSB buses)
  --   * `remainder_check_multiplicity = -1` (`remainder_lt_gadget`
  --     byte-range check); derived via the defining equation
  --     `rcm = (1 - is_c_0_result) · is_real` and IsZeroWordGadget's
  --     `result ∈ {0, 1}` constraint
  -- The 4 W-variant U16MSB byte buses (multiplicity a sum of W selectors)
  -- are discharged by `simp` from the selector facts.
  -- The single non-vacuous entry is the chip's served ALU emission,
  -- multiplicity `-is_real`; when active, the exact-one selector
  -- constraint pins one of the eight selectors to `1` and we dispatch to
  -- the matching `spec_DIV` / … / `spec_REMUW`.
  -- =====================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_DivRemChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AbsConstraints air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    simp [bus_row_wf_asrt, AbsBuses]
    obtain ⟨h_div_b, h_divu_b, h_rem_b, h_remu_b,
            h_divw_b, h_remw_b, h_divuw_b, h_remuw_b, h_sum⟩ :=
      selector_breakdown air row h_constraints
    obtain ⟨h_excl_div, h_excl_divu, h_excl_rem, h_excl_remu,
            h_excl_divw, h_excl_remw, h_excl_divuw, h_excl_remuw⟩ :=
      selector_exclusivity air row h_constraints
    simp [ChipExtraBuses, MulGadget.AbsBuses,
          AddGadget.AbsBuses, LtWordU16Gadget.AbsBuses,
          U16MSBGadget.AbsBuses, U16ToU8GadgetSafe.AbsBuses,
          h_is_real]
    -- =================================================================
    -- Vacuous-LHS auxiliaries. Every conjunct of the form `x = -1 → …`
    -- where `x` is a boolean collapses to `True` because the premise is
    -- unsatisfiable in FKB (neither `0` nor `1` equals `-1 = KB_prime - 1`).
    -- We carve out one helper per distinct LHS shape.
    -- =================================================================
    have h_abs_c_b :
        air.cols.values.abs_c_alu_event row 0 = 0 ∨
        air.cols.values.abs_c_alu_event row 0 = 1 := by
      have := h_constraints
      simp [AbsConstraints, sub_eq_zero] at this
      clear *- this; aesop
    have h_neg_abs_c :
        air.cols.values.abs_c_alu_event row 0 ≠ (-1 : FKB) := by
      rcases h_abs_c_b with h | h <;> rw [h] <;> decide
    have h_abs_rem_b :
        air.cols.values.abs_rem_alu_event row 0 = 0 ∨
        air.cols.values.abs_rem_alu_event row 0 = 1 := by
      have := h_constraints
      simp [AbsConstraints, sub_eq_zero] at this
      clear *- this; aesop
    have h_neg_abs_rem :
        air.cols.values.abs_rem_alu_event row 0 ≠ (-1 : FKB) := by
      rcases h_abs_rem_b with h | h <;> rw [h] <;> decide
    have h_irnw_b :
        air.cols.values.is_real_not_word row 0 = 0 ∨
        air.cols.values.is_real_not_word row 0 = 1 := by
      have := h_constraints
      simp [AbsConstraints, sub_eq_zero] at this
      clear *- this; aesop
    have h_neg_irnw :
        air.cols.values.is_real_not_word row 0 ≠ (-1 : FKB) := by
      rcases h_irnw_b with h | h <;> rw [h] <;> decide
    -- `remainder_check_multiplicity = (1 - is_c_0_result) · is_real`
    -- (constraint 16). With `is_real = 1`, this gives `rcm = 1 - is_c_0`,
    -- so `rcm ∈ {0, 1}` cannot equal `-1` in FKB.
    have h_rcm_eq :
        air.cols.values.remainder_check_multiplicity row 0
        = (1 - air.cols.values.is_c_0.result row 0)
            * air.cols.values.is_real row 0 := by
      have := h_constraints
      simp [AbsConstraints, sub_eq_zero] at this
      clear *- this; aesop
    have h_is_c_0_b :
        air.cols.values.is_c_0.result row 0 = 0 ∨
        air.cols.values.is_c_0.result row 0 = 1 := by
      have := h_constraints
      simp [AbsConstraints, IsZeroWordGadget.AbsConstraints, h_is_real,
            sub_eq_zero, mul_eq_zero] at this
      clear *- this; aesop
    have h_neg_rcm :
        air.cols.values.remainder_check_multiplicity row 0 ≠ (-1 : FKB) := by
      rw [h_rcm_eq, h_is_real]
      rcases h_is_c_0_b with h | h <;> rw [h] <;> decide
    simp [h_neg_abs_c, h_neg_abs_rem, h_neg_irnw, h_neg_rcm]
    -- =================================================================
    -- Eight-way dispatch on which selector is `1`. At each leaf the
    -- opcode formula collapses to a literal and we apply the matching
    -- `spec_X` projection.
    -- =================================================================
    rcases h_div_b with h_div | h_div
    rotate_left
    . -- is_div = 1 → opcode 34, apply spec_DIV
      obtain ⟨h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw⟩ :=
        h_excl_div h_div
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_DIV air row <;> grind
    rcases h_divu_b with h_divu | h_divu
    rotate_left
    . -- is_divu = 1 → opcode 35, apply spec_DIVU
      obtain ⟨_, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw⟩ :=
        h_excl_divu h_divu
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_DIVU air row <;> grind
    rcases h_rem_b with h_rem | h_rem
    rotate_left
    . -- is_rem = 1 → opcode 36, apply spec_REM
      obtain ⟨_, _, h_remu, h_divw, h_remw, h_divuw, h_remuw⟩ :=
        h_excl_rem h_rem
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_REM air row <;> grind
    rcases h_remu_b with h_remu | h_remu
    rotate_left
    . -- is_remu = 1 → opcode 37, apply spec_REMU
      obtain ⟨_, _, _, h_divw, h_remw, h_divuw, h_remuw⟩ :=
        h_excl_remu h_remu
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_REMU air row <;> grind
    rcases h_divw_b with h_divw | h_divw
    rotate_left
    . -- is_divw = 1 → opcode 49, apply spec_DIVW
      obtain ⟨_, _, _, _, h_remw, h_divuw, h_remuw⟩ :=
        h_excl_divw h_divw
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_DIVW air row <;> grind
    rcases h_remw_b with h_remw | h_remw
    rotate_left
    . -- is_remw = 1 → opcode 51, apply spec_REMW
      obtain ⟨_, _, _, _, _, h_divuw, h_remuw⟩ :=
        h_excl_remw h_remw
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_REMW air row <;> grind
    rcases h_divuw_b with h_divuw | h_divuw
    rotate_left
    . -- is_divuw = 1 → opcode 50, apply spec_DIVUW
      obtain ⟨_, _, _, _, _, _, h_remuw⟩ :=
        h_excl_divuw h_divuw
      simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
      apply spec_DIVUW air row <;> grind
    -- All seven previous selectors are 0; h_sum forces is_remuw = 1.
    have h_remuw : air.cols.values.is_remuw row 0 = 1 := by
      have := h_sum
      rw [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw] at this
      simpa using this
    simp [h_div, h_divu, h_rem, h_remu, h_divw, h_remw, h_divuw, h_remuw]
    apply spec_REMUW air row <;> grind


end DivRemChip.Spec
