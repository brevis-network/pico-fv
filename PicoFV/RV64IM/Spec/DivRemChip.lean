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
| `is_divuw = 1`  | 50     | unsigned 32-bit quotient,  zero-extended to 64        |
| `is_remw = 1`   | 51     | signed   32-bit remainder, sign-extended to 64        |
| `is_remuw = 1`  | 52     | unsigned 32-bit remainder, zero-extended to 64        |

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
        `remainder_lt_gadget.bit = 1` which is **not enforced by
        Pico's constraints** (one `sorry`, fixed by adding
        `builder.when(rem_check_mult).assert_one(bit)` to Pico Rust).
        The bridge between `ar.toNat`/`ac.toNat` and `|r|.natAbs`/
        `|c|.natAbs` goes through `U64w.msb_3_negative` +
        constraint-13 abs-value identities.
     c. **`sign(r) = sign(b) ∨ r = 0`** — by-cases on `r = 0`; else
        `Int.split_nzp` (3-way `< 0 / = 0 / > 0`) + sign-consistency
        constraints + the algebraic equation to rule out `b = 0`
        when `r ≠ 0`.

Each individual `spec_DIV` / `spec_REM` is a one-line projection from
`spec_DIV_REM` (still `sorry`). The unsigned (`spec_DIVU_REMU`) and
W-window (`spec_DIVW_REMW`, `spec_DIVUW_REMUW`) groupings will follow
the same shape but with simpler case splits (no overflow for unsigned,
`U64w.extend false`/`true` + `BitVec.setWidth 32` bridges for word
variants).

**Status:** `spec_DIV_REM` proven modulo the `bit = 1` sorry; other
spec_* lemmas still scaffolded with `sorry`.
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
    --   * `is_c_0 = 0`: normal unsigned word division (deferred).
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
  -- spec_DIVW_REMW  (paired): both signed 32-bit W selectors at once.
  --
  -- Returns the chip's `(quotient, remainder)` as the 64-bit lift of
  -- `RV64IM.execute_DIVW_REMW_pure` on the low 32 bits of `b` and `c`
  -- with the **signed** word mode `.DRS`. The chip stores the 32-bit
  -- result in `quotient_0 / quotient_1` (resp. `remainder_0 /
  -- remainder_1`), with `quotient_2 = quotient_3 = quot_msb · 0xFFFF`
  -- and `remainder_2 = remainder_3 = rem_msb · 0xFFFF` providing the
  -- 32→64 sign-extension via the `U16MSBGadget`s on `q_1` and `r_1`
  -- (added in PR #101 commits `ddd0d96` and `f35b17d` /
  -- `b6f2de0`).
  --
  -- Statement-only for now; the proof mirrors `spec_DIVUW_REMUW` but
  -- with non-trivial sign handling (b_neg, rem_neg, c_neg, INT_MIN/-1
  -- overflow clamp).
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
    sorry

  -- ========================================================================
  -- spec_DIV  (ALU opcode 34): signed 64-bit quotient.
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
  -- spec_REM  (ALU opcode 36): signed 64-bit remainder.
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
  -- spec_DIVU  (ALU opcode 35): unsigned 64-bit quotient.
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
  -- spec_REMU  (ALU opcode 37): unsigned 64-bit remainder.
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
  -- spec_DIVW  (ALU opcode 49): signed 32-bit quotient, sign-extended.
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
  -- spec_REMW  (ALU opcode 51): signed 32-bit remainder, sign-extended.
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
  -- spec_DIVUW  (ALU opcode 50): unsigned 32-bit quotient, zero-extended.
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
  -- spec_REMUW  (ALU opcode 52): unsigned 32-bit remainder, zero-extended.
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
  -- Well-formedness — dispatches to the active `spec_*` for the main
  -- ALU entry; sub-gadget bus entries discharged via their own specs
  --

  -- =====================================================================
  -- All ByteBus entries have multiplicity `-is_real` (or `-is_mulw`,
  -- `-abs_c_alu_event`, `-abs_rem_alu_event`) ∈ {0, -1}, never
  -- triggering `wf_assert_cond`. The two `looking_alu(ADD)` entries
  -- for the abs-value sub-events have multiplicities
  -- `-abs_c_alu_event` / `-abs_rem_alu_event` ∈ {0, -1}, also vacuous.
  -- The single looked ALU entry has multiplicity `is_real ∈ {0, 1}`;
  -- when `is_real = 1` exactly one of the eight selectors is `1`
  -- (`selector_breakdown` + the exact-one constraint) and we dispatch
  -- to the matching `spec_DIV` / `spec_DIVU` / … / `spec_REMUW`.
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
    sorry

end DivRemChip.Spec
