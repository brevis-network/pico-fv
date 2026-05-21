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

  -- ========================================================================
  -- spec_DIV_REM  (paired): both signed 64-bit selectors at once.
  -- Result: the chip's `quotient` / `remainder` columns are the
  -- (`Int.tdiv`, `Int.tmod`) of `b` / `c` (RV64 signed semantics, with
  -- the divide-by-zero and overflow special cases handled by Pico's
  -- `execute_DIV_REM_pure_int .DRS`).
  --
  -- Proof skeleton (see file-header for context):
  --   step 1: selector cleanup via `selector_breakdown` + 6 grind calls
  --   step 2: `gadget_specs_pack` → chip-only ext/wf + NoGadgets + 11
  --           gadget-spec thunks
  --   step 3: range extraction from `ChipExtraBuses` ext (ALU externals)
  --           and wf (ByteBus.Spec U16Range)
  --   step 4: `is_real_not_word = 1`, `*_comp = *` from NoGadgets
  --   step 5: `combine_MUL_MULH` on the two `ALUBus.Spec` MUL outputs
  --   step 6: case-split c == 0 / overflow / normal
  --           - normal case: `Int.tdiv_tmod_unique_full` with
  --             `FKB_add_128` for the equation, `LtWordU16Gadget` for
  --             the magnitude bound (one `sorry` — Pico missing
  --             `assert_one(bit)`; see [[divrem_bit1_soundness_gap]]),
  --             and sign-consistency for the sign condition.
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
      have h_overflow := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.1
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
            replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
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
          have relevant_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
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
          have relevant_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
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
    sorry

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
    sorry

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
    sorry

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
    -- Same shape as spec_DIVU, projection to the remainder component.
    sorry

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
    sorry

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
    sorry

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
    sorry

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
    sorry

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
    simp [bus_row_wf_asm, ByteBus.Spec, h_is_real] at h_rest
    simp [and_assoc] at h_wf; replace h_wf := h_wf.1
    -- constraints separation
    simp [AbsConstraints] at h_constraints
    replace h_constraints := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
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
    simp [bus_row_ext_asrt, h_is_real]
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
    sorry

end DivRemChip.Spec
