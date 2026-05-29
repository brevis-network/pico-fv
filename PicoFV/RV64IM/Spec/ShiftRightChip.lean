import PicoFV.RV64IM.Constraints.ShiftRightChip
import PicoFV.RV64IM.Spec.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# ShiftRightChip — semantic specification

Four ALU outputs handled (vs two for SLLChip):

- `spec_SRL`  (opcode 6):  64-bit logical right shift, shift = low 6 bits of `c_for_lookup`.
- `spec_SRA`  (opcode 7):  64-bit arithmetic right shift (sign-extends MSB).
- `spec_SRLW` (opcode 43): 32-bit logical right shift, then sign-extend to 64.
- `spec_SRAW` (opcode 44): 32-bit arithmetic right shift, then sign-extend to 64.

## Soundness gaps (two missing constraints in Pico)

Two assumptions are added per `spec_S*` to bridge holes in the chip
(see `memory/shiftright_bdecomp_soundness_gap.md`):

1. **`MISSING_b_decomp_i`** — `b_i = higher_limb_i · 2^s4 + lower_limb_i`
   for each `i ∈ {0..3}`. Pico's SR chip range-checks
   `(lower_limb_i, higher_limb_i)` but does **not** tie them to `b_i`.
   In SLLChip the analogous identity is enforced by per-limb carry
   constraints (`b_i · v_0123 = higher_limb_i · 65536 + lower_limb_i · v_0123`);
   SR has no such constraint.

2. **`MISSING_c_eq`** — `c = c_for_lookup_0` (in FKB).  The chip uses two
   separate columns: `c` (column 20) drives the byte-bus s5 decomposition
   into `c_bits_0..5`, while `c_for_lookup` (columns 8..11) is broadcast
   on the ALU bus.  Pico's SR chip has no `assert_eq(c, c_for_lookup[0])`.
   In SLLChip the operand 2 is `c_0..c_3` directly (one column reused for
   both roles), so this gap doesn't arise there.

Both assumptions become provable from the chip constraints once Pico
adds the missing equalities, at which point they can be removed.
-/

namespace ShiftRightChip.Spec

  open RV64IM_Interactions
  open ShiftRightChip.ConstraintsAndBuses
  open ShiftRightChip.Interactions
  open ShiftRightChip.Interpretations
  open LeanRV64D.Functions

  set_option maxHeartbeats 4_000_000_000

  -- =====================================================================
  -- `v_0123` cascade for SR: when `c_bits_0..3` are booleans,
  -- `v_0123 = 2^(16 - k_nat)` where `k_nat = c0.val + 2 c1.val + 4 c2.val + 8 c3.val`.
  -- The cascade is `v_01 = ((1-c0)+1)·2 · ((1-c1)·3+1) = 2^(3 - c0 - 2·c1)`,
  -- and `v_0123 = 2^(16 - k_nat)`.
  -- =====================================================================
  private lemma v0123_pow_inv
      (c0 c1 c2 c3 v01 v012 v0123 : FKB)
      (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1)
      (hc2 : c2 = 0 ∨ c2 = 1) (hc3 : c3 = 0 ∨ c3 = 1)
      (h_v01  : v01   = ((1 - c0) + 1) * 2 * ((1 - c1) * 3 + 1))
      (h_v012 : v012  = v01 * ((1 - c2) * 15 + 1))
      (h_v0123: v0123 = v012 * ((1 - c3) * 255 + 1))
    : c0.val + 2*c1.val + 4*c2.val + 8*c3.val ≤ 15 ∧
      v0123 = ((2^(16 - (c0.val + 2*c1.val + 4*c2.val + 8*c3.val)) : ℕ) : FKB) := by
    rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;>
    rcases hc2 with h2 | h2 <;> rcases hc3 with h3 | h3 <;>
    subst h0 h1 h2 h3 <;>
    refine ⟨?_, ?_⟩ <;> simp_all

  -- =====================================================================
  -- `s4` decomposition: same as SLL — the FKB sum `c0·1 + c1·2 + c2·4 + c3·8`
  -- has Nat value `c0.val + 2 c1.val + 4 c2.val + 8 c3.val`, and
  -- `16 - s4_FKB` has Nat value `16 - s4_nat`.
  -- =====================================================================
  private lemma s4_FKB_val
      (c0 c1 c2 c3 : FKB)
      (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1)
      (hc2 : c2 = 0 ∨ c2 = 1) (hc3 : c3 = 0 ∨ c3 = 1)
    : (c0 + c1 * 2 + c2 * 4 + c3 * 8).val
        = c0.val + 2*c1.val + 4*c2.val + 8*c3.val ∧
      (16 - (c0 + c1 * 2 + c2 * 4 + c3 * 8) : FKB).val
        = 16 - (c0.val + 2*c1.val + 4*c2.val + 8*c3.val) := by
    rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;>
    rcases hc2 with h2 | h2 <;> rcases hc3 with h3 | h3 <;>
    subst h0 h1 h2 h3 <;> decide

  -- =====================================================================
  -- `c_0` mod-64 decomposition (same as SLLChip but with `c` replacing
  -- the `c_0` column).
  -- =====================================================================
  private lemma c_mod64
      (c_col s5_FKB : FKB)
      (hs5_val : s5_FKB.val ≤ 63)
      (hdecomp : ((c_col - s5_FKB) * 2097414145).val < 1024)
    : c_col.val % 64 = s5_FKB.val := by
    set t : FKB := (c_col - s5_FKB) * 2097414145 with ht_def
    have hinv : (64 : FKB) * 2097414145 = 1 := by decide
    have h64t : 64 * t = c_col - s5_FKB := by
      rw [ht_def]; linear_combination (c_col - s5_FKB) * hinv
    have hc_eq : c_col = s5_FKB + 64 * t := by rw [h64t]; ring
    have h64t_val : (64 * t : FKB).val = 64 * t.val := by
      rw [Fin.val_mul]
      have : (((64 : FKB)).val : ℕ) = 64 := by decide
      rw [this]
      apply Nat.mod_eq_of_lt
      have : t.val < 1024 := hdecomp
      omega
    have hsum_val : (s5_FKB + 64 * t : FKB).val = s5_FKB.val + 64 * t.val := by
      rw [Fin.val_add, h64t_val]
      apply Nat.mod_eq_of_lt
      have : t.val < 1024 := hdecomp
      omega
    apply_fun Fin.val at hc_eq
    rw [hsum_val] at hc_eq
    omega

  -- =====================================================================
  -- spec_SRL — opcode 6 (64-bit logical right shift).
  --
  -- Status: SORRY — needs the b-decomposition and c-equality assumptions
  -- (see file header) plus the BitVec identity proof.
  -- =====================================================================

  lemma spec_SRL
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_srl : air.cols.values.is_srl row 0 = 1)
    (h_is_sra : air.cols.values.is_sra row 0 = 0)
    (h_is_srlw : air.cols.values.is_srlw row 0 = 0)
    (h_is_sraw : air.cols.values.is_sraw row 0 = 0)
    -- MISSING (Pico soundness gap): `b_i = higher_limb_i · 2^s4 + lower_limb_i`
    (_MISSING_b_decomp_0 : (air.cols.values.b_0 row 0).val
      = (air.cols.values.higher_limb_0 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_0 row 0).val)
    (_MISSING_b_decomp_1 : (air.cols.values.b_1 row 0).val
      = (air.cols.values.higher_limb_1 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_1 row 0).val)
    (_MISSING_b_decomp_2 : (air.cols.values.b_2 row 0).val
      = (air.cols.values.higher_limb_2 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_2 row 0).val)
    (_MISSING_b_decomp_3 : (air.cols.values.b_3 row 0).val
      = (air.cols.values.higher_limb_3 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_3 row 0).val)
    -- MISSING (Pico soundness gap): `c = c_for_lookup_0`
    (_MISSING_c_eq : (air.cols.values.c row 0) = (air.cols.values.c_for_lookup_0 row 0))
  :
    ALUBus.Spec
      6
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    -- Step 1: `is_real = 1` from the 4 selector hypotheses.
    have h_is_real :
      air.cols.values.is_srl row 0 + air.cols.values.is_sra row 0 +
      air.cols.values.is_srlw row 0 + air.cols.values.is_sraw row 0 = 1
      := by rw [h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]; ring
    -- Step 2: Extract operand u16 bounds from h_ext.
    simp [bus_row_ext_asm, bus_row, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_ext
    obtain ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩ := h_ext
    -- Step 3: Extract byte-bus assumptions from h_wf.
    --   With is_srl = 1, is_sra = is_srlw = is_sraw = 0, all U16MSB byte
    --   entries (gated by is_sra, is_sraw, is_srlw + is_sraw) are
    --   vacuous. Only the 9 BitRange (opcode 9) entries fire.
    simp [bus_row_wf_asm, bus_row, ByteBus.Spec, h_is_srl, h_is_sra, h_is_srlw, h_is_sraw]
      at h_wf
    obtain ⟨h_c_decomp,
            ⟨_, h_lo0⟩, ⟨_, h_hi0⟩, ⟨_, h_lo1⟩, ⟨_, h_hi1⟩,
            ⟨_, h_lo2⟩, ⟨_, h_hi2⟩, ⟨_, h_lo3⟩, _, h_hi3⟩ := h_wf
    -- Step 4: Extract all 59 constraints (post-simp with selectors).
    simp [constraint_and_interaction_simplification, sub_eq_zero,
          h_is_srl, h_is_sra, h_is_srlw, h_is_sraw] at h_constraints
    obtain ⟨_, _h_imm_c_b, _h_w_imm,
            h_cb0_b, h_cb1_b, h_cb2_b, h_cb3_b, h_cb4_b, h_cb5_b,
            h_v01, h_v012, h_v0123,
            h_su0_sel, h_su0_b, h_su1_sel, h_su1_b,
            h_su2_sel, h_su2_b, h_su3_sel, h_su3_b,
            h_su_sum,
            h_lr0, h_lr1, h_lr2, h_lr3,
            _h_b_msb_b, h_b_msb_zero, h_sra_msb_v0123,
            _h_srw_msb_b, h_srw_msb_zero,
            h_su0_a0, h_su0_a1, h_su0_a2, h_su0_a3,
            h_su1_a0, h_su1_a1, h_su1_a2, h_su1_a3,
            h_su2_a0, h_su2_a1, h_su2_a2, h_su2_a3,
            h_su3_a0, h_su3_a1, h_su3_a2, h_su3_a3⟩ := h_constraints
    -- Step 5: Derive `v_0123 = 2^(16-k)` and `k ≤ 15` (where `k = c_bits sum`).
    set k_nat : ℕ := (air.cols.values.c_bits_0 row 0).val
                   + 2 * (air.cols.values.c_bits_1 row 0).val
                   + 4 * (air.cols.values.c_bits_2 row 0).val
                   + 8 * (air.cols.values.c_bits_3 row 0).val with hk_def
    obtain ⟨hk_le, hv⟩ := v0123_pow_inv _ _ _ _ _ _ _
      h_cb0_b h_cb1_b h_cb2_b h_cb3_b h_v01 h_v012 h_v0123
    obtain ⟨hs4_val, h16s4_val⟩ := s4_FKB_val _ _ _ _ h_cb0_b h_cb1_b h_cb2_b h_cb3_b
    -- Step 6: Convert byte-bus bounds to Nat form using s4_FKB_val.
    rw [hs4_val] at h_lo0 h_lo1 h_lo2 h_lo3
    rw [h16s4_val] at h_hi0 h_hi1 h_hi2 h_hi3
    change _ < 2^(k_nat) at h_lo0 h_lo1 h_lo2 h_lo3
    change _ < 2^(16 - k_nat) at h_hi0 h_hi1 h_hi2 h_hi3
    -- Step 7: Use MISSING_b_decomp_i for per-limb identities (assumption).
    -- (For SR these are axiomatic — see file header comment for the Pico gap.)
    have h_decomp_0 : (air.cols.values.b_0 row 0).val
        = (air.cols.values.higher_limb_0 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_0 row 0).val := _MISSING_b_decomp_0
    have h_decomp_1 : (air.cols.values.b_1 row 0).val
        = (air.cols.values.higher_limb_1 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_1 row 0).val := _MISSING_b_decomp_1
    have h_decomp_2 : (air.cols.values.b_2 row 0).val
        = (air.cols.values.higher_limb_2 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_2 row 0).val := _MISSING_b_decomp_2
    have h_decomp_3 : (air.cols.values.b_3 row 0).val
        = (air.cols.values.higher_limb_3 row 0).val * 2^k_nat
          + (air.cols.values.lower_limb_3 row 0).val := _MISSING_b_decomp_3
    -- Step 8+: limb_result values, case-split, BitVec identity.
    sorry

  -- =====================================================================
  -- spec_SRA — opcode 7 (64-bit arithmetic right shift, sign-extends b's MSB).
  -- Status: SORRY.
  -- =====================================================================

  lemma spec_SRA
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_sra : air.cols.values.is_sra row 0 = 1)
    (_MISSING_b_decomp_0 : (air.cols.values.b_0 row 0).val
      = (air.cols.values.higher_limb_0 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_0 row 0).val)
    (_MISSING_b_decomp_1 : (air.cols.values.b_1 row 0).val
      = (air.cols.values.higher_limb_1 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_1 row 0).val)
    (_MISSING_b_decomp_2 : (air.cols.values.b_2 row 0).val
      = (air.cols.values.higher_limb_2 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_2 row 0).val)
    (_MISSING_b_decomp_3 : (air.cols.values.b_3 row 0).val
      = (air.cols.values.higher_limb_3 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_3 row 0).val)
    (_MISSING_c_eq : (air.cols.values.c row 0) = (air.cols.values.c_for_lookup_0 row 0))
  :
    ALUBus.Spec
      7
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    sorry

  -- =====================================================================
  -- spec_SRLW — opcode 43 (32-bit logical right shift, sign-extended via
  -- srw_msb = MSB of a_1).
  -- Status: SORRY.
  -- =====================================================================

  lemma spec_SRLW
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_srlw : air.cols.values.is_srlw row 0 = 1)
    (_MISSING_b_decomp_0 : (air.cols.values.b_0 row 0).val
      = (air.cols.values.higher_limb_0 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_0 row 0).val)
    (_MISSING_b_decomp_1 : (air.cols.values.b_1 row 0).val
      = (air.cols.values.higher_limb_1 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_1 row 0).val)
    (_MISSING_b_decomp_2 : (air.cols.values.b_2 row 0).val
      = (air.cols.values.higher_limb_2 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_2 row 0).val)
    (_MISSING_b_decomp_3 : (air.cols.values.b_3 row 0).val
      = (air.cols.values.higher_limb_3 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_3 row 0).val)
    (_MISSING_c_eq : (air.cols.values.c row 0) = (air.cols.values.c_for_lookup_0 row 0))
  :
    ALUBus.Spec
      43
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    sorry

  -- =====================================================================
  -- spec_SRAW — opcode 44 (32-bit arithmetic right shift, sign-extended).
  -- Status: SORRY.
  -- =====================================================================

  lemma spec_SRAW
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
    (h_is_sraw : air.cols.values.is_sraw row 0 = 1)
    (_MISSING_b_decomp_0 : (air.cols.values.b_0 row 0).val
      = (air.cols.values.higher_limb_0 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_0 row 0).val)
    (_MISSING_b_decomp_1 : (air.cols.values.b_1 row 0).val
      = (air.cols.values.higher_limb_1 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_1 row 0).val)
    (_MISSING_b_decomp_2 : (air.cols.values.b_2 row 0).val
      = (air.cols.values.higher_limb_2 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_2 row 0).val)
    (_MISSING_b_decomp_3 : (air.cols.values.b_3 row 0).val
      = (air.cols.values.higher_limb_3 row 0).val *
          2^((air.cols.values.c_bits_0 row 0).val + 2*(air.cols.values.c_bits_1 row 0).val
             + 4*(air.cols.values.c_bits_2 row 0).val + 8*(air.cols.values.c_bits_3 row 0).val)
        + (air.cols.values.lower_limb_3 row 0).val)
    (_MISSING_c_eq : (air.cols.values.c row 0) = (air.cols.values.c_for_lookup_0 row 0))
  :
    ALUBus.Spec
      44
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_for_lookup_0 row 0) (air.cols.values.c_for_lookup_1 row 0)
      (air.cols.values.c_for_lookup_2 row 0) (air.cols.values.c_for_lookup_3 row 0)
  := by
    sorry

  --
  -- Externals — vacuous (negative byte multiplicities, never +1).
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row]
    intro h; exfalso; grind

  --
  -- wf_asrt — TODO (will dispatch to spec_SRL / spec_SRA / spec_SRLW / spec_SRAW).
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_ShiftRightChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : ShiftRightChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    sorry

end ShiftRightChip.Spec
