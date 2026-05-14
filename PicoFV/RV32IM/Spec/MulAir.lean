import PicoFV.RV32IM.Constraints.MulAir
import Mathlib.Tactic.LinearCombination

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace MulAir.Spec

  open RV32IM_Interactions
  open MulAir.ConstraintsAndBuses
  open MulAir.Interactions
  open MulAir.Interpretations

  -- ============================================
  -- Helper: upper bound on product of two bytes.
  -- ============================================

  private lemma ub_byte_prod {a b : Fin KB} (ha : a.val < 256) (hb : b.val < 256)
  :
    a.val * b.val ≤ 65025
  := by
    trans 255 * 255 <;> [ apply mul_le_mul; skip ] <;> omega

  -- ==========================================================================
  -- Core schoolbook multiplication correctness: given 8 carry-chain equations,
  -- proves U64b.toBV prod = U64b.toBV bw * U64b.toBV cw.
  -- Uses joins/divs lemmas to fold carries into a single 64-bit equation.
  -- ==========================================================================

  lemma core_mul
    (b c : U32b)
    (sgn_b sgn_c : Bool)
    (prod : U64b)
    (cy0 cy1 cy2 cy3 cy4 cy5 cy6 cy7 : ℕ) :
    let bw := b.extend sgn_b
    let cw := c.extend sgn_c
    -- Carry chain equations (schoolbook byte-multiplication)
    prod[0].toNat + cy0 * 256 =
      bw[0].toNat * cw[0].toNat →
    prod[1].toNat + cy1 * 256 =
      bw[0].toNat * cw[1].toNat + bw[1].toNat * cw[0].toNat + cy0 →
    prod[2].toNat + cy2 * 256 =
      bw[0].toNat * cw[2].toNat + bw[1].toNat * cw[1].toNat +
      bw[2].toNat * cw[0].toNat + cy1 →
    prod[3].toNat + cy3 * 256 =
      bw[0].toNat * cw[3].toNat + bw[1].toNat * cw[2].toNat +
      bw[2].toNat * cw[1].toNat + bw[3].toNat * cw[0].toNat + cy2 →
    prod[4].toNat + cy4 * 256 =
      bw[0].toNat * cw[4].toNat + bw[1].toNat * cw[3].toNat +
      bw[2].toNat * cw[2].toNat + bw[3].toNat * cw[1].toNat +
      bw[4].toNat * cw[0].toNat + cy3 →
    prod[5].toNat + cy5 * 256 =
      bw[0].toNat * cw[5].toNat + bw[1].toNat * cw[4].toNat +
      bw[2].toNat * cw[3].toNat + bw[3].toNat * cw[2].toNat +
      bw[4].toNat * cw[1].toNat + bw[5].toNat * cw[0].toNat + cy4 →
    prod[6].toNat + cy6 * 256 =
      bw[0].toNat * cw[6].toNat + bw[1].toNat * cw[5].toNat +
      bw[2].toNat * cw[4].toNat + bw[3].toNat * cw[3].toNat +
      bw[4].toNat * cw[2].toNat + bw[5].toNat * cw[1].toNat +
      bw[6].toNat * cw[0].toNat + cy5 →
    prod[7].toNat + cy7 * 256 =
      bw[0].toNat * cw[7].toNat + bw[1].toNat * cw[6].toNat +
      bw[2].toNat * cw[5].toNat + bw[3].toNat * cw[4].toNat +
      bw[4].toNat * cw[3].toNat + bw[5].toNat * cw[2].toNat +
      bw[6].toNat * cw[1].toNat + bw[7].toNat * cw[0].toNat + cy6 →
    U64b.toBV prod = U64b.toBV bw * U64b.toBV cw := by
    intro bw cw h0 h1 h2 h3 h4 h5 h6 h7

    simp [← BitVec.toNat_inj,U64b.toNat]

    set p0 := prod[0].toNat; set p1 := prod[1].toNat; set p2 := prod[2].toNat; set p3 := prod[3].toNat
    set p4 := prod[4].toNat; set p5 := prod[5].toNat; set p6 := prod[6].toNat; set p7 := prod[7].toNat
    set b0 := bw[0].toNat; set b1 := bw[1].toNat; set b2 := bw[2].toNat; set b3 := bw[3].toNat
    set b4 := bw[4].toNat; set b5 := bw[5].toNat; set b6 := bw[6].toNat; set b7 := bw[7].toNat
    set c0 := cw[0].toNat; set c1 := cw[1].toNat; set c2 := cw[2].toNat; set c3 := cw[3].toNat
    set c4 := cw[4].toNat; set c5 := cw[5].toNat; set c6 := cw[6].toNat; set c7 := cw[7].toNat
    have ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_b4, ub_b5, ub_b6, ub_b7,
           ub_c0, ub_c1, ub_c2, ub_c3, ub_c4, ub_c5, ub_c6, ub_c7 ⟩ :
      p0 < 256 ∧ p1 < 256 ∧ p2 < 256 ∧ p3 < 256 ∧ p4 < 256 ∧ p5 < 256 ∧ p6 < 256 ∧ p7 < 256 ∧
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧ b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧ b7 < 256 ∧
      c0 < 256 ∧ c1 < 256 ∧ c2 < 256 ∧ c3 < 256 ∧ c4 < 256 ∧ c5 < 256 ∧ c6 < 256 ∧ c6 < 256
    := by subst b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7; omega

    -- Derive mod/div decompositions from carry chain
    have eqp0 : p0 = (b0 * c0) % 256 := by omega
    have eqc0 : cy0 = (b0 * c0) / 256 := by omega
    have eqp1 : p1 = (b0 * c1 + b1 * c0 + cy0) % 256 := by omega
    have eqc1 : cy1 = (b0 * c1 + b1 * c0 + cy0) / 256 := by omega
    have eqp2 : p2 = (b0 * c2 + b1 * c1 + b2 * c0 + cy1) % 256 := by omega
    have eqc2 : cy2 = (b0 * c2 + b1 * c1 + b2 * c0 + cy1) / 256 := by omega
    have eqp3 : p3 = (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0 + cy2) % 256 := by omega
    have eqc3 : cy3 = (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0 + cy2) / 256 := by omega
    have eqp4 : p4 = (b0 * c4 + b1 * c3 + b2 * c2 + b3 * c1 + b4 * c0 + cy3) % 256 := by omega
    have eqc4 : cy4 = (b0 * c4 + b1 * c3 + b2 * c2 + b3 * c1 + b4 * c0 + cy3) / 256 := by omega
    have eqp5 : p5 = (b0 * c5 + b1 * c4 + b2 * c3 + b3 * c2 + b4 * c1 + b5 * c0 + cy4) % 256 := by omega
    have eqc5 : cy5 = (b0 * c5 + b1 * c4 + b2 * c3 + b3 * c2 + b4 * c1 + b5 * c0 + cy4) / 256 := by omega
    have eqp6 : p6 = (b0 * c6 + b1 * c5 + b2 * c4 + b3 * c3 + b4 * c2 + b5 * c1 + b6 * c0 + cy5) % 256 := by omega
    have eqc6 : cy6 = (b0 * c6 + b1 * c5 + b2 * c4 + b3 * c3 + b4 * c2 + b5 * c1 + b6 * c0 + cy5) / 256 := by omega
    have eqp7 : p7 = (b0 * c7 + b1 * c6 + b2 * c5 + b3 * c4 + b4 * c3 + b5 * c2 + b6 * c1 + b7 * c0 + cy6) % 256 := by omega
    have eqc7 : cy7 = (b0 * c7 + b1 * c6 + b2 * c5 + b3 * c4 + b4 * c3 + b5 * c2 + b6 * c1 + b7 * c0 + cy6) / 256 := by omega

    clear h0 h1 h2 h3 h4 h5 h6 h7

    -- Substitute mod/div decompositions
    simp [eqp0, eqp1, eqp2, eqp3, eqp4, eqp5, eqp6, eqp7,
        eqc0, eqc1, eqc2, eqc3, eqc4, eqc5, eqc6]
    clear eqp0 eqp1 eqp2 eqp3 eqp4 eqp5 eqp6 eqp7
          eqc0 eqc1 eqc2 eqc3 eqc4 eqc5 eqc6 eqc7

    -- Joins/divs lemmas (from SP1)
    have joins : ∀ (i : Fin 8) (a b : ℕ),
      a % (256 ^ i.val) + (b + a / (256 ^ i.val)) % 256 * (256 ^ i.val) =
      (a + b * (256 ^ i.val)) % (256 ^ (i.val + 1)) := by
      intro i a b; fin_cases i <;> simp <;> omega
    have divs : ∀ (i : Fin 8) (a b : ℕ),
      (a + b / (256 ^ i.val)) / 256 =
      (b + a * (256 ^ i.val)) / (256 ^ (i.val + 1)) := by
      intro i a b; fin_cases i <;> simp <;> omega

    have j1 := joins 1; have j2 := joins 2; have j3 := joins 3; have j4 := joins 4
    have j5 := joins 5; have j6 := joins 6; have j7 := joins 7
    have d1 := divs 1; have d2 := divs 2; have d3 := divs 3; have d4 := divs 4
    have d5 := divs 5; have d6 := divs 6; have d7 := divs 7
    simp at j1 j2 j3 j4 j5 j6 j7 d1 d2 d3 d4 d5 d6 d7

    rw [j1, d1, j2, d2, j3, d3, j4, d4, j5, d5, j6, d6, j7]
    ring_nf
    omega

  -- ===========================================
  -- Helpers: extract low/high 32 bits from U64b.
  -- ===========================================

  private lemma U64_extractLsb_low (x : U64b) :
      BitVec.extractLsb 31 0 (U64b.toBV x) = U32b.toBV #v[x[0], x[1], x[2], x[3]] := by
    simp [← BitVec.toNat_inj, U64b.toNat, U32b.toNat]
    omega

  private lemma U64_extractLsb_high (x : U64b) :
      BitVec.extractLsb 63 32 (U64b.toBV x) = U32b.toBV #v[x[4], x[5], x[6], x[7]] := by
    simp [← BitVec.toNat_inj, U64b.toNat, U32b.toNat]
    omega

  --
  -- Externals
  --

  -- =======================
  -- Externality assertions.
  -- =======================

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_MulAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_constraints : MulAir.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selector_exclusivity := selector_exclusivity air row h_is_real h_constraints
    simp [bus_row_ext_asrt, bus_row]
    grind

  --
  -- Opcode specifications
  --

  -- ========================================================================
  -- MUL (opcode 30): low 32 bits of unsigned product.
  -- Applies core_mul with extend=false for both operands, extracts low word.
  -- ========================================================================

  lemma spec_MUL
    [Field ExtF]
    (air : Valid_MulAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulAir.Extraction.allHold air row)
    (h_is_mul : air.cols.is_mul row 0 = 1)
  :
    ALUBus.Spec
      30
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    simp [ALUBus.Spec]
    have selector_exclusivity := selector_exclusivity air row h_is_real h_constraints
    simp [h_is_mul] at selector_exclusivity; replace selector_exclusivity := selector_exclusivity.1
    simp [bus_row_ext_asm, bus_row, h_is_real, h_is_mul, selector_exclusivity] at h_ext
    obtain ⟨ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3⟩ := h_ext
    simp [constraint_and_interaction_simplification, sub_eq_zero, *] at h_constraints
    obtain ⟨ ci, h_bse, h_cse, h_p0, h_p1, h_p2, h_p3, h_p4, h_p5, h_p6, h_p7,
             h_a0, h_a1, h_a2, h_a3, h_b_bmsb, h_b_cmsb, h_b_bse, h_b_cse, h_bse_msb, h_cse_msb ⟩ := h_constraints
    clear ci; rw [← h_a0, ← h_a1, ← h_a2, ← h_a3]; clear h_a0 h_a1 h_a2 h_a3

    simp [bus_row_wf_asm, bus_row, h_is_real, ByteBus.Spec, and_assoc] at h_wf
    simp [h_wf]
    obtain ⟨ eq_bmsb, ub_bmsb, ub_b3, eq_cmsb, ub_cmsb, ub_c3,
             ub_cy0, ub_cy1, ub_cy2, ub_cy3, ub_cy4, ub_cy5, ub_cy6, ub_cy7,
             ub_p0, ub_p1, ub_p2, ub_p3, ub_p4, ub_p5, ub_p6, ub_p7 ⟩ := h_wf
    clear ub_b3 ub_c3

    set b0 := air.cols.b_0 row 0; set b1 := air.cols.b_1 row 0; set b2 := air.cols.b_2 row 0; set b3 := air.cols.b_3 row 0
    set c0 := air.cols.c_0 row 0; set c1 := air.cols.c_1 row 0; set c2 := air.cols.c_2 row 0; set c3 := air.cols.c_3 row 0
    set p0 := air.cols.product_0 row 0; set p1 := air.cols.product_1 row 0; set p2 := air.cols.product_2 row 0; set p3 := air.cols.product_3 row 0
    set p4 := air.cols.product_4 row 0; set p5 := air.cols.product_5 row 0; set p6 := air.cols.product_6 row 0; set p7 := air.cols.product_7 row 0
    set cy0 := air.cols.carry_0 row 0; set cy1 := air.cols.carry_1 row 0; set cy2 := air.cols.carry_2 row 0; set cy3 := air.cols.carry_3 row 0
    set cy4 := air.cols.carry_4 row 0; set cy5 := air.cols.carry_5 row 0; set cy6 := air.cols.carry_6 row 0; set cy7 := air.cols.carry_7 row 0
    set b_ext := air.cols.b_sign_extend row 0 * 255; set c_ext := air.cols.c_sign_extend row 0 * 255

    have ub_b_ext : b_ext < 256 := by clear *- h_b_bse; subst b_ext; omega
    have ub_c_ext : c_ext < 256 := by clear *- h_b_cse; subst c_ext; omega

    have ub_00 := ub_byte_prod ub_b0 ub_c0; have ub_01 := ub_byte_prod ub_b0 ub_c1;
    have ub_02 := ub_byte_prod ub_b0 ub_c2; have ub_03 := ub_byte_prod ub_b0 ub_c3;
    have ub_10 := ub_byte_prod ub_b1 ub_c0; have ub_11 := ub_byte_prod ub_b1 ub_c1;
    have ub_12 := ub_byte_prod ub_b1 ub_c2; have ub_13 := ub_byte_prod ub_b1 ub_c3;
    have ub_20 := ub_byte_prod ub_b2 ub_c0; have ub_21 := ub_byte_prod ub_b2 ub_c1;
    have ub_22 := ub_byte_prod ub_b2 ub_c2; have ub_23 := ub_byte_prod ub_b2 ub_c3;
    have ub_30 := ub_byte_prod ub_b3 ub_c0; have ub_31 := ub_byte_prod ub_b3 ub_c1;
    have ub_32 := ub_byte_prod ub_b3 ub_c2; have ub_33 := ub_byte_prod ub_b3 ub_c3;

    have ub_eb0 := ub_byte_prod ub_b_ext ub_c0; have ub_eb1 := ub_byte_prod ub_b_ext ub_c1;
    have ub_eb2 := ub_byte_prod ub_b_ext ub_c2; have ub_eb3 := ub_byte_prod ub_b_ext ub_c3;
    have ub_ec0 := ub_byte_prod ub_b0 ub_c_ext; have ub_ec1 := ub_byte_prod ub_b1 ub_c_ext;
    have ub_ec2 := ub_byte_prod ub_b2 ub_c_ext; have ub_ec3 := ub_byte_prod ub_b3 ub_c_ext;

    simp [RV32IM.execute_MUL_pure]

    set b : U32b := #v[b0, b1, b2, b3]
    set c : U32b := #v[c0, c1, c2, c3]
    set prod : U64b := #v[p0, p1, p2, p3, p4, p5, p6, p7]

    rw [eq_sub_iff_add_eq] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    have h_b_ext : b.extend false = (#v[b0, b1, b2, b3, b_ext, b_ext, b_ext, b_ext] : U64b)
    := by
      have : b.ext false = b_ext.val := by
        subst b_ext
        simp [U32b.ext, h_bse]
      simp only [U32b.extend]; congr

    have h_c_ext : c.extend false = (#v[c0, c1, c2, c3, c_ext, c_ext, c_ext, c_ext] : U64b)
    := by
      have : c.ext false = c_ext.val := by
        subst c_ext
        simp [U32b.ext, h_cse]
      simp only [U32b.extend]; congr

    have core_mul := core_mul b c false false prod cy0.val cy1.val cy2.val cy3.val cy4.val cy5.val cy6.val cy7.val
    simp [prod, h_b_ext, h_c_ext] at core_mul
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at core_mul
    specialize core_mul h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    simp [← U32b.extend_BitVec_extend, h_b_ext, h_c_ext]
    rw [← core_mul, U64_extractLsb_low]
    rfl

  -- ===============================================================
  -- MULH (opcode 31): high 32 bits of signed*signed product.
  -- Applies core_mul with extend=true for both, extracts high word.
  -- ===============================================================

  lemma spec_MULH
    [Field ExtF]
    (air : Valid_MulAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulAir.Extraction.allHold air row)
    (h_is_mulh : air.cols.is_mulh row 0 = 1)
  :
    ALUBus.Spec
      31
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    simp [ALUBus.Spec]
    have selector_exclusivity := selector_exclusivity air row h_is_real h_constraints
    simp [h_is_mulh] at selector_exclusivity; replace selector_exclusivity := selector_exclusivity.2.1
    simp [bus_row_ext_asm, bus_row, h_is_real, h_is_mulh, selector_exclusivity] at h_ext
    obtain ⟨ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3⟩ := h_ext
    simp [constraint_and_interaction_simplification, sub_eq_zero, *] at h_constraints
    obtain ⟨ ci, h_bse, h_cse, h_p0, h_p1, h_p2, h_p3, h_p4, h_p5, h_p6, h_p7,
             h_a0, h_a1, h_a2, h_a3, h_b_bmsb, h_b_cmsb, h_b_bse, h_b_cse, h_bse_msb, h_cse_msb ⟩ := h_constraints
    clear ci; rw [← h_a0, ← h_a1, ← h_a2, ← h_a3]; clear h_a0 h_a1 h_a2 h_a3

    simp [bus_row_wf_asm, bus_row, h_is_real, ByteBus.Spec, and_assoc] at h_wf
    simp [h_wf]
    obtain ⟨ eq_bmsb, ub_bmsb, ub_b3, eq_cmsb, ub_cmsb, ub_c3,
             ub_cy0, ub_cy1, ub_cy2, ub_cy3, ub_cy4, ub_cy5, ub_cy6, ub_cy7,
             ub_p0, ub_p1, ub_p2, ub_p3, ub_p4, ub_p5, ub_p6, ub_p7 ⟩ := h_wf
    clear ub_b3 ub_c3

    set b0 := air.cols.b_0 row 0; set b1 := air.cols.b_1 row 0; set b2 := air.cols.b_2 row 0; set b3 := air.cols.b_3 row 0
    set c0 := air.cols.c_0 row 0; set c1 := air.cols.c_1 row 0; set c2 := air.cols.c_2 row 0; set c3 := air.cols.c_3 row 0
    set p0 := air.cols.product_0 row 0; set p1 := air.cols.product_1 row 0; set p2 := air.cols.product_2 row 0; set p3 := air.cols.product_3 row 0
    set p4 := air.cols.product_4 row 0; set p5 := air.cols.product_5 row 0; set p6 := air.cols.product_6 row 0; set p7 := air.cols.product_7 row 0
    set cy0 := air.cols.carry_0 row 0; set cy1 := air.cols.carry_1 row 0; set cy2 := air.cols.carry_2 row 0; set cy3 := air.cols.carry_3 row 0
    set cy4 := air.cols.carry_4 row 0; set cy5 := air.cols.carry_5 row 0; set cy6 := air.cols.carry_6 row 0; set cy7 := air.cols.carry_7 row 0
    set b_ext := air.cols.b_sign_extend row 0 * 255; set c_ext := air.cols.c_sign_extend row 0 * 255

    have ub_b_ext : b_ext < 256 := by clear *- h_b_bse; subst b_ext; omega
    have ub_c_ext : c_ext < 256 := by clear *- h_b_cse; subst c_ext; omega

    have ub_00 := ub_byte_prod ub_b0 ub_c0; have ub_01 := ub_byte_prod ub_b0 ub_c1;
    have ub_02 := ub_byte_prod ub_b0 ub_c2; have ub_03 := ub_byte_prod ub_b0 ub_c3;
    have ub_10 := ub_byte_prod ub_b1 ub_c0; have ub_11 := ub_byte_prod ub_b1 ub_c1;
    have ub_12 := ub_byte_prod ub_b1 ub_c2; have ub_13 := ub_byte_prod ub_b1 ub_c3;
    have ub_20 := ub_byte_prod ub_b2 ub_c0; have ub_21 := ub_byte_prod ub_b2 ub_c1;
    have ub_22 := ub_byte_prod ub_b2 ub_c2; have ub_23 := ub_byte_prod ub_b2 ub_c3;
    have ub_30 := ub_byte_prod ub_b3 ub_c0; have ub_31 := ub_byte_prod ub_b3 ub_c1;
    have ub_32 := ub_byte_prod ub_b3 ub_c2; have ub_33 := ub_byte_prod ub_b3 ub_c3;

    have ub_eb0 := ub_byte_prod ub_b_ext ub_c0; have ub_eb1 := ub_byte_prod ub_b_ext ub_c1;
    have ub_eb2 := ub_byte_prod ub_b_ext ub_c2; have ub_eb3 := ub_byte_prod ub_b_ext ub_c3;
    have ub_ec0 := ub_byte_prod ub_b0 ub_c_ext; have ub_ec1 := ub_byte_prod ub_b1 ub_c_ext;
    have ub_ec2 := ub_byte_prod ub_b2 ub_c_ext; have ub_ec3 := ub_byte_prod ub_b3 ub_c_ext;

    simp [RV32IM.execute_MUL_pure]

    set b : U32b := #v[b0, b1, b2, b3]
    set c : U32b := #v[c0, c1, c2, c3]
    set prod : U64b := #v[p0, p1, p2, p3, p4, p5, p6, p7]

    rw [eq_sub_iff_add_eq] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    have h_b_ext : b.extend true = (#v[b0, b1, b2, b3, b_ext, b_ext, b_ext, b_ext] : U64b)
    := by
      have : b.ext true = b_ext.val := by
        subst b_ext
        simp [U32b.ext, h_bse, eq_bmsb, b, ← U32b.msb_3_negative, BitVec.msb_eq_decide]
        clear *- ub_b3; grind
      simp only [U32b.extend]; congr

    have h_c_ext : c.extend true = (#v[c0, c1, c2, c3, c_ext, c_ext, c_ext, c_ext] : U64b)
    := by
      have : c.ext true = c_ext.val := by
        subst c_ext
        simp [U32b.ext, h_cse, eq_cmsb, c, ← U32b.msb_3_negative, BitVec.msb_eq_decide]
        clear *- ub_c3; grind
      simp only [U32b.extend]; congr

    have core_mul := core_mul b c true true prod cy0.val cy1.val cy2.val cy3.val cy4.val cy5.val cy6.val cy7.val
    simp [prod, h_b_ext, h_c_ext] at core_mul
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at core_mul
    specialize core_mul h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    simp [← U32b.extend_BitVec_extend, h_b_ext, h_c_ext]
    rw [← core_mul, U64_extractLsb_high]
    rfl

  -- =============================================================
  -- MULHU (opcode 32): high 32 bits of unsigned*unsigned product.
  -- =============================================================

  lemma spec_MULHU
    [Field ExtF]
    (air : Valid_MulAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulAir.Extraction.allHold air row)
    (h_is_mulhu : air.cols.is_mulhu row 0 = 1)
  :
    ALUBus.Spec
      32
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    simp [ALUBus.Spec]
    have selector_exclusivity := selector_exclusivity air row h_is_real h_constraints
    simp [h_is_mulhu] at selector_exclusivity; replace selector_exclusivity := selector_exclusivity.2.2.1
    simp [bus_row_ext_asm, bus_row, h_is_real, h_is_mulhu, selector_exclusivity] at h_ext
    obtain ⟨ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3⟩ := h_ext
    simp [constraint_and_interaction_simplification, sub_eq_zero, *] at h_constraints
    obtain ⟨ ci, h_bse, h_cse, h_p0, h_p1, h_p2, h_p3, h_p4, h_p5, h_p6, h_p7,
             h_a0, h_a1, h_a2, h_a3, h_b_bmsb, h_b_cmsb, h_b_bse, h_b_cse, h_bse_msb, h_cse_msb ⟩ := h_constraints
    clear ci; rw [← h_a0, ← h_a1, ← h_a2, ← h_a3]; clear h_a0 h_a1 h_a2 h_a3

    simp [bus_row_wf_asm, bus_row, h_is_real, ByteBus.Spec, and_assoc] at h_wf
    simp [h_wf]
    obtain ⟨ eq_bmsb, ub_bmsb, ub_b3, eq_cmsb, ub_cmsb, ub_c3,
             ub_cy0, ub_cy1, ub_cy2, ub_cy3, ub_cy4, ub_cy5, ub_cy6, ub_cy7,
             ub_p0, ub_p1, ub_p2, ub_p3, ub_p4, ub_p5, ub_p6, ub_p7 ⟩ := h_wf
    clear ub_b3 ub_c3

    set b0 := air.cols.b_0 row 0; set b1 := air.cols.b_1 row 0; set b2 := air.cols.b_2 row 0; set b3 := air.cols.b_3 row 0
    set c0 := air.cols.c_0 row 0; set c1 := air.cols.c_1 row 0; set c2 := air.cols.c_2 row 0; set c3 := air.cols.c_3 row 0
    set p0 := air.cols.product_0 row 0; set p1 := air.cols.product_1 row 0; set p2 := air.cols.product_2 row 0; set p3 := air.cols.product_3 row 0
    set p4 := air.cols.product_4 row 0; set p5 := air.cols.product_5 row 0; set p6 := air.cols.product_6 row 0; set p7 := air.cols.product_7 row 0
    set cy0 := air.cols.carry_0 row 0; set cy1 := air.cols.carry_1 row 0; set cy2 := air.cols.carry_2 row 0; set cy3 := air.cols.carry_3 row 0
    set cy4 := air.cols.carry_4 row 0; set cy5 := air.cols.carry_5 row 0; set cy6 := air.cols.carry_6 row 0; set cy7 := air.cols.carry_7 row 0
    set b_ext := air.cols.b_sign_extend row 0 * 255; set c_ext := air.cols.c_sign_extend row 0 * 255

    have ub_b_ext : b_ext < 256 := by clear *- h_b_bse; subst b_ext; omega
    have ub_c_ext : c_ext < 256 := by clear *- h_b_cse; subst c_ext; omega

    have ub_00 := ub_byte_prod ub_b0 ub_c0; have ub_01 := ub_byte_prod ub_b0 ub_c1;
    have ub_02 := ub_byte_prod ub_b0 ub_c2; have ub_03 := ub_byte_prod ub_b0 ub_c3;
    have ub_10 := ub_byte_prod ub_b1 ub_c0; have ub_11 := ub_byte_prod ub_b1 ub_c1;
    have ub_12 := ub_byte_prod ub_b1 ub_c2; have ub_13 := ub_byte_prod ub_b1 ub_c3;
    have ub_20 := ub_byte_prod ub_b2 ub_c0; have ub_21 := ub_byte_prod ub_b2 ub_c1;
    have ub_22 := ub_byte_prod ub_b2 ub_c2; have ub_23 := ub_byte_prod ub_b2 ub_c3;
    have ub_30 := ub_byte_prod ub_b3 ub_c0; have ub_31 := ub_byte_prod ub_b3 ub_c1;
    have ub_32 := ub_byte_prod ub_b3 ub_c2; have ub_33 := ub_byte_prod ub_b3 ub_c3;

    have ub_eb0 := ub_byte_prod ub_b_ext ub_c0; have ub_eb1 := ub_byte_prod ub_b_ext ub_c1;
    have ub_eb2 := ub_byte_prod ub_b_ext ub_c2; have ub_eb3 := ub_byte_prod ub_b_ext ub_c3;
    have ub_ec0 := ub_byte_prod ub_b0 ub_c_ext; have ub_ec1 := ub_byte_prod ub_b1 ub_c_ext;
    have ub_ec2 := ub_byte_prod ub_b2 ub_c_ext; have ub_ec3 := ub_byte_prod ub_b3 ub_c_ext;

    simp [RV32IM.execute_MUL_pure]

    set b : U32b := #v[b0, b1, b2, b3]
    set c : U32b := #v[c0, c1, c2, c3]
    set prod : U64b := #v[p0, p1, p2, p3, p4, p5, p6, p7]

    rw [eq_sub_iff_add_eq] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    have h_b_ext : b.extend false = (#v[b0, b1, b2, b3, b_ext, b_ext, b_ext, b_ext] : U64b)
    := by
      have : b.ext false = b_ext.val := by
        subst b_ext
        simp [U32b.ext, h_bse]
      simp only [U32b.extend]; congr

    have h_c_ext : c.extend false = (#v[c0, c1, c2, c3, c_ext, c_ext, c_ext, c_ext] : U64b)
    := by
      have : c.ext false = c_ext.val := by
        subst c_ext
        simp [U32b.ext, h_cse]
      simp only [U32b.extend]; congr

    have core_mul := core_mul b c false false prod cy0.val cy1.val cy2.val cy3.val cy4.val cy5.val cy6.val cy7.val
    simp [prod, h_b_ext, h_c_ext] at core_mul
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at core_mul
    specialize core_mul h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    simp [← U32b.extend_BitVec_extend, h_b_ext, h_c_ext]
    rw [← core_mul, U64_extractLsb_high]
    rfl

  -- ============================================================
  -- MULHSU (opcode 33): high 32 bits of signed*unsigned product.
  -- b extends signed, c extends unsigned.
  -- ============================================================

  lemma spec_MULHSU
    [Field ExtF]
    (air : Valid_MulAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulAir.Extraction.allHold air row)
    (h_is_mulhsu : air.cols.is_mulhsu row 0 = 1)
  :
    ALUBus.Spec
      33
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    simp [ALUBus.Spec]
    have selector_exclusivity := selector_exclusivity air row h_is_real h_constraints
    simp [h_is_mulhsu] at selector_exclusivity; replace selector_exclusivity := selector_exclusivity.2.2.2
    simp [bus_row_ext_asm, bus_row, h_is_real, h_is_mulhsu, selector_exclusivity] at h_ext
    obtain ⟨ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3⟩ := h_ext
    simp [constraint_and_interaction_simplification, sub_eq_zero, *] at h_constraints
    obtain ⟨ ci, h_bse, h_cse, h_p0, h_p1, h_p2, h_p3, h_p4, h_p5, h_p6, h_p7,
             h_a0, h_a1, h_a2, h_a3, h_b_bmsb, h_b_cmsb, h_b_bse, h_b_cse, h_bse_msb, h_cse_msb ⟩ := h_constraints
    clear ci; rw [← h_a0, ← h_a1, ← h_a2, ← h_a3]; clear h_a0 h_a1 h_a2 h_a3

    simp [bus_row_wf_asm, bus_row, h_is_real, ByteBus.Spec, and_assoc] at h_wf
    simp [h_wf]
    obtain ⟨ eq_bmsb, ub_bmsb, ub_b3, eq_cmsb, ub_cmsb, ub_c3,
             ub_cy0, ub_cy1, ub_cy2, ub_cy3, ub_cy4, ub_cy5, ub_cy6, ub_cy7,
             ub_p0, ub_p1, ub_p2, ub_p3, ub_p4, ub_p5, ub_p6, ub_p7 ⟩ := h_wf
    clear ub_b3 ub_c3

    set b0 := air.cols.b_0 row 0; set b1 := air.cols.b_1 row 0; set b2 := air.cols.b_2 row 0; set b3 := air.cols.b_3 row 0
    set c0 := air.cols.c_0 row 0; set c1 := air.cols.c_1 row 0; set c2 := air.cols.c_2 row 0; set c3 := air.cols.c_3 row 0
    set p0 := air.cols.product_0 row 0; set p1 := air.cols.product_1 row 0; set p2 := air.cols.product_2 row 0; set p3 := air.cols.product_3 row 0
    set p4 := air.cols.product_4 row 0; set p5 := air.cols.product_5 row 0; set p6 := air.cols.product_6 row 0; set p7 := air.cols.product_7 row 0
    set cy0 := air.cols.carry_0 row 0; set cy1 := air.cols.carry_1 row 0; set cy2 := air.cols.carry_2 row 0; set cy3 := air.cols.carry_3 row 0
    set cy4 := air.cols.carry_4 row 0; set cy5 := air.cols.carry_5 row 0; set cy6 := air.cols.carry_6 row 0; set cy7 := air.cols.carry_7 row 0
    set b_ext := air.cols.b_sign_extend row 0 * 255; set c_ext := air.cols.c_sign_extend row 0 * 255

    have ub_b_ext : b_ext < 256 := by clear *- h_b_bse; subst b_ext; omega
    have ub_c_ext : c_ext < 256 := by clear *- h_b_cse; subst c_ext; omega

    have ub_00 := ub_byte_prod ub_b0 ub_c0; have ub_01 := ub_byte_prod ub_b0 ub_c1;
    have ub_02 := ub_byte_prod ub_b0 ub_c2; have ub_03 := ub_byte_prod ub_b0 ub_c3;
    have ub_10 := ub_byte_prod ub_b1 ub_c0; have ub_11 := ub_byte_prod ub_b1 ub_c1;
    have ub_12 := ub_byte_prod ub_b1 ub_c2; have ub_13 := ub_byte_prod ub_b1 ub_c3;
    have ub_20 := ub_byte_prod ub_b2 ub_c0; have ub_21 := ub_byte_prod ub_b2 ub_c1;
    have ub_22 := ub_byte_prod ub_b2 ub_c2; have ub_23 := ub_byte_prod ub_b2 ub_c3;
    have ub_30 := ub_byte_prod ub_b3 ub_c0; have ub_31 := ub_byte_prod ub_b3 ub_c1;
    have ub_32 := ub_byte_prod ub_b3 ub_c2; have ub_33 := ub_byte_prod ub_b3 ub_c3;

    have ub_eb0 := ub_byte_prod ub_b_ext ub_c0; have ub_eb1 := ub_byte_prod ub_b_ext ub_c1;
    have ub_eb2 := ub_byte_prod ub_b_ext ub_c2; have ub_eb3 := ub_byte_prod ub_b_ext ub_c3;
    have ub_ec0 := ub_byte_prod ub_b0 ub_c_ext; have ub_ec1 := ub_byte_prod ub_b1 ub_c_ext;
    have ub_ec2 := ub_byte_prod ub_b2 ub_c_ext; have ub_ec3 := ub_byte_prod ub_b3 ub_c_ext;

    simp [RV32IM.execute_MUL_pure]

    set b : U32b := #v[b0, b1, b2, b3]
    set c : U32b := #v[c0, c1, c2, c3]
    set prod : U64b := #v[p0, p1, p2, p3, p4, p5, p6, p7]

    rw [eq_sub_iff_add_eq] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7
    rw [Nat.mod_eq_of_lt (by omega)] at h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    have h_b_ext : b.extend true = (#v[b0, b1, b2, b3, b_ext, b_ext, b_ext, b_ext] : U64b)
    := by
      have : b.ext true = b_ext.val := by
        subst b_ext
        simp [U32b.ext, h_bse, eq_bmsb, b, ← U32b.msb_3_negative, BitVec.msb_eq_decide]
        clear *- ub_b3; grind
      simp only [U32b.extend]; congr

    have h_c_ext : c.extend false = (#v[c0, c1, c2, c3, c_ext, c_ext, c_ext, c_ext] : U64b)
    := by
      have : c.ext false = c_ext.val := by
        subst c_ext
        simp [U32b.ext, h_cse]
      simp only [U32b.extend]; congr

    have core_mul := core_mul b c true false prod cy0.val cy1.val cy2.val cy3.val cy4.val cy5.val cy6.val cy7.val
    simp [prod, h_b_ext, h_c_ext] at core_mul
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at core_mul
    specialize core_mul h_p0 h_p1 h_p2 h_p3 h_p4 h_p5 h_p6 h_p7

    simp [← U32b.extend_BitVec_extend, h_b_ext, h_c_ext]
    rw [← core_mul, U64_extractLsb_high]
    rfl

  --
  -- Well-formedness
  --

  -- ==================================================================================
  -- Well-formedness: dispatches to the per-opcode spec lemma based on active selector.
  -- ==================================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_MulAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulAir.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    -- Set up assumptions
    have h_wf' := h_wf
    simp [bus_row_wf_asm] at h_wf'
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf'
    -- Main proof
    simp [bus_row_wf_asrt]
    constructor
    -- Program
    . simp [bus_row]
    . constructor
      . -- ALU
        simp [bus_row]
        intro h_mult
        have selectors := selector_breakdown air row h_is_real h_constraints
        have exclusivity := selector_exclusivity air row h_is_real h_constraints
        obtain ⟨h_mul, h_mulh, h_mulhu, h_mulhsu, h_sum⟩ := selectors
        obtain h_mul | h_mul := h_mul
        · obtain h_mulh | h_mulh := h_mulh
          · obtain h_mulhu | h_mulhu := h_mulhu
            . obtain h_mulhsu | h_mulhsu := h_mulhsu
              . exfalso; grind
              . have spec := spec_MULHSU air row h_is_real h_ext h_wf h_constraints h_mulhsu
                simp_all
            . have spec := spec_MULHU air row h_is_real h_ext h_wf h_constraints h_mulhu
              simp_all
          . have spec := spec_MULH air row h_is_real h_ext h_wf h_constraints h_mulh
            simp_all
        . have spec := spec_MUL air row h_is_real h_ext h_wf h_constraints h_mul
          simp_all
      . constructor
        . simp [bus_row, ByteBus.Spec]
          have selectors := selector_exclusivity air row h_is_real h_constraints
          split_ands <;> intro h <;> exfalso <;> grind
        . simp [bus_row]

end MulAir.Spec
