import PicoFV.RV32IM.Constraints.DivRemAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace DivRemAir.Spec

  open RV32IM_Interactions
  open DivRemAir.ConstraintsAndBuses
  open DivRemAir.Interactions
  open DivRemAir.Interpretations

  attribute [-simp]
    Int.tmod_eq_emod
    Int.natCast_tdiv_eq_ediv
    not_and
    Fin.val_pos_iff
    Fin.val_eq_zero_iff

  --
  -- Externals
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selector_breakdown := selector_breakdown air row h_is_real h_constraints
    simp [bus_row_ext_asrt, bus_row, h_is_real] at ⊢
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    clear asm_prog asm_state asm_mem
    simp [bus_row, h_is_real, ByteBus.Spec] at asm_byte
    simp [bus_row_ext_asm, bus_row, h_is_real] at h_ext
    simp [asm_byte]
    obtain ⟨ h_rcm, h_ext ⟩ := h_ext
    obtain h_cs : air.cols.c_0 row 0 < 256 ∧ air.cols.c_1 row 0 < 256 ∧ air.cols.c_2 row 0 < 256
      := by split_ands <;> try { clear *- selector_breakdown h_ext; grind }
    simp [h_cs]
    split_ands <;> try { clear *- selector_breakdown h_ext; grind }
    clear h_ext h_rcm
    intro h_mult u0; clear u0
    have h_c_is_zero : constraint_105 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      *
    ] at h_c_is_zero
    have relevant_constraints
    : constraint_88 air row ∧ constraint_101 air row ∧ constraint_101 air row ∧
      constraint_102 air row ∧ constraint_103 air row ∧ constraint_104 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at relevant_constraints
    simp [relevant_constraints]; clear relevant_constraints
    simp [bus_row, *] at asm_alu
    obtain ⟨ alu_cql, alu_cqh, alu_c, alu_rem, alu_lt ⟩ := asm_alu
    clear alu_cql alu_cqh
    have relevant_constraints
    : constraint_93 air row ∧ constraint_94 air row ∧ constraint_95 air row ∧ constraint_96 air row ∧
      constraint_97 air row ∧ constraint_98 air row ∧ constraint_99 air row ∧ constraint_100 air row ∧
      constraint_106 air row ∧ constraint_107 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at relevant_constraints
    obtain ⟨ b_rem_neg, b_c_neg ⟩
    : constraint_125 air row ∧ constraint_126 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at b_rem_neg b_c_neg
    obtain rem_neg | rem_neg := b_rem_neg <;>
    obtain c_neg | c_neg := b_c_neg <;> simp_all
    . simp [ALUBus.Spec] at alu_c; simp_all
    . simp [ALUBus.Spec] at alu_rem; simp_all
    . simp [ALUBus.Spec] at alu_c alu_rem; simp_all

  --
  -- Auxiliaries
  --

  lemma div_mod_decomposition {a b c : FKB} :
    a.val < 256 → c.val < KB_prime / 256 → (b - c * 256 = a ↔ a = b % 256 ∧ c = b / 256) := by
    intro ub_a ub_c
    constructor
    . intro eq_a
      simp [Fin.ext_iff] at *
      have lb_b : c * 256 ≤ b := by
        by_contra lb_b
        simp [Fin.lt_def, Fin.sub_def, Fin.mul_def] at *
        rw [Nat.mod_eq_of_lt (a := (c : ℕ) * 256) (by omega)] at eq_a lb_b
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

  lemma FKB_add_64 {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c1 c2 c3 c4 c5 c6 c7 c0 cry0 cry1 cry2 cry3 cry4 cry5 cry6 cry7 : FKB}
    (ub_a0 : a0 < 256) (ub_a1 : a1 < 256) (ub_a2 : a2 < 256) (ub_a3 : a3 < 256) (ub_a4 : a4 < 256) (ub_a5 : a5 < 256) (ub_a6 : a6 < 256) (ub_a7 : a7 < 256)
    (ub_b0 : b0 < 256) (ub_b1 : b1 < 256) (ub_b2 : b2 < 256) (ub_b3 : b3 < 256) (ub_b4 : b4 < 256) (ub_b5 : b5 < 256) (ub_b6 : b6 < 256) (ub_b7 : b7 < 256)
    (ub_c0 : c0 < 256) (ub_c1 : c1 < 256) (ub_c2 : c2 < 256) (ub_c3 : c3 < 256) (ub_c4 : c4 < 256) (ub_c5 : c5 < 256) (ub_c6 : c6 < 256) (ub_c7 : c7 < 256)
    (eq_p0 : b0 + c0 - cry0 * 256 = a0)
    (eq_p1 : b1 + c1 - cry1 * 256 + cry0 = a1)
    (eq_p2 : b2 + c2 - cry2 * 256 + cry1 = a2)
    (eq_p3 : b3 + c3 - cry3 * 256 + cry2 = a3)
    (eq_p4 : b4 + c4 - cry4 * 256 + cry3 = a4)
    (eq_p5 : b5 + c5 - cry5 * 256 + cry4 = a5)
    (eq_p6 : b6 + c6 - cry6 * 256 + cry5 = a6)
    (eq_p7 : b7 + c7 - cry7 * 256 + cry6 = a7)
    (b_cr0 : cry0 = 0 ∨ cry0 = 1)
    (b_cr1 : cry1 = 0 ∨ cry1 = 1)
    (b_cr2 : cry2 = 0 ∨ cry2 = 1)
    (b_cr3 : cry3 = 0 ∨ cry3 = 1)
    (b_cr4 : cry4 = 0 ∨ cry4 = 1)
    (b_cr5 : cry5 = 0 ∨ cry5 = 1)
    (b_cr6 : cry6 = 0 ∨ cry6 = 1)
    (b_cr7 : cry7 = 0 ∨ cry7 = 1)
  :
    U64.toBV #v[a0, a1, a2, a3, a4, a5, a6, a7] =
      U64.toBV #v[b0, b1, b2, b3, b4, b5, b6, b7] + U64.toBV #v[c0, c1, c2, c3, c4, c5, c6, c7]
  := by
    rw [add_comm_sub] at eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
    rw [← add_sub_assoc] at eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
    rw [div_mod_decomposition (by assumption) (by clear *- b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7; omega)] at eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
    simp [← BitVec.toNat_inj, U64.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]

    have joins : forall (i : Fin 8) (a b : ℕ), a % (256 ^ i.val) + (b + a / (256 ^ i.val)) % 256 * (256 ^ i.val) = (a + b * (256 ^ i.val)) % (256 ^ (i.val + 1)) := by
      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
    have divs : forall (i : Fin 8) (a b : ℕ), (a + b / (256 ^ i.val)) / 256 = (b + a * (256 ^ i.val)) / (256 ^ (i.val + 1)) := by
      clear *-; intro i a b; fin_cases i <;> norm_num <;> omega
    have j1 := joins 1; have j2 := joins 2; have j3 := joins 3; have j4 := joins 4; have j5 := joins 5; have j6 := joins 6; have j7 := joins 7
    have d1 := divs 1; have d2 := divs 2; have d3 := divs 3; have d4 := divs 4; have d5 := divs 5; have d6 := divs 6; have d7 := divs 7
    simp at j1 j2 j3 j4 j5 j6 j7 d1 d2 d3 d4 d5 d6 d7
    clear joins divs

    simp_all [Fin.val_add]
    repeat rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)]
    rw [j1, d1, j2, d2, j3, d3, j4, d4, j5, d5, j6, d6, j7]
    ring_nf

  --
  -- DIV-REM specification
  --

  lemma spec_DIV_REM
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_div_rem : air.cols.is_div row 0 + air.cols.is_rem row 0 = 1)
  :
    ⟨ U32.toBV #v[air.cols.quotient_0 row 0, air.cols.quotient_1 row 0, air.cols.quotient_2 row 0, air.cols.quotient_3 row 0],
      U32.toBV #v[air.cols.remainder_0 row 0, air.cols.remainder_1 row 0, air.cols.remainder_2 row 0, air.cols.remainder_3 row 0]⟩ =
    RV32IM.execute_DIV_REM_pure (U32.toBV #v[air.cols.b_0 row 0, air.cols.b_1 row 0, air.cols.b_2 row 0, air.cols.b_3 row 0])
                                (U32.toBV #v[air.cols.c_0 row 0, air.cols.c_1 row 0, air.cols.c_2 row 0, air.cols.c_3 row 0]) .DRS
  := by
    obtain ⟨ eq_divu, eq_remu ⟩ : air.cols.is_divu row 0 = 0 ∧ air.cols.is_remu row 0 = 0
      := by
        have selectors := selector_breakdown air row h_is_real h_constraints
        clear *- selectors h_div_rem; grind
    -- Helpers
    obtain ⟨ eq_is_c_0, eq_rem_mult ⟩ := helpers_general air row h_is_real h_constraints
    have helpers := helpers_signed air row h_is_real h_wf h_constraints
    -- External assumptions
    simp [bus_row_ext_asm, bus_row, h_is_real, and_assoc] at h_ext
    obtain ⟨ u0, u1, ub_operands ⟩ := h_ext; clear u0 u1
    have ub_op_hyps : 4 < air.cols.is_divu row 0 * 35 + air.cols.is_remu row 0 * 37 + air.cols.is_div row 0 * 34 + air.cols.is_rem row 0 * 36
      := by
        have selectors := selector_breakdown air row h_is_real h_constraints
        clear *- selectors; omega
    specialize ub_operands ub_op_hyps
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3 ⟩ := ub_operands
    clear ub_op_hyps
    -- Well-formedness assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ u0, asm_alu, asm_byte, u1, u2 ⟩ := h_wf; clear u0 u1 u2
    -- MSB and range assumptions
    simp [bus_row, ByteBus.Spec, h_is_real, and_assoc] at asm_byte
    obtain ⟨ eq_b_msb, ub_b_msb, u0, eq_c_msb, ub_c_msb, u1, eq_rem_msb, ub_rem_msb, u2,
             ub_q0, ub_q1, ub_q2, ub_q3, ub_r0, ub_r1, ub_r2, ub_r3,
             ub_cq0, ub_cq1, ub_cq2, ub_cq3, ub_cq4, ub_cq5, ub_cq6, ub_cq7 ⟩ := asm_byte
    clear u0 u1 u2
    -- ALU assumptions
    simp [bus_row, h_is_real, h_div_rem, eq_divu, eq_remu] at asm_alu
    obtain ⟨ alu_mul_l, alu_mul_h, alu_c, alu_rem, alu_rem_mult ⟩ := asm_alu
    simp [ALUBus.Spec] at alu_mul_l alu_mul_h
    replace alu_mul_l := alu_mul_l.2; replace alu_mul_h := alu_mul_h.2
    -- Other details
    have eq_is_signed : air.cols.is_signed row 0 = 1
      := by simp [Valid_DivRemCols.is_signed, h_div_rem]
    -- Helpers
    specialize helpers eq_is_signed
    obtain ⟨ eq_b_neg, eq_rem_neg, eq_c_neg, eq_rem_alu, eq_c_alu, eq_overflow ⟩ := helpers
    simp [eq_c_alu] at alu_c; simp [eq_rem_alu] at alu_rem; simp [eq_rem_mult] at alu_rem_mult
    clear eq_c_alu eq_rem_alu eq_rem_mult
    -- Main proof
    simp [RV32IM.execute_DIV_REM_pure, RV32IM.execute_DIV_REM_pure_int]
    by_cases h_c_zero :
      U32.toInt
        #v[BitVec.ofNat 8 (air.cols.c_0 row 0), BitVec.ofNat 8 (air.cols.c_1 row 0),
           BitVec.ofNat 8 (air.cols.c_2 row 0), BitVec.ofNat 8 (air.cols.c_3 row 0)] = 0 <;>
    simp [h_c_zero] <;>
    [ skip; have eq_is_c_0_int := h_c_zero ] <;>
    rw [U32_int_eq_0 ub_c0 ub_c1 ub_c2 ub_c3] at h_c_zero <;>
    simp [h_c_zero] at eq_is_c_0 alu_rem_mult
    . -- `c` is zero
      obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3 ⟩ := h_c_zero
      split_ands
      . have relevant_q_constraints :
          constraint_89 air row ∧ constraint_90 air row ∧ constraint_91 air row ∧ constraint_92 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          *
        ] at relevant_q_constraints
        simp [relevant_q_constraints, U32.toBV]
      . simp [eq_c0, eq_c1, eq_c2, eq_c3, RV32IM.execute_MUL_pure] at alu_mul_l
        conv at alu_mul_l => rhs; simp [U32.toBV, BitVec.extend]
        simp [← BitVec.toInt_inj, U32_int_eq_0 ub_cq0 ub_cq1 ub_cq2 ub_cq3] at alu_mul_l
        obtain ⟨ eq_cq0, eq_cq1, eq_cq2, eq_cq3 ⟩ := alu_mul_l
        simp [← BitVec.toInt_inj]
        have range_r := U32.toInt_range #v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0), BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)]
        rw [Int.bmod_eq_of_le (by clear *- range_r; omega) (by clear *- range_r; omega)]
        have relevant_r_constraints :
          constraint_44 air row ∧ constraint_45 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧
          constraint_108 air row ∧ constraint_109 air row ∧ constraint_110 air row ∧ constraint_111 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          *
        ] at relevant_r_constraints
        have carry_zeros :
          air.cols.carry_0 row 0 = 0 ∧ air.cols.carry_1 row 0 = 0 ∧ air.cols.carry_2 row 0 = 0 ∧ air.cols.carry_3 row 0 = 0
          := by omega
        simp [carry_zeros] at relevant_r_constraints
        simp [relevant_r_constraints]
    -- `c` is not zero
    . have alu_mul := RV32IM.combine_MUL_MULH alu_mul_l alu_mul_h
      simp at alu_mul; clear alu_mul_l alu_mul_h
      by_cases h_overflow :
        U32.toInt #v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0),
                     BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)]
          = -2147483648 ∧
        U32.toInt #v[BitVec.ofNat 8 (air.cols.c_0 row 0), BitVec.ofNat 8 (air.cols.c_1 row 0),
                     BitVec.ofNat 8 (air.cols.c_2 row 0), BitVec.ofNat 8 (air.cols.c_3 row 0)]
          = -1 <;>
      simp [h_overflow] <;>
      rw [U32_int_eq_minInt ub_b0 ub_b1 ub_b2 ub_b3, U32_int_eq_neg_one ub_c0 ub_c1 ub_c2 ub_c3] at h_overflow
      -- Overflow
      . have h_rem_char : constraint_69 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
        ] at h_rem_char
        simp [h_overflow] at eq_b_msb alu_mul eq_b_neg eq_c_neg h_rem_char eq_overflow
        simp [eq_b_neg] at h_rem_char; rw [eq_comm (a := 1)] at h_rem_char
        have relevant_constraints :
          constraint_44 air row ∧ constraint_45 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧
          constraint_50 air row ∧ constraint_53 air row ∧ constraint_56 air row ∧ constraint_59 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          eq_overflow
        ] at relevant_constraints
        obtain ⟨ eq_p0, eq_p1, eq_p2, eq_p3, eq_p4, eq_p5, eq_p6, eq_p7 ⟩ := relevant_constraints
        symm at eq_p0 eq_p1 eq_p2 eq_p3
        simp [h_overflow] at eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
        suffices h_eq :
          air.cols.quotient_0 row 0 = 0 ∧ air.cols.quotient_1 row 0 = 0 ∧ air.cols.quotient_2 row 0 = 0 ∧ air.cols.quotient_3 row 0 = 128 ∧
          air.cols.remainder_0 row 0 = 0 ∧ air.cols.remainder_1 row 0 = 0 ∧ air.cols.remainder_2 row 0 = 0 ∧ air.cols.remainder_3 row 0 = 0
        . simp [h_eq, U32.toBV]
        . have relevant_constraints :
            constraint_108 air row ∧ constraint_109 air row ∧ constraint_110 air row ∧ constraint_111 air row ∧
            constraint_112 air row ∧ constraint_113 air row ∧ constraint_114 air row ∧ constraint_115 air row
          := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
          simp [
            pico_encapsulation,
            constraint_and_interaction_simplification,
            sub_eq_zero,
          ] at relevant_constraints
          obtain ⟨ b_cr0, b_cr1, b_cr2, b_cr3, b_cr4, b_cr5, b_cr6, b_cr7 ⟩ := relevant_constraints
          clear *- eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
                   ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cq4 ub_cq5 ub_cq6 ub_cq7
                   ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3
                   b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7
                   alu_mul eq_rem_neg h_rem_char
          have ub_rem_neg : air.cols.rem_neg row 0 * 255 < 256 := by clear *- eq_rem_neg; grind
          have alu_sum :=
            @FKB_add_64
              (eq_p0 := eq_p0) (eq_p1 := eq_p1) (eq_p2 := eq_p2) (eq_p3 := eq_p3)
              (eq_p4 := eq_p4) (eq_p5 := eq_p5) (eq_p6 := eq_p6) (eq_p7 := eq_p7)
          specialize alu_sum (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          specialize alu_sum ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cq4 ub_cq5 ub_cq6 ub_cq7 ub_r0 ub_r1 ub_r2 ub_r3 ub_rem_neg ub_rem_neg ub_rem_neg ub_rem_neg
          specialize alu_sum b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7
          clear b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7 eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
          simp [← BitVec.toNat_inj, U64.toNat] at alu_sum
          repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_sum
          have eq_ext_c :
            U32.extend #v[255#8, 255#8, 255#8, 255#8] true = #v[255, 255, 255, 255, 255, 255, 255, 255]
            := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
          split_ifs at eq_rem_neg with h_rem_neg
          . simp [eq_rem_neg] at alu_sum h_rem_char
            obtain eq_rs :
              air.cols.remainder_0 row 0 = 0 ∧ air.cols.remainder_1 row 0 = 0 ∧ air.cols.remainder_2 row 0 = 0 ∧ air.cols.remainder_3 row 0 = 0
            := by clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_rem_char; omega
            simp [eq_rs] at alu_sum ⊢
            obtain eq_cqs :
              air.cols.c_times_quotient_0 row 0 = 0 ∧ air.cols.c_times_quotient_1 row 0 = 0 ∧ air.cols.c_times_quotient_2 row 0 = 0 ∧ air.cols.c_times_quotient_3 row 0 = 128 ∧
              air.cols.c_times_quotient_4 row 0 = 0 ∧ air.cols.c_times_quotient_5 row 0 = 0 ∧ air.cols.c_times_quotient_6 row 0 = 0 ∧ air.cols.c_times_quotient_7 row 0 = 0
              := by clear *- ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cq4 ub_cq5 ub_cq6 ub_cq7 alu_sum; omega
            by_cases h_msb_q3 : 128 ≤ (air.cols.quotient_3 row 0).val % 256
            . have eq_ext_q :
                U32.extend #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)] true =
                #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0), 255, 255, 255, 255]
                := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_msb_q3]
              clear alu_sum
              simp [eq_ext_q, eq_ext_c, eq_cqs] at alu_mul
              -- Deep recursion if `BitVec.toNat_mul` not disabled
              simp [← BitVec.toNat_inj, -BitVec.toNat_mul] at alu_mul
              repeat rw [BitVec.toNat_mul] at alu_mul
              simp [U64.toNat] at alu_mul
              repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_mul
              ring_nf at alu_mul
              have : (340282366841710300930663525768809676800 + (air.cols.quotient_0 row 0).val * 18446744073709551615 + (air.cols.quotient_1 row 0) * 4722366482869645213440 + (air.cols.quotient_2 row 0) * 1208925819614629174640640 + (air.cols.quotient_3 row 0) * 309485009821345068708003840) % 18446744073709551616 =
                      4294967296 - ((air.cols.quotient_0 row 0).val + (air.cols.quotient_1 row 0) * 256 + (air.cols.quotient_2 row 0) * 65536 + (air.cols.quotient_3 row 0) * 16777216)
                := by clear *- ub_q0 ub_q1 ub_q2 ub_q3; omega
              rw [this] at alu_mul; clear this
              omega
            . have eq_ext_q :
                U32.extend #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)] true =
                #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0), 0, 0, 0, 0]
                := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_msb_q3]
              clear alu_sum
              simp [eq_ext_q, eq_ext_c, eq_cqs] at alu_mul
              -- Deep recursion if `BitVec.toNat_mul` not disabled
              simp [← BitVec.toNat_inj, -BitVec.toNat_mul] at alu_mul
              repeat rw [BitVec.toNat_mul] at alu_mul
              simp [U64.toNat] at alu_mul
              repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_mul
              ring_nf at alu_mul
              rw [Nat.mod_eq_of_lt (by clear *- ub_q3; omega)] at h_msb_q3; simp at h_msb_q3
              by_cases h_q_zero : air.cols.quotient_0 row 0 = 0 ∧ air.cols.quotient_1 row 0 = 0 ∧ air.cols.quotient_2 row 0 = 0 ∧ air.cols.quotient_3 row 0 = 0
              . simp [h_q_zero] at alu_mul
              . have : ((air.cols.quotient_0 row 0).val * 18446744073709551615 + (air.cols.quotient_1 row 0) * 4722366482869645213440 + (air.cols.quotient_2 row 0) * 1208925819614629174640640 + (air.cols.quotient_3 row 0) * 309485009821345068708003840) % 18446744073709551616 =
                        18446744073709551616 - ((air.cols.quotient_0 row 0).val + (air.cols.quotient_1 row 0) * 256 + (air.cols.quotient_2 row 0) * 65536 + (air.cols.quotient_3 row 0) * 16777216)
                  := by clear *- ub_q0 ub_q1 ub_q2 ub_q3 h_msb_q3 h_q_zero; omega
                rw [this] at alu_mul; clear this
                omega
          . simp at h_rem_neg; simp [eq_rem_neg] at alu_sum
            clear h_rem_char; ring_nf at alu_sum
            replace alu_sum :
              (air.cols.c_times_quotient_0 row 0).val + (air.cols.c_times_quotient_1 row 0) * 256 + (air.cols.c_times_quotient_2 row 0) * 65536 + (air.cols.c_times_quotient_3 row 0) * 16777216 +
              (air.cols.c_times_quotient_4 row 0) * 4294967296 + (air.cols.c_times_quotient_5 row 0) * 1099511627776 + (air.cols.c_times_quotient_6 row 0) * 281474976710656 + (air.cols.c_times_quotient_7 row 0) * 72057594037927936 +
              (air.cols.remainder_0 row 0) + (air.cols.remainder_1 row 0) * 256 + (air.cols.remainder_2 row 0) * 65536 + (air.cols.remainder_3 row 0) * 16777216
                = 6442450944
            := by omega
            have eq_cqhs : (air.cols.c_times_quotient_4 row 0 = 0 ∨ air.cols.c_times_quotient_4 row 0 = 1) ∧ air.cols.c_times_quotient_5 row 0 = 0 ∧ air.cols.c_times_quotient_6 row 0 = 0 ∧ air.cols.c_times_quotient_7 row 0 = 0
              := by clear alu_mul; omega
            simp [eq_cqhs] at alu_mul alu_sum
            replace eq_cqhs := eq_cqhs.1; obtain eq_cq4 | eq_cq4 := eq_cqhs
            . simp [eq_cq4] at alu_mul alu_sum
              have : 128 ≤ air.cols.c_times_quotient_3 row 0
                := by clear alu_mul; omega
              by_cases h_msb_q3 : 128 ≤ (air.cols.quotient_3 row 0).val % 256
              . have eq_ext_q :
                  U32.extend #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)] true =
                  #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0), 255, 255, 255, 255]
                  := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_msb_q3]
                simp [eq_ext_q, eq_ext_c] at alu_mul
                -- Deep recursion if `BitVec.toNat_mul` not disabled
                simp [← BitVec.toNat_inj, -BitVec.toNat_mul] at alu_mul
                repeat rw [BitVec.toNat_mul] at alu_mul
                simp [U64.toNat] at alu_mul
                repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_mul
                ring_nf at alu_mul
                rw [Nat.mod_eq_of_lt (by clear *- ub_q3; omega)] at h_msb_q3
                have : (340282366841710300930663525768809676800 + (air.cols.quotient_0 row 0).val * 18446744073709551615 + (air.cols.quotient_1 row 0) * 4722366482869645213440 + (air.cols.quotient_2 row 0) * 1208925819614629174640640 + (air.cols.quotient_3 row 0) * 309485009821345068708003840) % 18446744073709551616 =
                       4294967296 - ((air.cols.quotient_0 row 0).val + (air.cols.quotient_1 row 0) * 256 + (air.cols.quotient_2 row 0) * 65536 + (air.cols.quotient_3 row 0) * 16777216)
                  := by clear *- ub_q0 ub_q1 ub_q2 ub_q3; omega
                rw [this] at alu_mul; clear this
                omega
              . have eq_ext_q :
                  U32.extend #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)] true =
                  #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0), 0, 0, 0, 0]
                  := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_msb_q3]
                simp [eq_ext_q, eq_ext_c] at alu_mul
                -- Deep recursion if `BitVec.toNat_mul` not disabled
                simp [← BitVec.toNat_inj, -BitVec.toNat_mul] at alu_mul
                repeat rw [BitVec.toNat_mul] at alu_mul
                simp [U64.toNat] at alu_mul
                repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_mul
                ring_nf at alu_mul
                rw [Nat.mod_eq_of_lt (by clear *- ub_q3; omega)] at h_msb_q3; simp at h_msb_q3
                by_cases h_q_zero : air.cols.quotient_0 row 0 = 0 ∧ air.cols.quotient_1 row 0 = 0 ∧ air.cols.quotient_2 row 0 = 0 ∧ air.cols.quotient_3 row 0 = 0
                . simp [h_q_zero] at alu_mul
                  omega
                . have : ((air.cols.quotient_0 row 0).val * 18446744073709551615 + (air.cols.quotient_1 row 0) * 4722366482869645213440 + (air.cols.quotient_2 row 0) * 1208925819614629174640640 + (air.cols.quotient_3 row 0) * 309485009821345068708003840) % 18446744073709551616 =
                          18446744073709551616 - ((air.cols.quotient_0 row 0).val + (air.cols.quotient_1 row 0) * 256 + (air.cols.quotient_2 row 0) * 65536 + (air.cols.quotient_3 row 0) * 16777216)
                    := by clear *- ub_q0 ub_q1 ub_q2 ub_q3 h_msb_q3 h_q_zero; omega
                  rw [this] at alu_mul; clear this
                  omega
            . simp [eq_cq4] at alu_mul alu_sum
              have eqs : air.cols.c_times_quotient_0 row 0 = 0 ∧ air.cols.c_times_quotient_1 row 0 = 0 ∧ air.cols.c_times_quotient_2 row 0 = 0 ∧ air.cols.c_times_quotient_3 row 0 = 0 ∧
                         air.cols.remainder_0 row 0 = 0 ∧ air.cols.remainder_1 row 0 = 0 ∧ air.cols.remainder_2 row 0 = 0 ∧ air.cols.remainder_3 row 0 = 128
                := by clear alu_mul; omega
              simp [eqs] at alu_mul ⊢ ; clear alu_sum
              by_cases h_msb_q3 : 128 ≤ (air.cols.quotient_3 row 0).val % 256
              . have eq_ext_q :
                  U32.extend #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)] true =
                  #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0), 255, 255, 255, 255]
                  := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_msb_q3]
                simp [eq_ext_q, eq_ext_c] at alu_mul
                -- Deep recursion if `BitVec.toNat_mul` not disabled
                simp [← BitVec.toNat_inj, -BitVec.toNat_mul] at alu_mul
                repeat rw [BitVec.toNat_mul] at alu_mul
                simp [U64.toNat] at alu_mul
                repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_mul
                ring_nf at alu_mul
                rw [Nat.mod_eq_of_lt (by clear *- ub_q3; omega)] at h_msb_q3
                have : (340282366841710300930663525768809676800 + (air.cols.quotient_0 row 0).val * 18446744073709551615 + (air.cols.quotient_1 row 0) * 4722366482869645213440 + (air.cols.quotient_2 row 0) * 1208925819614629174640640 + (air.cols.quotient_3 row 0) * 309485009821345068708003840) % 18446744073709551616 =
                       4294967296 - ((air.cols.quotient_0 row 0).val + (air.cols.quotient_1 row 0) * 256 + (air.cols.quotient_2 row 0) * 65536 + (air.cols.quotient_3 row 0) * 16777216)
                := by clear *- ub_q0 ub_q1 ub_q2 ub_q3; omega
                rw [this] at alu_mul; clear this
                clear *- alu_mul ub_q0 ub_q1 ub_q2 ub_q3 h_msb_q3
                omega
              . have eq_ext_q :
                  U32.extend #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)] true =
                  #v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0), 0, 0, 0, 0]
                  := by simp [U32.extend, U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_msb_q3]
                simp [eq_ext_q, eq_ext_c] at alu_mul
                -- Deep recursion if `BitVec.toNat_mul` not disabled
                simp [← BitVec.toNat_inj, -BitVec.toNat_mul] at alu_mul
                repeat rw [BitVec.toNat_mul] at alu_mul
                simp [U64.toNat] at alu_mul
                repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at alu_mul
                ring_nf at alu_mul
                rw [Nat.mod_eq_of_lt (by clear *- ub_q3; omega)] at h_msb_q3; simp at h_msb_q3
                by_cases h_q_zero : air.cols.quotient_0 row 0 = 0 ∧ air.cols.quotient_1 row 0 = 0 ∧ air.cols.quotient_2 row 0 = 0 ∧ air.cols.quotient_3 row 0 = 0
                . simp [h_q_zero] at alu_mul
                . have : ((air.cols.quotient_0 row 0).val * 18446744073709551615 + (air.cols.quotient_1 row 0) * 4722366482869645213440 + (air.cols.quotient_2 row 0) * 1208925819614629174640640 + (air.cols.quotient_3 row 0) * 309485009821345068708003840) % 18446744073709551616 =
                          18446744073709551616 - ((air.cols.quotient_0 row 0).val + (air.cols.quotient_1 row 0) * 256 + (air.cols.quotient_2 row 0) * 65536 + (air.cols.quotient_3 row 0) * 16777216)
                  := by clear *- ub_q0 ub_q1 ub_q2 ub_q3 h_msb_q3 h_q_zero; omega
                  rw [this] at alu_mul; clear this
                  omega
      -- No overflow
      . rw [if_neg (by clear *- h_overflow; omega)] at eq_overflow
        have relevant_constraints :
          constraint_44 air row ∧ constraint_45 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧
          constraint_48 air row ∧ constraint_49 air row ∧ constraint_51 air row ∧ constraint_52 air row ∧
          constraint_54 air row ∧ constraint_55 air row ∧ constraint_57 air row ∧ constraint_58 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          eq_overflow
        ] at relevant_constraints
        set b_ext : FKB := ⟨ U32.ext #v[air.cols.b_0 row 0, air.cols.b_1 row 0, air.cols.b_2 row 0, air.cols.b_3 row 0] true, by clear *-; have := @U32.ext_le_255; grind⟩
        have eq_b_neg_prod : air.cols.b_neg row 0 * 255 = b_ext
        := by
          subst b_ext; rw [eq_b_neg]; clear *- ub_b3
          simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
          simp [Fin.ext_iff]; split_ifs <;> simp <;> omega
        have ub_b_ext : b_ext < 256 := by rw [← eq_b_neg_prod]; clear *- eq_b_neg; grind
        set r_ext : FKB := ⟨ U32.ext #v[air.cols.remainder_0 row 0, air.cols.remainder_1 row 0, air.cols.remainder_2 row 0, air.cols.remainder_3 row 0] true, by clear *-; have := @U32.ext_le_255; grind⟩
        have eq_rem_neg_prod : air.cols.rem_neg row 0 * 255 = r_ext
        := by
          subst r_ext; rw [eq_rem_neg]; clear *- ub_r3
          simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
          simp [Fin.ext_iff]; split_ifs <;> simp <;> omega
        have ub_r_ext : r_ext < 256 := by rw [← eq_rem_neg_prod]; clear *- eq_rem_neg; grind
        simp [eq_rem_neg_prod, eq_b_neg] at relevant_constraints
        obtain ⟨ eq_p0, eq_p1, eq_p2, eq_p3, eq_p4p, eq_p4n, eq_p5p, eq_p5n, eq_p6p, eq_p6n, eq_p7p, eq_p7n ⟩ := relevant_constraints
        symm at eq_p0 eq_p1 eq_p2 eq_p3
        have ⟨ eq_p4, eq_p5, eq_p6, eq_p7 ⟩ :
          air.cols.c_times_quotient_4 row 0 + r_ext - air.cols.carry_4 row 0 * 256 + air.cols.carry_3 row 0 = b_ext ∧
          air.cols.c_times_quotient_5 row 0 + r_ext - air.cols.carry_5 row 0 * 256 + air.cols.carry_4 row 0 = b_ext ∧
          air.cols.c_times_quotient_6 row 0 + r_ext - air.cols.carry_6 row 0 * 256 + air.cols.carry_5 row 0 = b_ext ∧
          air.cols.c_times_quotient_7 row 0 + r_ext - air.cols.carry_7 row 0 * 256 + air.cols.carry_6 row 0 = b_ext
        := by
          clear *- ub_b3 eq_p4p eq_p5p eq_p6p eq_p7p eq_p4n eq_p5n eq_p6n eq_p7n
          subst b_ext; simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
          split_ifs with h_if <;> grind
        clear eq_p4p eq_p5p eq_p6p eq_p7p eq_p4n eq_p5n eq_p6n eq_p7n
        have relevant_constraints :
          constraint_108 air row ∧ constraint_109 air row ∧ constraint_110 air row ∧ constraint_111 air row ∧
          constraint_112 air row ∧ constraint_113 air row ∧ constraint_114 air row ∧ constraint_115 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
        ] at relevant_constraints
        obtain ⟨ b_cr0, b_cr1, b_cr2, b_cr3, b_cr4, b_cr5, b_cr6, b_cr7 ⟩ := relevant_constraints
        have alu_sum :=
          @FKB_add_64
            (eq_p0 := eq_p0) (eq_p1 := eq_p1) (eq_p2 := eq_p2) (eq_p3 := eq_p3)
            (eq_p4 := eq_p4) (eq_p5 := eq_p5) (eq_p6 := eq_p6) (eq_p7 := eq_p7)
        specialize alu_sum ub_b0 ub_b1 ub_b2 ub_b3 ub_b_ext ub_b_ext ub_b_ext ub_b_ext
        specialize alu_sum ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cq4 ub_cq5 ub_cq6 ub_cq7 ub_r0 ub_r1 ub_r2 ub_r3 ub_r_ext ub_r_ext ub_r_ext ub_r_ext
        specialize alu_sum b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7
        clear b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7 eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
        replace alu_sum :
          (U32.extend
            #v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0),
               BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)]
            true).toBV =
            U64.toBV
              #v[BitVec.ofNat 8 (air.cols.c_times_quotient_0 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_1 row 0),
                 BitVec.ofNat 8 (air.cols.c_times_quotient_2 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_3 row 0),
                 BitVec.ofNat 8 (air.cols.c_times_quotient_4 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_5 row 0),
                 BitVec.ofNat 8 (air.cols.c_times_quotient_6 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_7 row 0)] +
              (U32.extend
                 #v[BitVec.ofNat 8 (air.cols.remainder_0 row 0), BitVec.ofNat 8 (air.cols.remainder_1 row 0),
                    BitVec.ofNat 8 (air.cols.remainder_2 row 0), BitVec.ofNat 8 (air.cols.remainder_3 row 0)] true).toBV
          := by clear *- alu_sum; subst b_ext r_ext; simpa [U32.extend]
        clear eq_b_neg_prod eq_rem_neg_prod ub_r_ext ub_b_ext b_ext r_ext
        simp [← BitVec.toInt_inj]
        have range_b := U32.toInt_range (#v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0), BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)])
        have range_c := U32.toInt_range (#v[BitVec.ofNat 8 (air.cols.c_0 row 0), BitVec.ofNat 8 (air.cols.c_1 row 0), BitVec.ofNat 8 (air.cols.c_2 row 0), BitVec.ofNat 8 (air.cols.c_3 row 0)])
        have range_q := U32.toInt_range (#v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)])
        have range_r := U32.toInt_range (#v[BitVec.ofNat 8 (air.cols.remainder_0 row 0), BitVec.ofNat 8 (air.cols.remainder_1 row 0), BitVec.ofNat 8 (air.cols.remainder_2 row 0), BitVec.ofNat 8 (air.cols.remainder_3 row 0)])
        have range_tmod := Int.tmod_range_32 range_b range_c
        have range_tdiv := @Int.tdiv_range_32
                             (c := U32.toInt #v[BitVec.ofNat 8 (air.cols.c_0 row 0), BitVec.ofNat 8 (air.cols.c_1 row 0), BitVec.ofNat 8 (air.cols.c_2 row 0), BitVec.ofNat 8 (air.cols.c_3 row 0)])
                             (range_b := range_b)
        specialize range_tdiv eq_is_c_0_int
        specialize range_tdiv
          (by
            clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3 h_overflow
            intro h_eq; apply h_overflow; clear h_overflow
            simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide] at h_eq
            obtain ⟨ h_eq_b, h_eq_c ⟩ := h_eq
            split_ifs at h_eq_b with h_b
            . split_ifs at h_eq_c with h_c
              . simp [U32.toNat] at h_eq_b h_eq_c
                omega
              . simp [U32.toNat] at h_eq_c
                omega
            . simp [U32.toNat] at h_eq_b
              omega
          )
        rw [Int.bmod_eq_of_le (by clear *- range_tdiv; tauto) (by clear *- range_tdiv; tauto)]
        rw [Int.bmod_eq_of_le (by clear *- range_tmod; tauto) (by clear *- range_tmod; tauto)]
        -- Moving to the three conditions
        rw [Int.tdiv_tmod_unique_full eq_is_c_0_int]
        -- First condition
        have cond_1 :
          U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.b_0 row 0), BitVec.ofNat 8 ↑(air.cols.b_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.b_2 row 0), BitVec.ofNat 8 ↑(air.cols.b_3 row 0)] =
          U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.quotient_0 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.quotient_2 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_3 row 0)] *
          U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] +
          U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)]
        := by
          rw [alu_mul] at alu_sum
          clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
                   ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3
                   alu_sum range_b range_c range_q range_r
          simp [← BitVec.toInt_inj] at alu_sum; rw [alu_sum]
          rw [Int.bmod_eq_of_le] <;> simp <;> nlinarith
        conv => arg 1; simp [cond_1]
        -- Second condition
        have cond_2 :
          |U32.toInt
            #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)]| <
            |U32.toInt
              #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
                 BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)]|
        := by
          by_cases h_r_max :
            U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0),
                         BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)] = -2147483648
          . exfalso
            clear alu_sum alu_mul range_tmod range_tdiv range_r
            simp [h_r_max] at cond_1
            rw [U32_int_eq_minInt ub_r0 ub_r1 ub_r2 ub_r3] at h_r_max
            simp [h_r_max] at alu_rem eq_rem_msb
            have relevant_constraints :
              constraint_101 air row ∧ constraint_102 air row ∧ constraint_103 air row ∧ constraint_104 air row
            := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
            simp [
              pico_encapsulation,
              constraint_and_interaction_simplification,
              sub_eq_zero,
              eq_is_c_0,
            ] at relevant_constraints
            simp [ALUBus.Spec, relevant_constraints] at alu_rem alu_rem_mult
            obtain ⟨ ⟨ ub_ar0, ub_ar1, ub_ar2, ub_ar3 ⟩, alu_rem ⟩ := alu_rem
            (conv at alu_rem_mult => lhs; simp [U32.toBV]); simp at alu_rem_mult
            have eq_ar : air.cols.abs_remainder_0 row 0 = 0 ∧ air.cols.abs_remainder_1 row 0 = 0 ∧ air.cols.abs_remainder_2 row 0 = 0 ∧ air.cols.abs_remainder_3 row 0 = 128
            := by
              clear *- ub_ar0 ub_ar1 ub_ar2 ub_ar3 alu_rem
              simp [← BitVec.toInt_inj, U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide] at alu_rem
              simp [U32.toNat] at alu_rem
              repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at alu_rem
              split_ifs at alu_rem <;> grind
            simp [eq_ar] at alu_rem_mult
            clear alu_rem h_r_max
            conv at alu_rem_mult => arg 1; simp [U32.toNat]
            have h_msb_c : 128 ≤ (air.cols.c_3 row 0).val
            := by
              split_ifs at eq_c_msb with h_eq_msb_c <;> [ skip; (clear *- h_eq_msb_c; omega) ]
              have relevant_constraints :
                constraint_93 air row ∧ constraint_95 air row ∧ constraint_97 air row ∧ constraint_99 air row
              := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
              simp [
                pico_encapsulation,
                constraint_and_interaction_simplification,
                sub_eq_zero,
              ] at relevant_constraints
              simp [U32.toNat] at alu_rem_mult
              rw [if_pos (by omega)] at eq_c_neg
              omega
            have h_msb_ac : 128 ≤ (air.cols.abs_c_3 row 0).val
              := by simp [U32.toNat] at alu_rem_mult; omega
            simp [ALUBus.Spec, ← BitVec.toNat_inj, U32.toNat, ub_c0, ub_c1, ub_c2, ub_c3, h_msb_c] at alu_c
            obtain ⟨ ⟨ ub_ac0, ub_ac1, ub_ac2, ub_ac3 ⟩, alu_c ⟩ := alu_c
            repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)] at alu_c
            have eqs_c_ac :
              air.cols.c_0 row 0 = 0 ∧ air.cols.c_1 row 0 = 0 ∧ air.cols.c_2 row 0 = 0 ∧ air.cols.c_3 row 0 = 128 ∧
              air.cols.abs_c_0 row 0 = 0 ∧ air.cols.abs_c_1 row 0 = 0 ∧ air.cols.abs_c_2 row 0 = 0 ∧ air.cols.abs_c_3 row 0 = 128
            := by
              clear *- ub_c0 ub_c1 ub_c2 ub_c3 ub_ac0 ub_ac1 ub_ac2 ub_ac3 alu_c h_msb_c h_msb_ac
              omega
            simp [eqs_c_ac, U32.toNat] at alu_rem_mult
          . by_cases h_c_max :
              U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
                           BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] = -2147483648
            . rw [h_c_max]; simp; clear *- range_r h_r_max
              obtain ⟨ r, eq_r ⟩ : ∃ r, r = U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)] := by simp
              rw [← eq_r] at range_r h_r_max ⊢; clear eq_r
              grind
            . simp [ALUBus.Spec] at alu_rem_mult
              simp [U32.toBV] at alu_rem_mult
              suffices :
                ((U32.toNat
                  #v[BitVec.ofNat 8 ↑(air.cols.abs_remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.abs_remainder_1 row 0),
                     BitVec.ofNat 8 ↑(air.cols.abs_remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.abs_remainder_3 row 0)]) : ℤ) =
                  |U32.toInt
                    #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0),
                       BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)]| ∧
                ((U32.toNat
                  #v[BitVec.ofNat 8 ↑(air.cols.max_abs_c_or_1_0 row 0), BitVec.ofNat 8 ↑(air.cols.max_abs_c_or_1_1 row 0),
                     BitVec.ofNat 8 ↑(air.cols.max_abs_c_or_1_2 row 0), BitVec.ofNat 8 ↑(air.cols.max_abs_c_or_1_3 row 0)]) : ℤ) =
                |U32.toInt
                  #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
                     BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)]|
              . simp [← this.1, ← this.2]
                exact alu_rem_mult
              . clear alu_rem_mult range_tmod range_tdiv eq_overflow
                have relevant_constraints :
                  constraint_93 air row ∧ constraint_94 air row ∧ constraint_95 air row ∧ constraint_96 air row ∧
                  constraint_97 air row ∧ constraint_98 air row ∧ constraint_99 air row ∧ constraint_100 air row ∧
                  constraint_101 air row ∧ constraint_102 air row ∧ constraint_103 air row ∧ constraint_104 air row
                := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
                simp [
                  pico_encapsulation,
                  constraint_and_interaction_simplification,
                  sub_eq_zero,
                  eq_is_c_0
                ] at relevant_constraints
                simp [eq_c_neg, eq_rem_neg] at relevant_constraints
                obtain ⟨ eqp_ac0, eqp_ar0, eqp_ac1, eqp_ar1, eqp_ac2, eqp_ar2, eqp_ac3, eqp_ar3, eq_max_0, eq_max_1, eq_max_2, eq_max_3 ⟩ := relevant_constraints
                rw [show (128 ≤ (air.cols.c_3 row 0).val) = ¬ ((air.cols.c_3 row 0).val < 128) by simp] at eqp_ac0 eqp_ac1 eqp_ac2 eqp_ac3
                rw [show (128 ≤ (air.cols.remainder_3 row 0).val) = ¬ ((air.cols.remainder_3 row 0).val < 128) by simp] at eqp_ar0 eqp_ar1 eqp_ar2 eqp_ar3
                rw [← imp_iff_not_or] at eqp_ac0 eqp_ar0 eqp_ac1 eqp_ar1 eqp_ac2 eqp_ar2 eqp_ac3 eqp_ar3
                rw [eq_comm] at eqp_ac0 eqp_ar0 eqp_ac1 eqp_ar1 eqp_ac2 eqp_ar2 eqp_ac3 eqp_ar3
                obtain ⟨ h_no_mod_c3, h_no_mod_r3 ⟩ :
                  (air.cols.c_3 row 0).val % 256 = (air.cols.c_3 row 0).val ∧
                  (air.cols.remainder_3 row 0).val % 256 = (air.cols.remainder_3 row 0).val
                  := by clear *- ub_c3 ub_r3; omega
                simp [Int.abs_cases]
                simp [← U32.not_negative_toInt, ← U32.msb_3_negative,
                      BitVec.msb_eq_decide, h_no_mod_c3, h_no_mod_r3]
                replace alu_c :
                  128 ≤ (air.cols.c_3 row 0).val →
                    air.cols.abs_c_0 row 0 < 256 ∧ air.cols.abs_c_1 row 0 < 256 ∧ air.cols.abs_c_2 row 0 < 256 ∧ air.cols.abs_c_3 row 0 < 256 ∧
                    U32.toInt #v[(air.cols.abs_c_0 row 0), (air.cols.abs_c_1 row 0), (air.cols.abs_c_2 row 0), (air.cols.abs_c_3 row 0)]
                      =
                    - U32.toInt #v[(air.cols.c_0 row 0), (air.cols.c_1 row 0), (air.cols.c_2 row 0), (air.cols.c_3 row 0)]
                := by
                  intro h_c_is_neg
                  specialize alu_c h_c_is_neg
                  simp [ALUBus.Spec] at alu_c
                  obtain ⟨ u0, u1, u2, u3, ub_ac0, ub_ac1, ub_ac2, ub_ac3 ⟩ := alu_c.1
                  clear u0 u1 u2 u3; simp [ub_ac0, ub_ac1, ub_ac2, ub_ac3]
                  replace alu_c := alu_c.2
                  simp [← BitVec.toInt_inj] at alu_c; symm at alu_c
                  conv at alu_c => rhs; simp [U32.toInt, U32.negative, U32.toNat]
                  have range_ac :=
                    U32.toInt_range #v[BitVec.ofNat 8 (air.cols.abs_c_0 row 0), BitVec.ofNat 8 (air.cols.abs_c_1 row 0),
                                       BitVec.ofNat 8 (air.cols.abs_c_2 row 0), BitVec.ofNat 8 (air.cols.abs_c_3 row 0)]
                  clear *- alu_c range_c range_ac alu_sum alu_mul h_c_max alu_sum
                  rw [alu_mul] at alu_sum; clear alu_mul
                  simp [Int.bmod_def] at alu_c
                  rw [if_pos] at alu_c
                  . omega
                  . by_contra h_if_neg
                    simp [h_if_neg] at alu_c
                    omega
                replace alu_rem :
                  128 ≤ (air.cols.remainder_3 row 0).val →
                    air.cols.abs_remainder_0 row 0 < 256 ∧ air.cols.abs_remainder_1 row 0 < 256 ∧ air.cols.abs_remainder_2 row 0 < 256 ∧ air.cols.abs_remainder_3 row 0 < 256 ∧
                    U32.toInt #v[(air.cols.abs_remainder_0 row 0), (air.cols.abs_remainder_1 row 0), (air.cols.abs_remainder_2 row 0), (air.cols.abs_remainder_3 row 0)]
                      =
                    - U32.toInt #v[(air.cols.remainder_0 row 0), (air.cols.remainder_1 row 0), (air.cols.remainder_2 row 0), (air.cols.remainder_3 row 0)]
                := by
                  intro h_rem_is_neg
                  specialize alu_rem h_rem_is_neg
                  simp [ALUBus.Spec] at alu_rem
                  obtain ⟨ u0, u1, u2, u3, ub_ar0, ub_ar1, ub_ar2, ub_ar3 ⟩ := alu_rem.1
                  clear u0 u1 u2 u3; simp [ub_ar0, ub_ar1, ub_ar2, ub_ar3]
                  replace alu_rem := alu_rem.2
                  simp [← BitVec.toInt_inj] at alu_rem; symm at alu_rem
                  conv at alu_rem => rhs; simp [U32.toInt, U32.negative, U32.toNat]
                  have range_ar :=
                    U32.toInt_range #v[BitVec.ofNat 8 (air.cols.abs_remainder_0 row 0), BitVec.ofNat 8 (air.cols.abs_remainder_1 row 0),
                                       BitVec.ofNat 8 (air.cols.abs_remainder_2 row 0), BitVec.ofNat 8 (air.cols.abs_remainder_3 row 0)]
                  clear *- alu_rem range_r range_ar alu_sum alu_mul h_r_max alu_sum
                  rw [alu_mul] at alu_sum; clear alu_mul
                  simp [Int.bmod_def] at alu_rem
                  rw [if_pos] at alu_rem
                  . omega
                  . by_contra h_if_neg
                    simp [h_if_neg] at alu_rem
                    omega
                split_ifs with h_rem_is_neg h_c_is_neg h_c_is_neg
                . simp [eq_max_0, eq_max_1, eq_max_2, eq_max_3]
                  simp [h_c_is_neg] at eqp_ac0 eqp_ac1 eqp_ac2 eqp_ac3
                  simp [h_rem_is_neg] at eqp_ar0 eqp_ar1 eqp_ar2 eqp_ar3
                  simp [eqp_ac0, eqp_ac1, eqp_ac2, eqp_ac3, eqp_ar0, eqp_ar1, eqp_ar2, eqp_ar3]
                  simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_c3, h_no_mod_r3]
                  rw [if_neg (by clear *- h_rem_is_neg; omega)]
                  rw [if_neg (by clear *- h_c_is_neg; omega)]
                  simp
                . simp [eq_max_0, eq_max_1, eq_max_2, eq_max_3]
                  simp [h_rem_is_neg] at eqp_ar0 eqp_ar1 eqp_ar2 eqp_ar3
                  simp [eqp_ar0, eqp_ar1, eqp_ar2, eqp_ar3]
                  conv =>
                    arg 1
                    simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_r3]
                    rw [if_neg (by clear *- h_rem_is_neg; omega)]
                  simp
                  simp at h_c_is_neg; specialize alu_c h_c_is_neg
                  obtain ⟨ ub_ac0, ub_ac1, ub_ac2, ub_ac3, alu_c ⟩ := alu_c
                  simp [← alu_c]
                  simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_c3, h_c_is_neg] at alu_c
                  split_ifs at alu_c with h_is_neg_ac
                  . simp [U32.toNat] at alu_c
                    repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)] at alu_c
                    omega
                  . simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_is_neg_ac]
                . simp [eq_max_0, eq_max_1, eq_max_2, eq_max_3]
                  simp [h_c_is_neg] at eqp_ac0 eqp_ac1 eqp_ac2 eqp_ac3
                  simp [eqp_ac0, eqp_ac1, eqp_ac2, eqp_ac3]
                  conv =>
                    arg 2
                    simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_c3]
                    rw [if_neg (by clear *- h_c_is_neg; omega)]
                  simp
                  simp at h_rem_is_neg; specialize alu_rem h_rem_is_neg
                  obtain ⟨ ub_ar0, ub_ar1, ub_ar2, ub_ar3, alu_rem ⟩ := alu_rem
                  simp [← alu_rem]
                  simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_r3, h_rem_is_neg] at alu_rem
                  split_ifs at alu_rem with h_is_neg_ar
                  . simp [U32.toNat] at alu_rem
                    repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)] at alu_rem
                    omega
                  . simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_is_neg_ar]
                . simp [eq_max_0, eq_max_1, eq_max_2, eq_max_3]
                  simp at h_c_is_neg; specialize alu_c h_c_is_neg
                  obtain ⟨ ub_ac0, ub_ac1, ub_ac2, ub_ac3, alu_c ⟩ := alu_c
                  simp [← alu_c]
                  simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_c3, h_c_is_neg] at alu_c
                  split_ifs at alu_c with h_is_neg_ac
                  . simp [U32.toNat] at alu_c
                    repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)] at alu_c
                    omega
                  . conv =>
                      arg 2
                      simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_is_neg_ac]
                    simp at h_rem_is_neg; specialize alu_rem h_rem_is_neg
                    obtain ⟨ ub_ar0, ub_ar1, ub_ar2, ub_ar3, alu_rem ⟩ := alu_rem
                    simp [← alu_rem]
                    simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_no_mod_r3, h_rem_is_neg] at alu_rem
                    split_ifs at alu_rem with h_is_neg_ar
                    . simp [U32.toNat] at alu_rem
                      repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)] at alu_rem
                      omega
                    . simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide, h_is_neg_ar]
        simp [cond_2]
        have relevant_constraints : constraint_68 air row ∧ constraint_69 air row
          := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
        ] at relevant_constraints
        have eq_rem_neg_uint :
          air.cols.rem_neg row 0 =
            if U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)] < 0 then 1 else 0
        := by
          have h_neg := @U32.negative_toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)]
          simp [← U32.msb_3_negative, BitVec.msb_eq_decide] at h_neg
          simp [← h_neg]
          clear *- eq_rem_neg ub_r3; grind
        have eq_b_neg_uint :
          air.cols.b_neg row 0 =
            if U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.b_0 row 0), BitVec.ofNat 8 ↑(air.cols.b_1 row 0), BitVec.ofNat 8 ↑(air.cols.b_2 row 0), BitVec.ofNat 8 ↑(air.cols.b_3 row 0)] < 0 then 1 else 0
        := by
          have h_neg := @U32.negative_toInt #v[BitVec.ofNat 8 ↑(air.cols.b_0 row 0), BitVec.ofNat 8 ↑(air.cols.b_1 row 0), BitVec.ofNat 8 ↑(air.cols.b_2 row 0), BitVec.ofNat 8 ↑(air.cols.b_3 row 0)]
          simp [← U32.msb_3_negative, BitVec.msb_eq_decide] at h_neg
          simp [← h_neg]
          clear *- eq_b_neg ub_b3; grind
        obtain ⟨ h_negs, h_rem_0_or_neg_or ⟩ := relevant_constraints
        replace h_rem_0_or_neg_or :
          air.cols.remainder_0 row 0 + air.cols.remainder_1 row 0 + air.cols.remainder_2 row 0 + air.cols.remainder_3 row 0 = 0 ∨
          (¬(U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)] = 0) ∧ (air.cols.rem_neg row 0 = 1 ∨ air.cols.b_neg row 0 = 0))
        := by
          clear *- h_negs h_rem_0_or_neg_or eq_b_neg eq_rem_neg ub_r0 ub_r1 ub_r2 ub_r3
          have :
            air.cols.remainder_0 row 0 + air.cols.remainder_1 row 0 + air.cols.remainder_2 row 0 + air.cols.remainder_3 row 0 = 0 ↔
            U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)] = 0
          := by
            simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
            split_ifs <;> simp [U32.toNat] <;> omega
          rw [← this]; tauto
        obtain h_rem_0 | ⟨ h_rem_n0, h_neg_or ⟩ := h_rem_0_or_neg_or <;> [ left; right ]
        . clear eq_b_neg eq_rem_neg h_negs
          simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
          split_ifs <;> simp [U32.toNat] <;> omega
        . simp [eq_rem_neg_uint, eq_b_neg_uint] at h_negs h_neg_or
          simp [Int.sign_cases]
          split_ifs with h_if_0 h_if_1 h_if_2 h_if_1 h_if_2 <;> try { simp }
          . clear *- h_if_0 h_if_1 h_negs h_rem_n0 h_neg_or; omega
          . clear *- h_if_0 h_if_1 h_if_2 h_negs h_rem_n0 h_neg_or; omega
          . clear *- h_if_0 h_if_1 h_negs h_rem_n0 h_neg_or; omega
          . clear *- h_if_0 h_if_1 h_if_2 h_negs h_rem_n0 h_neg_or
                     ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
                     ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3
                     cond_1 cond_2
            simp [h_if_2] at cond_1 h_negs h_neg_or h_if_1 h_if_2
            clear h_neg_or h_if_1 h_if_2
            have lb_r : 0 < U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)] := by clear *- h_negs h_rem_n0; omega
            clear *- cond_1 cond_2 lb_r
            obtain ⟨ q, c, r, eq_q, eq_c, eq_r ⟩ :
              ∃ q c r, q = U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.quotient_0 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_1 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_2 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_3 row 0)] ∧
                       c = U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0), BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] ∧
                       r = U32.toInt #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)]
              := by simp
            simp [← eq_q, ← eq_c, ← eq_r] at cond_1 cond_2 lb_r
            clear eq_q eq_r eq_c
            simp [Int.abs_cases] at cond_2
            rw [if_pos (by omega)] at cond_2
            apply Int.split_nzp c <;> intro hc
            . rw [if_neg (by omega)] at cond_2
              apply Int.split_nzp q <;> intro hq <;> nlinarith
            . omega
            . rw [if_pos (by omega)] at cond_2
              apply Int.split_nzp q <;> intro hq <;> nlinarith

  --
  -- DIVU-REMU specification
  --

  lemma spec_DIVU_REMU
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_divu_remu : air.cols.is_divu row 0 + air.cols.is_remu row 0 = 1)
  :
    ⟨ U32.toBV #v[air.cols.quotient_0 row 0, air.cols.quotient_1 row 0, air.cols.quotient_2 row 0, air.cols.quotient_3 row 0],
      U32.toBV #v[air.cols.remainder_0 row 0, air.cols.remainder_1 row 0, air.cols.remainder_2 row 0, air.cols.remainder_3 row 0]⟩ =
    RV32IM.execute_DIV_REM_pure (U32.toBV #v[air.cols.b_0 row 0, air.cols.b_1 row 0, air.cols.b_2 row 0, air.cols.b_3 row 0])
                                (U32.toBV #v[air.cols.c_0 row 0, air.cols.c_1 row 0, air.cols.c_2 row 0, air.cols.c_3 row 0]) .DRU
  := by
    obtain ⟨ eq_div, eq_rem ⟩ : air.cols.is_div row 0 = 0 ∧ air.cols.is_rem row 0 = 0
      := by
        have selectors := selector_breakdown air row h_is_real h_constraints
        clear *- selectors h_divu_remu; grind
    -- Helpers
    obtain ⟨ eq_is_c_0, eq_rem_mult ⟩ := helpers_general air row h_is_real h_constraints
    -- External assumptions
    simp [bus_row_ext_asm, bus_row, h_is_real, and_assoc] at h_ext
    obtain ⟨ u0, u1, ub_operands ⟩ := h_ext; clear u0 u1
    have ub_op_hyps : 4 < air.cols.is_divu row 0 * 35 + air.cols.is_remu row 0 * 37 + air.cols.is_div row 0 * 34 + air.cols.is_rem row 0 * 36
      := by
        have selectors := selector_breakdown air row h_is_real h_constraints
        clear *- selectors; omega
    specialize ub_operands ub_op_hyps
    obtain ⟨ ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3 ⟩ := ub_operands
    clear ub_op_hyps
    -- Well-formedness assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ u0, asm_alu, asm_byte, u1, u2 ⟩ := h_wf; clear u0 u1 u2
    -- MSB and range assumptions
    simp [bus_row, ByteBus.Spec, h_is_real, and_assoc] at asm_byte
    obtain ⟨ eq_b_msb, ub_b_msb, u0, eq_c_msb, ub_c_msb, u1, eq_rem_msb, ub_rem_msb, u2,
             ub_q0, ub_q1, ub_q2, ub_q3, ub_r0, ub_r1, ub_r2, ub_r3,
             ub_cq0, ub_cq1, ub_cq2, ub_cq3, ub_cq4, ub_cq5, ub_cq6, ub_cq7 ⟩ := asm_byte
    clear u0 u1 u2
    -- ALU assumptions
    simp [bus_row, h_is_real, h_divu_remu, eq_div, eq_rem] at asm_alu
    obtain ⟨ alu_mul_l, alu_mul_h, alu_c, alu_rem, alu_rem_mult ⟩ := asm_alu
    clear alu_c alu_rem
    simp [ALUBus.Spec] at alu_mul_l alu_mul_h
    replace alu_mul_l := alu_mul_l.2; replace alu_mul_h := alu_mul_h.2
    -- Other details
    have eq_is_signed : air.cols.is_signed row 0 = 0
      := by simp [Valid_DivRemCols.is_signed, eq_div, eq_rem]
    -- Main proof
    simp [RV32IM.execute_DIV_REM_pure, RV32IM.execute_DIV_REM_pure_int]
    by_cases h_c_zero :
      U32.toNat
        #v[BitVec.ofNat 8 (air.cols.c_0 row 0), BitVec.ofNat 8 (air.cols.c_1 row 0),
           BitVec.ofNat 8 (air.cols.c_2 row 0), BitVec.ofNat 8 (air.cols.c_3 row 0)] = 0 <;>
    simp [h_c_zero] <;>
    [ skip; have eq_is_c_0_nat := h_c_zero ] <;>
    rw [U32_nat_eq_0 ub_c0 ub_c1 ub_c2 ub_c3] at h_c_zero <;>
    simp [h_c_zero] at eq_is_c_0 alu_rem_mult
    . -- `c` is zero
      obtain ⟨ eq_c0, eq_c1, eq_c2, eq_c3 ⟩ := h_c_zero
      split_ands
      . have relevant_q_constraints :
          constraint_89 air row ∧ constraint_90 air row ∧ constraint_91 air row ∧ constraint_92 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          *
        ] at relevant_q_constraints
        simp [relevant_q_constraints, U32.toBV]
      . simp [eq_c0, eq_c1, eq_c2, eq_c3, RV32IM.execute_MUL_pure] at alu_mul_l
        conv at alu_mul_l => rhs; simp [U32.toBV, BitVec.extend]
        simp [← BitVec.toNat_inj, U32_nat_eq_0 ub_cq0 ub_cq1 ub_cq2 ub_cq3] at alu_mul_l
        obtain ⟨ eq_cq0, eq_cq1, eq_cq2, eq_cq3 ⟩ := alu_mul_l
        simp [← BitVec.toNat_inj]
        have ub_b := U32.toNat_ub #v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0), BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)]
        rw [Nat.mod_eq_of_lt (by clear *- ub_b; omega)]
        have relevant_r_constraints :
          constraint_44 air row ∧ constraint_45 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧
          constraint_108 air row ∧ constraint_109 air row ∧ constraint_110 air row ∧ constraint_111 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          *
        ] at relevant_r_constraints
        have carry_zeros :
          air.cols.carry_0 row 0 = 0 ∧ air.cols.carry_1 row 0 = 0 ∧ air.cols.carry_2 row 0 = 0 ∧ air.cols.carry_3 row 0 = 0
          := by omega
        simp [carry_zeros] at relevant_r_constraints
        simp [relevant_r_constraints]
    -- `c` is not zero
    . have alu_mul := RV32IM.combine_MUL_MULHU alu_mul_l alu_mul_h;
      simp at alu_mul; clear alu_mul_l alu_mul_h
      . have relevant_constraints :
          constraint_0 air row ∧ constraint_1 air row ∧ constraint_43 air row ∧
          constraint_44 air row ∧ constraint_45 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧
          constraint_48 air row ∧ constraint_49 air row ∧ constraint_51 air row ∧ constraint_52 air row ∧
          constraint_54 air row ∧ constraint_55 air row ∧ constraint_57 air row ∧ constraint_58 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          eq_is_signed
        ] at relevant_constraints
        obtain ⟨ eq_b_neg, eq_rem_neg, eq_overflow, relevant_constraints ⟩ := relevant_constraints
        simp [eq_b_neg, eq_rem_neg, eq_overflow] at relevant_constraints
        set b_ext : FKB := ⟨ U32.ext #v[air.cols.b_0 row 0, air.cols.b_1 row 0, air.cols.b_2 row 0, air.cols.b_3 row 0] false, by clear *-; have := @U32.ext_le_255; grind⟩
        have eq_b_ext : b_ext = 0 := by subst b_ext; simp [U32.ext]
        set r_ext : FKB := ⟨ U32.ext #v[air.cols.remainder_0 row 0, air.cols.remainder_1 row 0, air.cols.remainder_2 row 0, air.cols.remainder_3 row 0] false, by clear *-; have := @U32.ext_le_255; grind⟩
        have eq_r_ext : r_ext = 0 := by subst r_ext; simp [U32.ext]
        obtain ⟨ eq_p0, eq_p1, eq_p2, eq_p3, eq_p4', eq_p5', eq_p6', eq_p7' ⟩ := relevant_constraints
        symm at eq_p0 eq_p1 eq_p2 eq_p3
        have ⟨ eq_p4, eq_p5, eq_p6, eq_p7 ⟩ :
          air.cols.c_times_quotient_4 row 0 + r_ext - air.cols.carry_4 row 0 * 256 + air.cols.carry_3 row 0 = b_ext ∧
          air.cols.c_times_quotient_5 row 0 + r_ext - air.cols.carry_5 row 0 * 256 + air.cols.carry_4 row 0 = b_ext ∧
          air.cols.c_times_quotient_6 row 0 + r_ext - air.cols.carry_6 row 0 * 256 + air.cols.carry_5 row 0 = b_ext ∧
          air.cols.c_times_quotient_7 row 0 + r_ext - air.cols.carry_7 row 0 * 256 + air.cols.carry_6 row 0 = b_ext
        := by
          clear *- ub_b3 eq_p4' eq_p5' eq_p6' eq_p7'
          subst b_ext; simp [U32.ext]
          grind
        clear eq_p4' eq_p5' eq_p6' eq_p7'
        have relevant_constraints :
          constraint_108 air row ∧ constraint_109 air row ∧ constraint_110 air row ∧ constraint_111 air row ∧
          constraint_112 air row ∧ constraint_113 air row ∧ constraint_114 air row ∧ constraint_115 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
        ] at relevant_constraints
        obtain ⟨ b_cr0, b_cr1, b_cr2, b_cr3, b_cr4, b_cr5, b_cr6, b_cr7 ⟩ := relevant_constraints
        have alu_sum :=
          @FKB_add_64
            (eq_p0 := eq_p0) (eq_p1 := eq_p1) (eq_p2 := eq_p2) (eq_p3 := eq_p3)
            (eq_p4 := eq_p4) (eq_p5 := eq_p5) (eq_p6 := eq_p6) (eq_p7 := eq_p7)
        specialize alu_sum ub_b0 ub_b1 ub_b2 ub_b3 (by rw [eq_b_ext]; simp) (by rw [eq_b_ext]; simp) (by rw [eq_b_ext]; simp) (by rw [eq_b_ext]; simp)
        specialize alu_sum ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cq4 ub_cq5 ub_cq6 ub_cq7 ub_r0 ub_r1 ub_r2 ub_r3 (by rw [eq_r_ext]; simp) (by rw [eq_r_ext]; simp) (by rw [eq_r_ext]; simp) (by rw [eq_r_ext]; simp)
        specialize alu_sum b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7
        clear b_cr0 b_cr1 b_cr2 b_cr3 b_cr4 b_cr5 b_cr6 b_cr7 eq_p0 eq_p1 eq_p2 eq_p3 eq_p4 eq_p5 eq_p6 eq_p7
        replace alu_sum :
          (U32.extend
            #v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0),
               BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)]
            false).toBV =
            U64.toBV
              #v[BitVec.ofNat 8 (air.cols.c_times_quotient_0 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_1 row 0),
                 BitVec.ofNat 8 (air.cols.c_times_quotient_2 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_3 row 0),
                 BitVec.ofNat 8 (air.cols.c_times_quotient_4 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_5 row 0),
                 BitVec.ofNat 8 (air.cols.c_times_quotient_6 row 0), BitVec.ofNat 8 (air.cols.c_times_quotient_7 row 0)] +
              (U32.extend
                 #v[BitVec.ofNat 8 (air.cols.remainder_0 row 0), BitVec.ofNat 8 (air.cols.remainder_1 row 0),
                    BitVec.ofNat 8 (air.cols.remainder_2 row 0), BitVec.ofNat 8 (air.cols.remainder_3 row 0)] false).toBV
          := by clear *- alu_sum; subst b_ext r_ext; simpa [U32.extend]
        clear eq_r_ext eq_b_ext b_ext r_ext
        have ub_b := U32.toNat_ub (#v[BitVec.ofNat 8 (air.cols.b_0 row 0), BitVec.ofNat 8 (air.cols.b_1 row 0), BitVec.ofNat 8 (air.cols.b_2 row 0), BitVec.ofNat 8 (air.cols.b_3 row 0)])
        have ub_c := U32.toNat_ub (#v[BitVec.ofNat 8 (air.cols.c_0 row 0), BitVec.ofNat 8 (air.cols.c_1 row 0), BitVec.ofNat 8 (air.cols.c_2 row 0), BitVec.ofNat 8 (air.cols.c_3 row 0)])
        have ub_q := U32.toNat_ub (#v[BitVec.ofNat 8 (air.cols.quotient_0 row 0), BitVec.ofNat 8 (air.cols.quotient_1 row 0), BitVec.ofNat 8 (air.cols.quotient_2 row 0), BitVec.ofNat 8 (air.cols.quotient_3 row 0)])
        have ub_r := U32.toNat_ub (#v[BitVec.ofNat 8 (air.cols.remainder_0 row 0), BitVec.ofNat 8 (air.cols.remainder_1 row 0), BitVec.ofNat 8 (air.cols.remainder_2 row 0), BitVec.ofNat 8 (air.cols.remainder_3 row 0)])
        -- Moving to the two conditions
        simp [← BitVec.toNat_inj]
        rw [Nat.mod_eq_of_lt
            (by
              simp [Int.natCast_tdiv_eq_ediv]
              apply lt_of_le_of_lt
              . apply Int.ediv_le_self
                omega
              . omega
            )]
        rw [Nat.mod_eq_of_lt
            (by
              simp [Int.tmod_eq_emod]
              trans
              . apply Int.emod_lt_of_pos
                clear *- ub_c eq_is_c_0_nat
                omega
              . omega
            )]
        rw [Int.tdiv_tmod_unique_full_nat eq_is_c_0_nat]
        -- First condition
        have cond_1 :
          U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.b_0 row 0), BitVec.ofNat 8 ↑(air.cols.b_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.b_2 row 0), BitVec.ofNat 8 ↑(air.cols.b_3 row 0)] =
          U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.quotient_0 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.quotient_2 row 0), BitVec.ofNat 8 ↑(air.cols.quotient_3 row 0)] *
          U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] +
          U32.toNat
            #v[BitVec.ofNat 8 ↑(air.cols.remainder_0 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_1 row 0),
               BitVec.ofNat 8 ↑(air.cols.remainder_2 row 0), BitVec.ofNat 8 ↑(air.cols.remainder_3 row 0)]
        := by
          rw [alu_mul] at alu_sum
          clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
                   ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3
                   alu_sum ub_b ub_c ub_q ub_r
          simp [← BitVec.toNat_inj] at alu_sum; rw [alu_sum]
          rw [Nat.mod_eq_of_lt]; nlinarith
        simp [cond_1]
        -- Second condition
        clear *- cond_1 ub_r ub_c alu_rem_mult eq_rem_mult h_c_zero eq_is_c_0 eq_is_signed h_constraints
        simp [h_c_zero] at eq_rem_mult; simp [eq_rem_mult, ALUBus.Spec] at alu_rem_mult
        conv at alu_rem_mult => lhs; simp [U32.toBV]
        have relevant_constraints :
          constraint_1 air row ∧ constraint_2 air row ∧
          constraint_93 air row ∧ constraint_94 air row ∧ constraint_95 air row ∧ constraint_96 air row ∧
          constraint_97 air row ∧ constraint_98 air row ∧ constraint_99 air row ∧ constraint_100 air row ∧
          constraint_101 air row ∧ constraint_102 air row ∧ constraint_103 air row ∧ constraint_104 air row
        := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
        simp [
          pico_encapsulation,
          constraint_and_interaction_simplification,
          sub_eq_zero,
          eq_is_c_0,
          eq_is_signed
        ] at relevant_constraints
        obtain ⟨ eq_rem_neg, eq_c_neg, relevant_constraints ⟩ := relevant_constraints
        simp_all

  --
  -- Opcode specifications
  --

  lemma spec_DIV
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_is_div : air.cols.is_div row 0 = 1)
  :
    ALUBus.Spec
      34
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    have exclusivity := selector_exclusivity air row h_is_real h_constraints
    replace exclusivity := exclusivity.1
    simp [h_is_div] at exclusivity
    have spec := spec_DIV_REM air row h_is_real h_ext h_wf h_constraints (by omega)
    obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
    : constraint_60 air row ∧ constraint_62 air row ∧ constraint_64 air row ∧ constraint_66 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at eq_a0 eq_a1 eq_a2 eq_a3
    rw [← eq_a0, ← eq_a1, ← eq_a2, ← eq_a3]
    simp [bus_row_wf_asm] at h_wf
    replace h_wf := h_wf.2.2.1
    simp [bus_row, h_is_real, ByteBus.Spec] at h_wf
    simp [ALUBus.Spec, ← spec, h_wf]

  lemma spec_DIVU
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_is_divu : air.cols.is_divu row 0 = 1)
  :
    ALUBus.Spec
      35
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    have exclusivity := selector_exclusivity air row h_is_real h_constraints
    replace exclusivity := exclusivity.2.1
    simp [h_is_divu] at exclusivity
    have spec := spec_DIVU_REMU air row h_is_real h_ext h_wf h_constraints (by omega)
    obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
    : constraint_60 air row ∧ constraint_62 air row ∧ constraint_64 air row ∧ constraint_66 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at eq_a0 eq_a1 eq_a2 eq_a3
    rw [← eq_a0, ← eq_a1, ← eq_a2, ← eq_a3]
    simp [bus_row_wf_asm] at h_wf
    replace h_wf := h_wf.2.2.1
    simp [bus_row, h_is_real, ByteBus.Spec] at h_wf
    simp [ALUBus.Spec, ← spec, h_wf]

  lemma spec_REM
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_is_rem : air.cols.is_rem row 0 = 1)
  :
    ALUBus.Spec
      36
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    have exclusivity := selector_exclusivity air row h_is_real h_constraints
    replace exclusivity := exclusivity.2.2.1
    simp [h_is_rem] at exclusivity
    have spec := spec_DIV_REM air row h_is_real h_ext h_wf h_constraints (by omega)
    obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
    : constraint_61 air row ∧ constraint_63 air row ∧ constraint_65 air row ∧ constraint_67 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at eq_a0 eq_a1 eq_a2 eq_a3
    rw [← eq_a0, ← eq_a1, ← eq_a2, ← eq_a3]
    simp [bus_row_wf_asm] at h_wf
    replace h_wf := h_wf.2.2.1
    simp [bus_row, h_is_real, ByteBus.Spec] at h_wf
    simp [ALUBus.Spec, ← spec, h_wf]

  lemma spec_REMU
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
    (h_is_remu : air.cols.is_remu row 0 = 1)
  :
    ALUBus.Spec
      37
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    have exclusivity := selector_exclusivity air row h_is_real h_constraints
    replace exclusivity := exclusivity.2.2.2
    simp [h_is_remu] at exclusivity
    have spec := spec_DIVU_REMU air row h_is_real h_ext h_wf h_constraints (by omega)
    obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
    : constraint_61 air row ∧ constraint_63 air row ∧ constraint_65 air row ∧ constraint_67 air row
      := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at eq_a0 eq_a1 eq_a2 eq_a3
    rw [← eq_a0, ← eq_a1, ← eq_a2, ← eq_a3]
    simp [bus_row_wf_asm] at h_wf
    replace h_wf := h_wf.2.2.1
    simp [bus_row, h_is_real, ByteBus.Spec] at h_wf
    simp [ALUBus.Spec, ← spec, h_wf]

  --
  -- Well-formedness
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_DivRemAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : DivRemAir.Extraction.allHold air row)
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
        simp [bus_row, h_is_real]
        split_ands
        . have relevant_constraints : constraint_128 air row
          := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
          simp [
            pico_encapsulation,
            constraint_and_interaction_simplification,
            sub_eq_zero,
            *
          ] at relevant_constraints
          clear *- relevant_constraints; grind
        . have relevant_constraints : constraint_129 air row
            := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
          simp [
            pico_encapsulation,
            constraint_and_interaction_simplification,
            sub_eq_zero,
            *
          ] at relevant_constraints
          clear *- relevant_constraints; grind
        . have relevant_constraints
          : constraint_85 air row ∧ constraint_105 air row
            := by simp [allHold_simplified] at h_constraints; clear *- h_constraints; aesop
          simp [
            pico_encapsulation,
            constraint_and_interaction_simplification,
            sub_eq_zero,
            *
          ] at relevant_constraints
          clear *- relevant_constraints; grind
        . have selectors := selector_breakdown air row h_is_real h_constraints
          have exclusivity := selector_exclusivity air row h_is_real h_constraints
          obtain ⟨h_div, h_divu, h_rem, h_remu, h_sum⟩ := selectors
          obtain h_div | h_div := h_div
          · obtain h_divu | h_divu := h_divu
            · obtain h_rem | h_rem := h_rem
              . obtain h_remu | h_remu := h_remu
                . exfalso; grind
                . have spec := spec_REMU air row h_is_real h_ext h_wf h_constraints h_remu
                  simp_all
              . have spec := spec_REM air row h_is_real h_ext h_wf h_constraints h_rem
                simp_all
            . have spec := spec_DIVU air row h_is_real h_ext h_wf h_constraints h_divu
              simp_all
          . have spec := spec_DIV air row h_is_real h_ext h_wf h_constraints h_div
            simp_all
      . constructor
        . simp [bus_row, ByteBus.Spec]
          have selectors := selector_exclusivity air row h_is_real h_constraints
          split_ands <;> intro h <;> exfalso <;> grind
        . simp [bus_row]

end DivRemAir.Spec
