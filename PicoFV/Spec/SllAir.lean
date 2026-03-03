import PicoFV.Constraints.SllAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace SllAir.Spec

  open RV32IM_Interactions
  open SllAir.ConstraintsAndBuses
  open SllAir.Interactions

  -- Helper: Convert FKB shift-result equation (first byte) to Nat carry equation
  private lemma sr_nat_first (sr b bsm co : FKB)
      (hsr : sr.val < 256) (hb : b.val < 256) (hbsm : bsm.val ≤ 128)
      (hco : co.val < 256)
      (heq : sr = b * bsm - co * 256) :
      sr.val + co.val * 256 = b.val * bsm.val := by
    have hprod : b.val * bsm.val ≤ 255 * 128 := Nat.mul_le_mul (by omega) hbsm
    grind

  -- Helper: Convert FKB shift-result equation (subsequent bytes) to Nat carry equation
  private lemma sr_nat_next (sr b bsm ci co : FKB)
      (hsr : sr.val < 256) (hb : b.val < 256) (hbsm : bsm.val ≤ 128)
      (hci : ci.val < 256) (hco : co.val < 256)
      (heq : sr = b * bsm - co * 256 + ci) :
      sr.val + co.val * 256 = b.val * bsm.val + ci.val := by
    have hprod : b.val * bsm.val ≤ 255 * 128 := Nat.mul_le_mul (by omega) hbsm
    grind

  -- Tactic macro for closing each SLL shift case with a concrete shift amount k
  set_option hygiene false in
  local macro "close_sll" : tactic =>
    `(tactic| (
      simp_all
      apply BitVec.eq_of_toNat_eq
      simp [U32.toBV_toNat, U32.toNat, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
      omega))

  lemma spec_SLL
    [Field ExtF]
    (air : Valid_SllAir FKB ExtF)
    (row : ℕ)
    (h_assumptions : bus_row_assumptions (bus_row air row))
    (h_constraints : SllAir.Extraction.allHold air row)
    (h_is_real : air.cols.is_real row 0 = 1)
  :
    ALUBus.Spec
      5
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Unfold ALUBus.Spec for opcode 5
    simp only [ALUBus.Spec]
    intro ⟨hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3⟩
    -- Simplify constraints
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    -- Get byte bounds from assumptions
    simp [bus_row_assumptions, bus_row, h_is_real, ByteBusEntry.Spec] at h_assumptions
    -- Extract byte bounds
    obtain ⟨⟨hsr0, hsr1⟩, ⟨hsr2, hsr3⟩, ⟨hsrc0, hsrc1⟩, hsrc2, hsrc3⟩ := h_assumptions
    -- Extract all constraints
    obtain ⟨_, h_c0_decomp,
      h_sbn0_sel, h_sbn1_sel, h_sbn2_sel, h_sbn3_sel, h_sbn4_sel, h_sbn5_sel, h_sbn6_sel, h_sbn7_sel,
      h_bsm0, h_bsm1, h_bsm2, h_bsm3, h_bsm4, h_bsm5, h_bsm6, h_bsm7,
      h_sr0, h_sr1, h_sr2, h_sr3,
      h_sbnb0_sel, h_sbnb1_sel, h_sbnb2_sel, h_sbnb3_sel,
      h_a0_b0, h_a1_b0, h_a2_b0, h_a3_b0,
      h_a0_b1, h_a1_b1, h_a2_b1, h_a3_b1,
      h_a0_b2, h_a1_b2, h_a2_b2, h_a3_b2,
      h_a0_b3, h_a1_b3, h_a2_b3, h_a3_b3,
      h_lsb0, h_lsb1, h_lsb2, h_lsb3, h_lsb4, h_lsb5, h_lsb6, h_lsb7,
      h_sbn0_bin, h_sbn1_bin, h_sbn2_bin, h_sbn3_bin, h_sbn4_bin, h_sbn5_bin, h_sbn6_bin, h_sbn7_bin,
      h_sbn_sum,
      h_sbnb0_bin, h_sbnb1_bin, h_sbnb2_bin, h_sbnb3_bin,
      h_sbnb_sum,
      _⟩ := h_constraints
    -- Derive bsm bound from constraints
    have hbsm : (air.cols.bit_shift_multiplier row 0).val ≤ 128 := by grind
    -- Derive Nat carry equations before case split
    have nat_sr0 := sr_nat_first _ _ _ _ hsr0 hb0 hbsm hsrc0 h_sr0
    have nat_sr1 := sr_nat_next _ _ _ _ _ hsr1 hb1 hbsm hsrc0 hsrc1 h_sr1
    have nat_sr2 := sr_nat_next _ _ _ _ _ hsr2 hb2 hbsm hsrc1 hsrc2 h_sr2
    have nat_sr3 := sr_nat_next _ _ _ _ _ hsr3 hb3 hbsm hsrc2 hsrc3 h_sr3

    have h_mod_32:
      U32.toNat #v[BitVec.ofNat 8 ↑(air.cols.c_0 row 0), BitVec.ofNat 8 ↑(air.cols.c_1 row 0),
                   BitVec.ofNat 8 ↑(air.cols.c_2 row 0), BitVec.ofNat 8 ↑(air.cols.c_3 row 0)] % 32
        =
      air.cols.c_lsb_0 row 0 + 2 * air.cols.c_lsb_1 row 0 +
      4 * air.cols.c_lsb_2 row 0 + 8 * air.cols.c_lsb_3 row 0 + 16 * air.cols.c_lsb_4 row 0
    := by
      simp [U32.toNat, ← h_c0_decomp]
      clear *- hc0 hc1 hc2 hc3 h_lsb0 h_lsb1 h_lsb2 h_lsb3 h_lsb4 h_lsb5 h_lsb6 h_lsb7
      grind
    rw [h_mod_32]

    -- Case split on 5 low bits (32 cases) and close each
    rcases h_lsb0 with h0 | h0 <;>
    rcases h_lsb1 with h1 | h1 <;>
    rcases h_lsb2 with h2 | h2 <;>
    rcases h_lsb3 with h3 | h3 <;>
    rcases h_lsb4 with h4 | h4

    all_goals close_sll

  lemma assertions
      [Field ExtF]
      (air : Valid_SllAir FKB ExtF)
      (row : ℕ)
      (h_assumptions : bus_row_assumptions (bus_row air row))
      (h_constraints : SllAir.Extraction.allHold air row)
    :
      bus_row_assertions (bus_row air row)
    := by
      -- Set up assumptions
      have h_assumptions' := h_assumptions
      simp [bus_row_assumptions] at h_assumptions'
      obtain ⟨ asm_prog, asm_alu, asm_byte, asm_reg ⟩ := h_assumptions'
      -- Main proof
      simp [bus_row_assertions]
      constructor
      -- Program
      . simp [bus_row]
      . constructor
        . -- ALU
          simp [bus_row]
          intro h_is_real
          exact spec_SLL air row h_assumptions h_constraints h_is_real
        . constructor
          . -- Byte
            simp [bus_row, ByteBusEntry.Spec]
            have h_c := h_constraints
            simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c
            split_ands <;> intro h <;> exfalso <;> grind
          . -- Register
            simp [bus_row]

end SllAir.Spec
