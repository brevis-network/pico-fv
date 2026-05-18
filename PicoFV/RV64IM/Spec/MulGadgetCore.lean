import PicoFV.Fundamentals.Word

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

/-!
# MulGadget core schoolbook-multiplication identity

This file isolates `core_mul_64` — the heavy ℕ-arithmetic lemma at
the heart of the `MulGadget` proof — into its own compilation unit so
that the rest of `Spec/MulGadget.lean` typechecks quickly. The lemma
is the RV64 analogue of RV32's `MulAir.Spec.core_mul`: given 16
byte-level carry-propagation equations on 16-byte operands `bw`, `cw`,
it concludes that the 16-byte `prod` satisfies
`U128b.toBV prod = U128b.toBV bw * U128b.toBV cw`.
-/

namespace MulGadget.Spec

  /-- Schoolbook multiplication correctness on 16-byte operands.
      RV64 analogue of `RV32.MulAir.Spec.core_mul`. -/
  lemma core_mul_64
    (bw cw : U128b)
    (prod : U128b)
    (cy0 cy1 cy2 cy3 cy4 cy5 cy6 cy7
     cy8 cy9 cy10 cy11 cy12 cy13 cy14 cy15 : ℕ)
    -- Carry chain (schoolbook byte-multiplication).
    (h0 :  prod[0].toNat + cy0 * 256 =
             bw[0].toNat * cw[0].toNat)
    (h1 :  prod[1].toNat + cy1 * 256 =
             bw[0].toNat * cw[1].toNat + bw[1].toNat * cw[0].toNat + cy0)
    (h2 :  prod[2].toNat + cy2 * 256 =
             bw[0].toNat * cw[2].toNat + bw[1].toNat * cw[1].toNat +
             bw[2].toNat * cw[0].toNat + cy1)
    (h3 :  prod[3].toNat + cy3 * 256 =
             bw[0].toNat * cw[3].toNat + bw[1].toNat * cw[2].toNat +
             bw[2].toNat * cw[1].toNat + bw[3].toNat * cw[0].toNat + cy2)
    (h4 :  prod[4].toNat + cy4 * 256 =
             bw[0].toNat * cw[4].toNat + bw[1].toNat * cw[3].toNat +
             bw[2].toNat * cw[2].toNat + bw[3].toNat * cw[1].toNat +
             bw[4].toNat * cw[0].toNat + cy3)
    (h5 :  prod[5].toNat + cy5 * 256 =
             bw[0].toNat * cw[5].toNat + bw[1].toNat * cw[4].toNat +
             bw[2].toNat * cw[3].toNat + bw[3].toNat * cw[2].toNat +
             bw[4].toNat * cw[1].toNat + bw[5].toNat * cw[0].toNat + cy4)
    (h6 :  prod[6].toNat + cy6 * 256 =
             bw[0].toNat * cw[6].toNat + bw[1].toNat * cw[5].toNat +
             bw[2].toNat * cw[4].toNat + bw[3].toNat * cw[3].toNat +
             bw[4].toNat * cw[2].toNat + bw[5].toNat * cw[1].toNat +
             bw[6].toNat * cw[0].toNat + cy5)
    (h7 :  prod[7].toNat + cy7 * 256 =
             bw[0].toNat * cw[7].toNat + bw[1].toNat * cw[6].toNat +
             bw[2].toNat * cw[5].toNat + bw[3].toNat * cw[4].toNat +
             bw[4].toNat * cw[3].toNat + bw[5].toNat * cw[2].toNat +
             bw[6].toNat * cw[1].toNat + bw[7].toNat * cw[0].toNat + cy6)
    (h8 :  prod[8].toNat + cy8 * 256 =
             bw[0].toNat * cw[8].toNat + bw[1].toNat * cw[7].toNat +
             bw[2].toNat * cw[6].toNat + bw[3].toNat * cw[5].toNat +
             bw[4].toNat * cw[4].toNat + bw[5].toNat * cw[3].toNat +
             bw[6].toNat * cw[2].toNat + bw[7].toNat * cw[1].toNat +
             bw[8].toNat * cw[0].toNat + cy7)
    (h9 :  prod[9].toNat + cy9 * 256 =
             bw[0].toNat * cw[9].toNat + bw[1].toNat * cw[8].toNat +
             bw[2].toNat * cw[7].toNat + bw[3].toNat * cw[6].toNat +
             bw[4].toNat * cw[5].toNat + bw[5].toNat * cw[4].toNat +
             bw[6].toNat * cw[3].toNat + bw[7].toNat * cw[2].toNat +
             bw[8].toNat * cw[1].toNat + bw[9].toNat * cw[0].toNat + cy8)
    (h10 : prod[10].toNat + cy10 * 256 =
             bw[0].toNat * cw[10].toNat + bw[1].toNat * cw[9].toNat +
             bw[2].toNat * cw[8].toNat + bw[3].toNat * cw[7].toNat +
             bw[4].toNat * cw[6].toNat + bw[5].toNat * cw[5].toNat +
             bw[6].toNat * cw[4].toNat + bw[7].toNat * cw[3].toNat +
             bw[8].toNat * cw[2].toNat + bw[9].toNat * cw[1].toNat +
             bw[10].toNat * cw[0].toNat + cy9)
    (h11 : prod[11].toNat + cy11 * 256 =
             bw[0].toNat * cw[11].toNat + bw[1].toNat * cw[10].toNat +
             bw[2].toNat * cw[9].toNat + bw[3].toNat * cw[8].toNat +
             bw[4].toNat * cw[7].toNat + bw[5].toNat * cw[6].toNat +
             bw[6].toNat * cw[5].toNat + bw[7].toNat * cw[4].toNat +
             bw[8].toNat * cw[3].toNat + bw[9].toNat * cw[2].toNat +
             bw[10].toNat * cw[1].toNat + bw[11].toNat * cw[0].toNat + cy10)
    (h12 : prod[12].toNat + cy12 * 256 =
             bw[0].toNat * cw[12].toNat + bw[1].toNat * cw[11].toNat +
             bw[2].toNat * cw[10].toNat + bw[3].toNat * cw[9].toNat +
             bw[4].toNat * cw[8].toNat + bw[5].toNat * cw[7].toNat +
             bw[6].toNat * cw[6].toNat + bw[7].toNat * cw[5].toNat +
             bw[8].toNat * cw[4].toNat + bw[9].toNat * cw[3].toNat +
             bw[10].toNat * cw[2].toNat + bw[11].toNat * cw[1].toNat +
             bw[12].toNat * cw[0].toNat + cy11)
    (h13 : prod[13].toNat + cy13 * 256 =
             bw[0].toNat * cw[13].toNat + bw[1].toNat * cw[12].toNat +
             bw[2].toNat * cw[11].toNat + bw[3].toNat * cw[10].toNat +
             bw[4].toNat * cw[9].toNat + bw[5].toNat * cw[8].toNat +
             bw[6].toNat * cw[7].toNat + bw[7].toNat * cw[6].toNat +
             bw[8].toNat * cw[5].toNat + bw[9].toNat * cw[4].toNat +
             bw[10].toNat * cw[3].toNat + bw[11].toNat * cw[2].toNat +
             bw[12].toNat * cw[1].toNat + bw[13].toNat * cw[0].toNat + cy12)
    (h14 : prod[14].toNat + cy14 * 256 =
             bw[0].toNat * cw[14].toNat + bw[1].toNat * cw[13].toNat +
             bw[2].toNat * cw[12].toNat + bw[3].toNat * cw[11].toNat +
             bw[4].toNat * cw[10].toNat + bw[5].toNat * cw[9].toNat +
             bw[6].toNat * cw[8].toNat + bw[7].toNat * cw[7].toNat +
             bw[8].toNat * cw[6].toNat + bw[9].toNat * cw[5].toNat +
             bw[10].toNat * cw[4].toNat + bw[11].toNat * cw[3].toNat +
             bw[12].toNat * cw[2].toNat + bw[13].toNat * cw[1].toNat +
             bw[14].toNat * cw[0].toNat + cy13)
    (h15 : prod[15].toNat + cy15 * 256 =
             bw[0].toNat * cw[15].toNat + bw[1].toNat * cw[14].toNat +
             bw[2].toNat * cw[13].toNat + bw[3].toNat * cw[12].toNat +
             bw[4].toNat * cw[11].toNat + bw[5].toNat * cw[10].toNat +
             bw[6].toNat * cw[9].toNat + bw[7].toNat * cw[8].toNat +
             bw[8].toNat * cw[7].toNat + bw[9].toNat * cw[6].toNat +
             bw[10].toNat * cw[5].toNat + bw[11].toNat * cw[4].toNat +
             bw[12].toNat * cw[3].toNat + bw[13].toNat * cw[2].toNat +
             bw[14].toNat * cw[1].toNat + bw[15].toNat * cw[0].toNat + cy14)
  :
    U128b.toBV prod = U128b.toBV bw * U128b.toBV cw
  := by
    simp [← BitVec.toNat_inj, U128b.toNat]
    -- Name every byte and carry for readability.
    set p0  := prod[0].toNat; set p1  := prod[1].toNat
    set p2  := prod[2].toNat; set p3  := prod[3].toNat
    set p4  := prod[4].toNat; set p5  := prod[5].toNat
    set p6  := prod[6].toNat; set p7  := prod[7].toNat
    set p8  := prod[8].toNat; set p9  := prod[9].toNat
    set p10 := prod[10].toNat; set p11 := prod[11].toNat
    set p12 := prod[12].toNat; set p13 := prod[13].toNat
    set p14 := prod[14].toNat; set p15 := prod[15].toNat
    set b0  := bw[0].toNat; set b1  := bw[1].toNat
    set b2  := bw[2].toNat; set b3  := bw[3].toNat
    set b4  := bw[4].toNat; set b5  := bw[5].toNat
    set b6  := bw[6].toNat; set b7  := bw[7].toNat
    set b8  := bw[8].toNat; set b9  := bw[9].toNat
    set b10 := bw[10].toNat; set b11 := bw[11].toNat
    set b12 := bw[12].toNat; set b13 := bw[13].toNat
    set b14 := bw[14].toNat; set b15 := bw[15].toNat
    set c0  := cw[0].toNat; set c1  := cw[1].toNat
    set c2  := cw[2].toNat; set c3  := cw[3].toNat
    set c4  := cw[4].toNat; set c5  := cw[5].toNat
    set c6  := cw[6].toNat; set c7  := cw[7].toNat
    set c8  := cw[8].toNat; set c9  := cw[9].toNat
    set c10 := cw[10].toNat; set c11 := cw[11].toNat
    set c12 := cw[12].toNat; set c13 := cw[13].toNat
    set c14 := cw[14].toNat; set c15 := cw[15].toNat
    -- Byte bounds (each BitVec 8 byte is < 256).
    have ub : p0 < 256 ∧ p1 < 256 ∧ p2 < 256 ∧ p3 < 256 ∧
              p4 < 256 ∧ p5 < 256 ∧ p6 < 256 ∧ p7 < 256 ∧
              p8 < 256 ∧ p9 < 256 ∧ p10 < 256 ∧ p11 < 256 ∧
              p12 < 256 ∧ p13 < 256 ∧ p14 < 256 ∧ p15 < 256 ∧
              b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
              b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧ b7 < 256 ∧
              b8 < 256 ∧ b9 < 256 ∧ b10 < 256 ∧ b11 < 256 ∧
              b12 < 256 ∧ b13 < 256 ∧ b14 < 256 ∧ b15 < 256 ∧
              c0 < 256 ∧ c1 < 256 ∧ c2 < 256 ∧ c3 < 256 ∧
              c4 < 256 ∧ c5 < 256 ∧ c6 < 256 ∧ c7 < 256 ∧
              c8 < 256 ∧ c9 < 256 ∧ c10 < 256 ∧ c11 < 256 ∧
              c12 < 256 ∧ c13 < 256 ∧ c14 < 256 ∧ c15 < 256 := by
      subst p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
      subst b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
      subst c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
      omega
    obtain ⟨ ub_p0, ub_p1, ub_p2, ub_p3, ub_p4, ub_p5, ub_p6, ub_p7,
             ub_p8, ub_p9, ub_p10, ub_p11, ub_p12, ub_p13, ub_p14, ub_p15,
             ub_b0, ub_b1, ub_b2, ub_b3, ub_b4, ub_b5, ub_b6, ub_b7,
             ub_b8, ub_b9, ub_b10, ub_b11, ub_b12, ub_b13, ub_b14, ub_b15,
             ub_c0, ub_c1, ub_c2, ub_c3, ub_c4, ub_c5, ub_c6, ub_c7,
             ub_c8, ub_c9, ub_c10, ub_c11, ub_c12, ub_c13, ub_c14, ub_c15 ⟩ := ub
    -- Derive mod/div decompositions from each carry equation.
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
    have eqp8 : p8 = (b0 * c8 + b1 * c7 + b2 * c6 + b3 * c5 + b4 * c4 + b5 * c3 + b6 * c2 + b7 * c1 + b8 * c0 + cy7) % 256 := by omega
    have eqc8 : cy8 = (b0 * c8 + b1 * c7 + b2 * c6 + b3 * c5 + b4 * c4 + b5 * c3 + b6 * c2 + b7 * c1 + b8 * c0 + cy7) / 256 := by omega
    have eqp9 : p9 = (b0 * c9 + b1 * c8 + b2 * c7 + b3 * c6 + b4 * c5 + b5 * c4 + b6 * c3 + b7 * c2 + b8 * c1 + b9 * c0 + cy8) % 256 := by omega
    have eqc9 : cy9 = (b0 * c9 + b1 * c8 + b2 * c7 + b3 * c6 + b4 * c5 + b5 * c4 + b6 * c3 + b7 * c2 + b8 * c1 + b9 * c0 + cy8) / 256 := by omega
    have eqp10 : p10 = (b0 * c10 + b1 * c9 + b2 * c8 + b3 * c7 + b4 * c6 + b5 * c5 + b6 * c4 + b7 * c3 + b8 * c2 + b9 * c1 + b10 * c0 + cy9) % 256 := by omega
    have eqc10 : cy10 = (b0 * c10 + b1 * c9 + b2 * c8 + b3 * c7 + b4 * c6 + b5 * c5 + b6 * c4 + b7 * c3 + b8 * c2 + b9 * c1 + b10 * c0 + cy9) / 256 := by omega
    have eqp11 : p11 = (b0 * c11 + b1 * c10 + b2 * c9 + b3 * c8 + b4 * c7 + b5 * c6 + b6 * c5 + b7 * c4 + b8 * c3 + b9 * c2 + b10 * c1 + b11 * c0 + cy10) % 256 := by omega
    have eqc11 : cy11 = (b0 * c11 + b1 * c10 + b2 * c9 + b3 * c8 + b4 * c7 + b5 * c6 + b6 * c5 + b7 * c4 + b8 * c3 + b9 * c2 + b10 * c1 + b11 * c0 + cy10) / 256 := by omega
    have eqp12 : p12 = (b0 * c12 + b1 * c11 + b2 * c10 + b3 * c9 + b4 * c8 + b5 * c7 + b6 * c6 + b7 * c5 + b8 * c4 + b9 * c3 + b10 * c2 + b11 * c1 + b12 * c0 + cy11) % 256 := by omega
    have eqc12 : cy12 = (b0 * c12 + b1 * c11 + b2 * c10 + b3 * c9 + b4 * c8 + b5 * c7 + b6 * c6 + b7 * c5 + b8 * c4 + b9 * c3 + b10 * c2 + b11 * c1 + b12 * c0 + cy11) / 256 := by omega
    have eqp13 : p13 = (b0 * c13 + b1 * c12 + b2 * c11 + b3 * c10 + b4 * c9 + b5 * c8 + b6 * c7 + b7 * c6 + b8 * c5 + b9 * c4 + b10 * c3 + b11 * c2 + b12 * c1 + b13 * c0 + cy12) % 256 := by omega
    have eqc13 : cy13 = (b0 * c13 + b1 * c12 + b2 * c11 + b3 * c10 + b4 * c9 + b5 * c8 + b6 * c7 + b7 * c6 + b8 * c5 + b9 * c4 + b10 * c3 + b11 * c2 + b12 * c1 + b13 * c0 + cy12) / 256 := by omega
    have eqp14 : p14 = (b0 * c14 + b1 * c13 + b2 * c12 + b3 * c11 + b4 * c10 + b5 * c9 + b6 * c8 + b7 * c7 + b8 * c6 + b9 * c5 + b10 * c4 + b11 * c3 + b12 * c2 + b13 * c1 + b14 * c0 + cy13) % 256 := by omega
    have eqc14 : cy14 = (b0 * c14 + b1 * c13 + b2 * c12 + b3 * c11 + b4 * c10 + b5 * c9 + b6 * c8 + b7 * c7 + b8 * c6 + b9 * c5 + b10 * c4 + b11 * c3 + b12 * c2 + b13 * c1 + b14 * c0 + cy13) / 256 := by omega
    have eqp15 : p15 = (b0 * c15 + b1 * c14 + b2 * c13 + b3 * c12 + b4 * c11 + b5 * c10 + b6 * c9 + b7 * c8 + b8 * c7 + b9 * c6 + b10 * c5 + b11 * c4 + b12 * c3 + b13 * c2 + b14 * c1 + b15 * c0 + cy14) % 256 := by omega
    clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    -- Substitute mod/div decompositions into the goal.
    simp [eqp0, eqp1, eqp2, eqp3, eqp4, eqp5, eqp6, eqp7,
          eqp8, eqp9, eqp10, eqp11, eqp12, eqp13, eqp14, eqp15,
          eqc0, eqc1, eqc2, eqc3, eqc4, eqc5, eqc6, eqc7,
          eqc8, eqc9, eqc10, eqc11, eqc12, eqc13, eqc14]
    clear eqp0 eqp1 eqp2 eqp3 eqp4 eqp5 eqp6 eqp7
          eqp8 eqp9 eqp10 eqp11 eqp12 eqp13 eqp14 eqp15
          eqc0 eqc1 eqc2 eqc3 eqc4 eqc5 eqc6 eqc7
          eqc8 eqc9 eqc10 eqc11 eqc12 eqc13 eqc14
    -- `joins` and `divs` ladders over `Fin 16`.
    have joins : ∀ (i : Fin 16) (a b : ℕ),
      a % (256 ^ i.val) + (b + a / (256 ^ i.val)) % 256 * (256 ^ i.val) =
      (a + b * (256 ^ i.val)) % (256 ^ (i.val + 1)) := by
      intro i a b; fin_cases i <;> simp <;> omega
    have divs : ∀ (i : Fin 16) (a b : ℕ),
      (a + b / (256 ^ i.val)) / 256 =
      (b + a * (256 ^ i.val)) / (256 ^ (i.val + 1)) := by
      intro i a b; fin_cases i <;> simp <;> omega
    have j1 := joins 1;  have j2 := joins 2;  have j3 := joins 3
    have j4 := joins 4;  have j5 := joins 5;  have j6 := joins 6
    have j7 := joins 7;  have j8 := joins 8;  have j9 := joins 9
    have j10 := joins 10; have j11 := joins 11; have j12 := joins 12
    have j13 := joins 13; have j14 := joins 14; have j15 := joins 15
    have d1 := divs 1;  have d2 := divs 2;  have d3 := divs 3
    have d4 := divs 4;  have d5 := divs 5;  have d6 := divs 6
    have d7 := divs 7;  have d8 := divs 8;  have d9 := divs 9
    have d10 := divs 10; have d11 := divs 11; have d12 := divs 12
    have d13 := divs 13; have d14 := divs 14; have d15 := divs 15
    simp at j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15
            d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    rw [j1, d1, j2, d2, j3, d3, j4, d4, j5, d5, j6, d6, j7, d7,
        j8, d8, j9, d9, j10, d10, j11, d11, j12, d12, j13, d13,
        j14, d14, j15]
    ring_nf
    omega

end MulGadget.Spec
