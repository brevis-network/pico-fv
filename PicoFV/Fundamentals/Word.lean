import PicoFV.Fundamentals.Core

@[reducible] def U32b := Vector (BitVec 8) 4
@[reducible] def U64b := Vector (BitVec 8) 8
@[reducible] def U64w := Vector (BitVec 16) 4
@[reducible] def U128w := Vector (BitVec 16) 8

set_option maxHeartbeats 1_000_000_000

namespace U32b

  /-- `U32b` as a vector of its constituents -/
  lemma destruct (x : U32b) : x = #v[x[0], x[1], x[2], x[3]] :=
    Vector.ext fun | 0, _ | 1, _ | 2, _ | 3, _ => by simp | n + 4, _ => by omega

  section toBV

    /-- From `U32b` to `BitVec 32` -/
    @[grind →]
    def toBV (x : U32b) : BitVec 32 := x[3] ++ x[2] ++ x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U32b} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      . simp [toBV] at h_eq_bv
        rw [destruct x, destruct y]
        grind

  end toBV

  section toNat_fromNat

    /-- From `U32b` to `ℕ` -/
    def toNat (x : U32b) : ℕ := x[0].toNat + x[1].toNat * 256 + x[2].toNat * 65536 + x[3].toNat * 16777216

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U32b} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      iterate 3 rw [BitVec.toNat_append,
                    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                    Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U32b) : x.toNat < 4294967296 := by simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U32b} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U32b` from a `ℕ` -/
    def fromNat (n : ℕ) : U32b :=
      #v[⟨n % 256, by omega⟩, ⟨ n / 256 % 256, by omega ⟩, ⟨ n / 65536 % 256, by omega ⟩, ⟨ n / 16777216 % 256, by omega ⟩ ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U32b} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 4 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ} (_ : n < 4294967296) : (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    grind_pattern BitVec.msb_eq_decide => x.msb

    /-- Negativity -/
    @[grind →]
    def negative (x : U32b) := ¬ (2 * x.toNat < 4294967296)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U32b} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top byte is the same as `negative` -/
    @[simp] lemma msb_3_negative {x : U32b} : x[3].msb = x.negative := by
      simp [← toBV_msb_negative]; grind

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_3_negative => x[3].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U32b` to `ℤ` -/
    @[grind →]
    def toInt (x : U32b) : ℤ := x.toNat - (if x.negative then 4294967296 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U32b} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U32b) : -2147483648 ≤ x.toInt ∧ x.toInt < 2147483648 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U32b} :
      x.toInt.bmod 4294967296 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U32b} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U32b} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U32b} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U32b` from an `ℤ` -/
    def fromInt (z : ℤ) : U32b :=
      let y := (z + if z < 0 then 4294967296 else 0).toNat
      #v[⟨y % 256, by omega⟩, ⟨ y / 256 % 256, by omega ⟩, ⟨ y / 65536 % 256, by omega ⟩, ⟨ y / 16777216 % 256, by omega ⟩ ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U32b} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 4 rw [← BitVec.toNat_inj]
        split_ands
        all_goals
          rw [BitVec.toNat_ofFin]; simp
          repeat rw [Int.toNat_add (by positivity) (by positivity)]
          repeat rw [Int.toNat_mul (by positivity) (by positivity)]
          simp; omega

    /-- `toInt`-`fromInt` invertibility -/
    lemma toInt_fromInt {z : ℤ} (_ : -2147483648 ≤ z) (_ : z < 2147483647) : (fromInt z).toInt = z := by
      simp [fromInt, toInt, toNat]; split_ifs with neg_z
      . rw [if_pos] <;> [ skip; simp [negative, toNat] ] <;> omega
      . rw [if_neg] <;> [ skip; simp [negative, toNat] ] <;> omega

  end toInt_fromInt

  section isolation

    @[simp]
    lemma isolate_byte_0
    :
      ((U32b.toNat #v[a, b, c, d] &&& 0xFF) : BitVec 8) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_byte_1
    :
      ((U32b.toNat #v[a, b, c, d] >>> 8 &&& 0xFF) : BitVec 8) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (b.toNat + c.toNat * 256 + d.toNat * 65536) % 256 &&& 255
      . congr; omega
      . trans b.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_2
    :
      ((U32b.toNat #v[a, b, c, d] >>> 16 &&& 0xFF) : BitVec 8) = c
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (c.toNat + d.toNat * 256) % 256 &&& 255
      . congr; omega
      . trans c.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_3
    :
      ((U32b.toNat #v[a, b, c, d] >>> 24) : BitVec 8) = d
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U32b

namespace U64b

  /-- `U64b` as a vector of its constituents -/
  lemma destruct (x : U64b) : x = #v[x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]] :=
    Vector.ext fun | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => by simp | n + 8, _ => by omega

  section toBV

    /-- From `U64b` to `BitVec 64` -/
    @[grind →]
    def toBV (x : U64b) : BitVec 64 := x[7] ++ x[6] ++ x[5] ++ x[4] ++ x[3] ++ x[2] ++ x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U64b} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      . simp [toBV] at h_eq_bv
        rw [destruct x, destruct y]
        grind

  end toBV

  section toNat_fromNat

    /-- From `U64b` to `ℕ` -/
    def toNat (x : U64b) : ℕ :=
      x[0].toNat + x[1].toNat * 256 + x[2].toNat * 65536 + x[3].toNat * 16777216 +
      x[4].toNat * 4294967296 + x[5].toNat * 1099511627776 +
      x[6].toNat * 281474976710656 + x[7].toNat * 72057594037927936

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U64b} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      iterate 7 rw [BitVec.toNat_append,
                    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                    Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U64b) : x.toNat < 18446744073709551616 := by simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U64b} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U64b` from a `ℕ` -/
    def fromNat (n : ℕ) : U64b :=
      #v[
        ⟨n % 256, by omega⟩,
        ⟨n / 256 % 256, by omega⟩,
        ⟨n / 65536 % 256, by omega⟩,
        ⟨n / 16777216 % 256, by omega⟩,
        ⟨n / 4294967296 % 256, by omega⟩,
        ⟨n / 1099511627776 % 256, by omega⟩,
        ⟨n / 281474976710656 % 256, by omega⟩,
        ⟨n / 72057594037927936 % 256, by omega⟩
      ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U64b} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 8 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ} (_ : n < 18446744073709551616) : (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    grind_pattern BitVec.msb_eq_decide => x.msb

    /-- Negativity -/
    @[grind →]
    def negative (x : U64b) := ¬ (2 * x.toNat < 18446744073709551616)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U64b} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top byte is the same as `negative` -/
    @[simp] lemma msb_7_negative {x : U64b} : x[7].msb = x.negative := by
      simp [← toBV_msb_negative]; grind

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_7_negative => x[7].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U64b` to `ℤ` -/
    @[grind →]
    def toInt (x : U64b) : ℤ := x.toNat - (if x.negative then 18446744073709551616 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U64b} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U64b) : -9223372036854775808 ≤ x.toInt ∧ x.toInt < 9223372036854775808 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U64b} :
      x.toInt.bmod 18446744073709551616 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U64b} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U64b} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U64b} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U64b` from an `ℤ` -/
    def fromInt (z : ℤ) : U64b :=
      let y := (z + if z < 0 then 18446744073709551616 else 0).toNat
      #v[
        ⟨y % 256, by omega⟩,
        ⟨y / 256 % 256, by omega⟩,
        ⟨y / 65536 % 256, by omega⟩,
        ⟨y / 16777216 % 256, by omega⟩,
        ⟨y / 4294967296 % 256, by omega⟩,
        ⟨y / 1099511627776 % 256, by omega⟩,
        ⟨y / 281474976710656 % 256, by omega⟩,
        ⟨y / 72057594037927936 % 256, by omega⟩
      ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U64b} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 8 rw [← BitVec.toNat_inj]
        split_ands
        all_goals
          rw [BitVec.toNat_ofFin]; simp
          repeat rw [Int.toNat_add (by positivity) (by positivity)]
          repeat rw [Int.toNat_mul (by positivity) (by positivity)]
          simp; omega

    /-- `toInt`-`fromInt` invertibility -/
    lemma toInt_fromInt {z : ℤ} (_ : -9223372036854775808 ≤ z) (_ : z < 9223372036854775807) : (fromInt z).toInt = z := by
      simp [fromInt, toInt, toNat]; split_ifs with neg_z
      . rw [if_pos] <;> [ skip; simp [negative, toNat] ] <;> omega
      . rw [if_neg] <;> [ skip; simp [negative, toNat] ] <;> omega

  end toInt_fromInt

  section isolation

    @[simp]
    lemma isolate_byte_0
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] &&& 0xFF) : BitVec 8) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_byte_1
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 8 &&& 0xFF) : BitVec 8) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (b.toNat + c.toNat * 256 + d.toNat * 65536 + e.toNat * 16777216
              + f.toNat * 4294967296 + g.toNat * 1099511627776
              + h.toNat * 281474976710656) % 256 &&& 255
      . congr; omega
      . trans b.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_2
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 16 &&& 0xFF) : BitVec 8) = c
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (c.toNat + d.toNat * 256 + e.toNat * 65536 + f.toNat * 16777216
              + g.toNat * 4294967296 + h.toNat * 1099511627776) % 256 &&& 255
      . congr; omega
      . trans c.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_3
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 24 &&& 0xFF) : BitVec 8) = d
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (d.toNat + e.toNat * 256 + f.toNat * 65536 + g.toNat * 16777216
              + h.toNat * 4294967296) % 256 &&& 255
      . congr; omega
      . trans d.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_4
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 32 &&& 0xFF) : BitVec 8) = e
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (e.toNat + f.toNat * 256 + g.toNat * 65536 + h.toNat * 16777216) % 256 &&& 255
      . congr; omega
      . trans e.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_5
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 40 &&& 0xFF) : BitVec 8) = f
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (f.toNat + g.toNat * 256 + h.toNat * 65536) % 256 &&& 255
      . congr; omega
      . trans f.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_6
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 48 &&& 0xFF) : BitVec 8) = g
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (g.toNat + h.toNat * 256) % 256 &&& 255
      . congr; omega
      . trans g.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_7
    :
      ((U64b.toNat #v[a, b, c, d, e, f, g, h] >>> 56) : BitVec 8) = h
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U64b

namespace U32b

  section extend

    /-- Sign-extender byte -/
    @[grind]
    def ext (w : U32b) (with_sign : Bool) := if with_sign && w.negative then 255 else 0

    lemma zero_le_ext w with_sign : 0 ≤ ext w with_sign := by grind
    lemma ext_le_255 w with_sign : ext w with_sign ≤ 255 := by grind

    /-- Sign-extension to 64 bits -/
    def extend (w : U32b) (with_sign : Bool) : U64b :=
      let ext := ext w with_sign
      #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

    /-- Compatibility of extensions -/
    lemma extend_BitVec_extend {w : U32b} {with_sign : Bool}
    :
      (w.extend with_sign).toBV = BitVec.extend w.toBV 64 with_sign
    := by
      rcases with_sign <;> simp [extend, BitVec.extend, ext, ← BitVec.toNat_inj]
      . simp [U64b.toNat, U32b.toNat]
        omega
      . rw [BitVec.toNat_signExtend]
        simp [U32b.toBV_msb_negative]
        by_cases w.negative
        all_goals
          simp_all
          simp only [toNat, U64b.toNat, Vector.getElem_mk,
                     List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                     BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          omega

    @[simp]
    lemma extend_toNat {w : U32b}
    :
      (w.extend false).toNat = w.toNat
    := by
      simp [extend, ext, U32b.toNat, toNat, U64b.toNat, toNat]

    @[simp]
    lemma extend_toInt {w : U32b}
    :
      (w.extend true).toInt = w.toInt
    := by
      simp [extend, ext, U64b.toInt, toInt, U64b.negative, negative, U64b.toNat, toNat]
      split_ifs <;> simp_all <;> omega

  end extend

end U32b

namespace U64w

  /-- `U64w` as a vector of its constituents -/
  lemma destruct (x : U64w) : x = #v[x[0], x[1], x[2], x[3]] :=
    Vector.ext fun | 0, _ | 1, _ | 2, _ | 3, _ => by simp | n + 4, _ => by omega

  section toBV

    /-- From `U64w` to `BitVec 64` -/
    @[grind →]
    def toBV (x : U64w) : BitVec 64 := x[3] ++ x[2] ++ x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U64w} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      . simp [toBV] at h_eq_bv
        rw [destruct x, destruct y]
        grind

  end toBV

  section toNat_fromNat

    /-- From `U64w` to `ℕ` -/
    def toNat (x : U64w) : ℕ :=
      x[0].toNat + x[1].toNat * 65536 + x[2].toNat * 4294967296 + x[3].toNat * 281474976710656

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U64w} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      iterate 3 rw [BitVec.toNat_append,
                    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                    Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U64w) : x.toNat < 18446744073709551616 := by simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U64w} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U64w` from a `ℕ` -/
    def fromNat (n : ℕ) : U64w :=
      #v[
        ⟨n % 65536, by omega⟩,
        ⟨n / 65536 % 65536, by omega⟩,
        ⟨n / 4294967296 % 65536, by omega⟩,
        ⟨n / 281474976710656 % 65536, by omega⟩
      ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U64w} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 4 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ} (_ : n < 18446744073709551616) : (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    /-- Negativity -/
    @[grind →]
    def negative (x : U64w) := ¬ (2 * x.toNat < 18446744073709551616)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U64w} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top limb is the same as `negative` -/
    @[simp] lemma msb_3_negative {x : U64w} : x[3].msb = x.negative := by
      simp [← toBV_msb_negative]; grind

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_3_negative => x[3].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U64w` to `ℤ` -/
    @[grind →]
    def toInt (x : U64w) : ℤ := x.toNat - (if x.negative then 18446744073709551616 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U64w} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U64w) : -9223372036854775808 ≤ x.toInt ∧ x.toInt < 9223372036854775808 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U64w} :
      x.toInt.bmod 18446744073709551616 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U64w} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U64w} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U64w} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U64w` from an `ℤ` -/
    def fromInt (z : ℤ) : U64w :=
      let y := (z + if z < 0 then 18446744073709551616 else 0).toNat
      #v[
        ⟨y % 65536, by omega⟩,
        ⟨y / 65536 % 65536, by omega⟩,
        ⟨y / 4294967296 % 65536, by omega⟩,
        ⟨y / 281474976710656 % 65536, by omega⟩
      ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U64w} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 4 rw [← BitVec.toNat_inj]
        split_ands
        all_goals
          rw [BitVec.toNat_ofFin]; simp
          repeat rw [Int.toNat_add (by positivity) (by positivity)]
          repeat rw [Int.toNat_mul (by positivity) (by positivity)]
          simp; omega

    /-- `toInt`-`fromInt` invertibility -/
    lemma toInt_fromInt {z : ℤ} (_ : -9223372036854775808 ≤ z) (_ : z < 9223372036854775807) : (fromInt z).toInt = z := by
      simp [fromInt, toInt, toNat]; split_ifs with neg_z
      . rw [if_pos] <;> [ skip; simp [negative, toNat] ] <;> omega
      . rw [if_neg] <;> [ skip; simp [negative, toNat] ] <;> omega

  end toInt_fromInt

  section isolation

    @[simp]
    lemma isolate_limb_0
    :
      ((U64w.toNat #v[a, b, c, d] &&& 0xFFFF) : BitVec 16) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_limb_1
    :
      ((U64w.toNat #v[a, b, c, d] >>> 16 &&& 0xFFFF) : BitVec 16) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (b.toNat + c.toNat * 65536 + d.toNat * 4294967296) % 65536 &&& 65535
      . congr; omega
      . trans b.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_2
    :
      ((U64w.toNat #v[a, b, c, d] >>> 32 &&& 0xFFFF) : BitVec 16) = c
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (c.toNat + d.toNat * 65536) % 65536 &&& 65535
      . congr; omega
      . trans c.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_3
    :
      ((U64w.toNat #v[a, b, c, d] >>> 48) : BitVec 16) = d
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U64w

namespace U128w

  /-- `U128w` as a vector of its constituents -/
  lemma destruct (x : U128w) : x = #v[x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]] :=
    Vector.ext fun | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => by simp | n + 8, _ => by omega

  section toBV

    /-- From `U128w` to `BitVec 128` -/
    @[grind →]
    def toBV (x : U128w) : BitVec 128 := x[7] ++ x[6] ++ x[5] ++ x[4] ++ x[3] ++ x[2] ++ x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U128w} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      . simp [toBV] at h_eq_bv
        rw [destruct x, destruct y]
        grind

  end toBV

  section toNat_fromNat

    /-- From `U128w` to `ℕ` -/
    def toNat (x : U128w) : ℕ :=
      x[0].toNat + x[1].toNat * 65536 + x[2].toNat * 4294967296 + x[3].toNat * 281474976710656 +
      x[4].toNat * 18446744073709551616 + x[5].toNat * 1208925819614629174706176 +
      x[6].toNat * 79228162514264337593543950336 + x[7].toNat * 5192296858534827628530496329220096

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U128w} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      iterate 7 rw [BitVec.toNat_append,
                    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                    Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U128w) : x.toNat < 340282366920938463463374607431768211456 := by simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U128w} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U128w` from a `ℕ` -/
    def fromNat (n : ℕ) : U128w :=
      #v[
        ⟨n % 65536, by omega⟩,
        ⟨n / 65536 % 65536, by omega⟩,
        ⟨n / 4294967296 % 65536, by omega⟩,
        ⟨n / 281474976710656 % 65536, by omega⟩,
        ⟨n / 18446744073709551616 % 65536, by omega⟩,
        ⟨n / 1208925819614629174706176 % 65536, by omega⟩,
        ⟨n / 79228162514264337593543950336 % 65536, by omega⟩,
        ⟨n / 5192296858534827628530496329220096 % 65536, by omega⟩
      ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U128w} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 8 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ} (_ : n < 340282366920938463463374607431768211456) : (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    /-- Negativity -/
    @[grind →]
    def negative (x : U128w) := ¬ (2 * x.toNat < 340282366920938463463374607431768211456)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U128w} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top limb is the same as `negative` -/
    @[simp] lemma msb_7_negative {x : U128w} : x[7].msb = x.negative := by
      simp [← toBV_msb_negative]; grind

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_7_negative => x[7].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U128w` to `ℤ` -/
    @[grind →]
    def toInt (x : U128w) : ℤ := x.toNat - (if x.negative then 340282366920938463463374607431768211456 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U128w} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U128w) :
      -170141183460469231731687303715884105728 ≤ x.toInt ∧
      x.toInt < 170141183460469231731687303715884105728 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U128w} :
      x.toInt.bmod 340282366920938463463374607431768211456 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U128w} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U128w} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U128w} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U128w` from an `ℤ` -/
    def fromInt (z : ℤ) : U128w :=
      let y := (z + if z < 0 then 340282366920938463463374607431768211456 else 0).toNat
      #v[
        ⟨y % 65536, by omega⟩,
        ⟨y / 65536 % 65536, by omega⟩,
        ⟨y / 4294967296 % 65536, by omega⟩,
        ⟨y / 281474976710656 % 65536, by omega⟩,
        ⟨y / 18446744073709551616 % 65536, by omega⟩,
        ⟨y / 1208925819614629174706176 % 65536, by omega⟩,
        ⟨y / 79228162514264337593543950336 % 65536, by omega⟩,
        ⟨y / 5192296858534827628530496329220096 % 65536, by omega⟩
      ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U128w} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 8 rw [← BitVec.toNat_inj]
        split_ands
        all_goals
          rw [BitVec.toNat_ofFin]; simp
          repeat rw [Int.toNat_add (by positivity) (by positivity)]
          repeat rw [Int.toNat_mul (by positivity) (by positivity)]
          simp; omega

    /-- `toInt`-`fromInt` invertibility -/
    lemma toInt_fromInt {z : ℤ}
        (_ : -170141183460469231731687303715884105728 ≤ z)
        (_ : z < 170141183460469231731687303715884105727) :
        (fromInt z).toInt = z := by
      simp [fromInt, toInt, toNat]; split_ifs with neg_z
      . rw [if_pos] <;> [ skip; simp [negative, toNat] ] <;> omega
      . rw [if_neg] <;> [ skip; simp [negative, toNat] ] <;> omega

  end toInt_fromInt

  section isolation

    @[simp]
    lemma isolate_limb_0
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] &&& 0xFFFF) : BitVec 16) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_limb_1
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 16 &&& 0xFFFF) : BitVec 16) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (b.toNat + c.toNat * 65536 + d.toNat * 4294967296
              + e.toNat * 281474976710656 + f.toNat * 18446744073709551616
              + g.toNat * 1208925819614629174706176
              + h.toNat * 79228162514264337593543950336) % 65536 &&& 65535
      . congr; omega
      . trans b.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_2
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 32 &&& 0xFFFF) : BitVec 16) = c
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (c.toNat + d.toNat * 65536 + e.toNat * 4294967296
              + f.toNat * 281474976710656 + g.toNat * 18446744073709551616
              + h.toNat * 1208925819614629174706176) % 65536 &&& 65535
      . congr; omega
      . trans c.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_3
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 48 &&& 0xFFFF) : BitVec 16) = d
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (d.toNat + e.toNat * 65536 + f.toNat * 4294967296
              + g.toNat * 281474976710656 + h.toNat * 18446744073709551616) % 65536 &&& 65535
      . congr; omega
      . trans d.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_4
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 64 &&& 0xFFFF) : BitVec 16) = e
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (e.toNat + f.toNat * 65536 + g.toNat * 4294967296
              + h.toNat * 281474976710656) % 65536 &&& 65535
      . congr; omega
      . trans e.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_5
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 80 &&& 0xFFFF) : BitVec 16) = f
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (f.toNat + g.toNat * 65536 + h.toNat * 4294967296) % 65536 &&& 65535
      . congr; omega
      . trans f.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_6
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 96 &&& 0xFFFF) : BitVec 16) = g
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (g.toNat + h.toNat * 65536) % 65536 &&& 65535
      . congr; omega
      . trans g.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_7
    :
      ((U128w.toNat #v[a, b, c, d, e, f, g, h] >>> 112) : BitVec 16) = h
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U128w

namespace U64w

  section extend

    /-- Sign-extender u16 limb -/
    @[grind]
    def ext (w : U64w) (with_sign : Bool) := if with_sign && w.negative then 65535 else 0

    lemma zero_le_ext w with_sign : 0 ≤ ext w with_sign := by grind
    lemma ext_le_65535 w with_sign : ext w with_sign ≤ 65535 := by grind

    /-- Sign-extension to 128 bits -/
    def extend (w : U64w) (with_sign : Bool) : U128w :=
      let ext := ext w with_sign
      #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

    /-- Compatibility of extensions -/
    lemma extend_BitVec_extend {w : U64w} {with_sign : Bool}
    :
      (w.extend with_sign).toBV = BitVec.extend w.toBV 128 with_sign
    := by
      rcases with_sign <;> simp [extend, BitVec.extend, ext, ← BitVec.toNat_inj]
      . simp [U128w.toNat, U64w.toNat]
        omega
      . rw [BitVec.toNat_signExtend]
        simp [U64w.toBV_msb_negative]
        by_cases w.negative
        all_goals
          simp_all
          simp only [toNat, U128w.toNat, Vector.getElem_mk,
                     List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                     BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          omega

    @[simp]
    lemma extend_toNat {w : U64w}
    :
      (w.extend false).toNat = w.toNat
    := by
      simp [extend, ext, U64w.toNat, toNat, U128w.toNat, toNat]

    @[simp]
    lemma extend_toInt {w : U64w}
    :
      (w.extend true).toInt = w.toInt
    := by
      simp [extend, ext, U128w.toInt, toInt, U128w.negative, negative, U128w.toNat, toNat]
      split_ifs <;> simp_all <;> omega

  end extend

end U64w
