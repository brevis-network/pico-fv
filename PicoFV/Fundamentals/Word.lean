import PicoFV.Fundamentals.Core

@[reducible] def U32b := Vector (BitVec 8) 4
@[reducible] def U64b := Vector (BitVec 8) 8
@[reducible] def U128b := Vector (BitVec 8) 16
@[reducible] def U32w := Vector (BitVec 16) 2
@[reducible] def U48w := Vector (BitVec 16) 3
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

namespace U32w

  /-- `U32w` as a vector of its constituents -/
  lemma destruct (x : U32w) : x = #v[x[0], x[1]] :=
    Vector.ext fun | 0, _ | 1, _ => by simp | n + 2, _ => by omega

  section toBV

    /-- From `U32w` to `BitVec 32` -/
    @[grind →]
    def toBV (x : U32w) : BitVec 32 := x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U32w} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      . simp [toBV] at h_eq_bv
        rw [destruct x, destruct y]
        grind

  end toBV

  section toNat_fromNat

    /-- From `U32w` to `ℕ` -/
    def toNat (x : U32w) : ℕ :=
      x[0].toNat + x[1].toNat * 65536

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U32w} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      rw [BitVec.toNat_append,
          ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
          Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U32w) : x.toNat < 4294967296 := by simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U32w} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U32w` from a `ℕ` -/
    def fromNat (n : ℕ) : U32w :=
      #v[
        ⟨n % 65536, by omega⟩,
        ⟨n / 65536 % 65536, by omega⟩
      ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U32w} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 2 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ} (_ : n < 4294967296) : (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    /-- Negativity -/
    @[grind →]
    def negative (x : U32w) := ¬ (2 * x.toNat < 4294967296)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U32w} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top limb is the same as `negative` -/
    @[simp] lemma msb_1_negative {x : U32w} : x[1].msb = x.negative := by
      simp [← toBV_msb_negative]; grind

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_1_negative => x[1].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U32w` to `ℤ` -/
    @[grind →]
    def toInt (x : U32w) : ℤ := x.toNat - (if x.negative then 4294967296 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U32w} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U32w) : -2147483648 ≤ x.toInt ∧ x.toInt < 2147483648 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U32w} :
      x.toInt.bmod 4294967296 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U32w} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U32w} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U32w} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U32w` from an `ℤ` -/
    def fromInt (z : ℤ) : U32w :=
      let y := (z + if z < 0 then 4294967296 else 0).toNat
      #v[
        ⟨y % 65536, by omega⟩,
        ⟨y / 65536 % 65536, by omega⟩
      ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U32w} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 2 rw [← BitVec.toNat_inj]
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
    lemma isolate_limb_0
    :
      ((U32w.toNat #v[a, b] &&& 0xFFFF) : BitVec 16) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_limb_1
    :
      ((U32w.toNat #v[a, b] >>> 16) : BitVec 16) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U32w

namespace U48w

  /-- `U48w` as a vector of its constituents -/
  lemma destruct (x : U48w) : x = #v[x[0], x[1], x[2]] :=
    Vector.ext fun | 0, _ | 1, _ | 2, _ => by simp | n + 3, _ => by omega

  section toBV

    /-- From `U48w` to `BitVec 48` -/
    @[grind →]
    def toBV (x : U48w) : BitVec 48 := x[2] ++ x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U48w} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      . simp [toBV] at h_eq_bv
        rw [destruct x, destruct y]
        grind

  end toBV

  section toNat_fromNat

    /-- From `U48w` to `ℕ` -/
    def toNat (x : U48w) : ℕ :=
      x[0].toNat + x[1].toNat * 65536 + x[2].toNat * 4294967296

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U48w} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      iterate 2 rw [BitVec.toNat_append,
                    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                    Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U48w) : x.toNat < 281474976710656 := by simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U48w} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U48w` from a `ℕ` -/
    def fromNat (n : ℕ) : U48w :=
      #v[
        ⟨n % 65536, by omega⟩,
        ⟨n / 65536 % 65536, by omega⟩,
        ⟨n / 4294967296 % 65536, by omega⟩
      ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U48w} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 3 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ} (_ : n < 281474976710656) : (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    /-- Negativity -/
    @[grind →]
    def negative (x : U48w) := ¬ (2 * x.toNat < 281474976710656)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U48w} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top limb is the same as `negative` -/
    @[simp] lemma msb_2_negative {x : U48w} : x[2].msb = x.negative := by
      simp [← toBV_msb_negative]; grind

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_2_negative => x[2].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U48w` to `ℤ` -/
    @[grind →]
    def toInt (x : U48w) : ℤ := x.toNat - (if x.negative then 281474976710656 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U48w} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U48w) : -140737488355328 ≤ x.toInt ∧ x.toInt < 140737488355328 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U48w} :
      x.toInt.bmod 281474976710656 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U48w} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U48w} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U48w} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U48w` from an `ℤ` -/
    def fromInt (z : ℤ) : U48w :=
      let y := (z + if z < 0 then 281474976710656 else 0).toNat
      #v[
        ⟨y % 65536, by omega⟩,
        ⟨y / 65536 % 65536, by omega⟩,
        ⟨y / 4294967296 % 65536, by omega⟩
      ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U48w} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 3 rw [← BitVec.toNat_inj]
        split_ands
        all_goals
          rw [BitVec.toNat_ofFin]; simp
          repeat rw [Int.toNat_add (by positivity) (by positivity)]
          repeat rw [Int.toNat_mul (by positivity) (by positivity)]
          simp; omega

    /-- `toInt`-`fromInt` invertibility -/
    lemma toInt_fromInt {z : ℤ} (_ : -140737488355328 ≤ z) (_ : z < 140737488355327) :
        (fromInt z).toInt = z := by
      simp [fromInt, toInt, toNat]; split_ifs with neg_z
      . rw [if_pos] <;> [ skip; simp [negative, toNat] ] <;> omega
      . rw [if_neg] <;> [ skip; simp [negative, toNat] ] <;> omega

  end toInt_fromInt

  section isolation

    @[simp]
    lemma isolate_limb_0
    :
      ((U48w.toNat #v[a, b, c] &&& 0xFFFF) : BitVec 16) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_limb_1
    :
      ((U48w.toNat #v[a, b, c] >>> 16 &&& 0xFFFF) : BitVec 16) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (b.toNat + c.toNat * 65536) % 65536 &&& 65535
      . congr; omega
      . trans b.toNat &&& (65535 : BitVec 16).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_limb_2
    :
      ((U48w.toNat #v[a, b, c] >>> 32) : BitVec 16) = c
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U48w

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

namespace U32w

  section extend

    /-- Sign-extender u16 limb -/
    @[grind]
    def ext (w : U32w) (with_sign : Bool) := if with_sign && w.negative then 65535 else 0

    lemma zero_le_ext w with_sign : 0 ≤ ext w with_sign := by grind
    lemma ext_le_65535 w with_sign : ext w with_sign ≤ 65535 := by grind

    /-- Sign-extension to 64 bits -/
    def extend (w : U32w) (with_sign : Bool) : U64w :=
      let ext := ext w with_sign
      #v[w[0], w[1], ext, ext]

    /-- Compatibility of extensions -/
    lemma extend_BitVec_extend {w : U32w} {with_sign : Bool}
    :
      (w.extend with_sign).toBV = BitVec.extend w.toBV 64 with_sign
    := by
      rcases with_sign <;> simp [extend, BitVec.extend, ext, ← BitVec.toNat_inj]
      . simp [U64w.toNat, U32w.toNat]
        omega
      . rw [BitVec.toNat_signExtend]
        simp [U32w.toBV_msb_negative]
        by_cases w.negative
        all_goals
          simp_all
          simp only [toNat, U64w.toNat, Vector.getElem_mk,
                     List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                     BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          omega

    @[simp]
    lemma extend_toNat {w : U32w}
    :
      (w.extend false).toNat = w.toNat
    := by
      simp [extend, ext, U32w.toNat, toNat, U64w.toNat, toNat]

    @[simp]
    lemma extend_toInt {w : U32w}
    :
      (w.extend true).toInt = w.toInt
    := by
      simp [extend, ext, U64w.toInt, toInt, U64w.negative, negative, U64w.toNat, toNat]
      split_ifs <;> simp_all <;> omega

  end extend

end U32w

namespace U64w

  section contract

    /-- Contraction of a `U64w` to a `U32w` by keeping the low 2 × u16
        limbs (the bottom 32 bits). The high two limbs are discarded.
        This is the `BitVec.setWidth 32` operation lifted to the `U64w` /
        `U32w` representations. -/
    def contract (w : U64w) : U32w := #v[w[0], w[1]]

    /-- Compatibility with `BitVec.setWidth`: contraction is precisely
        the `setWidth 32` operation on the `BitVec 64` representation. -/
    @[simp]
    lemma contract_toBV {w : U64w} :
      (contract w).toBV = w.toBV.setWidth 32
    := by
      rw [← BitVec.toNat_inj, BitVec.toNat_setWidth,
          U32w.toBV_toNat, U64w.toBV_toNat]
      simp [contract, U32w.toNat, U64w.toNat]
      omega

    /-- `toNat` compatibility: contraction takes the value mod `2^32`. -/
    @[simp]
    lemma contract_toNat {w : U64w} :
      (contract w).toNat = w.toNat % 4294967296
    := by
      simp [contract, U32w.toNat, U64w.toNat]
      omega

    /-- Round-trip: contracting an extension recovers the original
        (independent of sign-extension flag — `contract` discards exactly
        the bits `extend` populates). -/
    @[simp]
    lemma contract_extend {w : U32w} {with_sign : Bool} :
      U64w.contract (w.extend with_sign) = w
    := by
      rw [U32w.destruct w]
      rfl

    /-- Reshape `(U64w.toBV w).setWidth 32` into the `U32w.toBV` of the
        first two limbs — the reverse-direction sibling of `contract_toBV`.
        Useful when a spec speaks of `b.setWidth 32` (e.g. the W-variant
        opcodes in `ALUBus.Spec`) but the chip witnesses are exposed
        as a u16-limb pair `#v[w[0], w[1]]`. -/
    @[simp]
    lemma setWidth_32_eq_low_U32w (w : U64w) :
      (w.toBV).setWidth 32 = U32w.toBV #v[w[0], w[1]]
    := by
      rw [← contract_toBV]; rfl

  end contract

end U64w

-- =========================================================================
-- U64w ↔ U64b conversion (byte view of a u16-limb word)
--
-- Useful for chips that constrain operands at u16 limb level but emit
-- byte-bus interactions on the constituent bytes (Bitwise, Mul). The
-- conversion is value-preserving on `BitVec 64` and forms a round-trip.
-- Byte ordering is little-endian within each limb:
--   `(toU64b w)[2*i]`   = low byte of `w[i]`
--   `(toU64b w)[2*i+1]` = high byte of `w[i]`
-- =========================================================================

namespace U64w

  section toU64b

    /-- Split each u16 limb into its low and high bytes, yielding a
        `U64b` with the same underlying `BitVec 64`. -/
    def toU64b (w : U64w) : U64b :=
      #v[ w[0].setWidth 8, (w[0] >>> 8).setWidth 8,
          w[1].setWidth 8, (w[1] >>> 8).setWidth 8,
          w[2].setWidth 8, (w[2] >>> 8).setWidth 8,
          w[3].setWidth 8, (w[3] >>> 8).setWidth 8 ]

    /-- `toU64b` preserves the underlying `BitVec 64`. -/
    @[simp]
    lemma toU64b_toBV {w : U64w} : (toU64b w).toBV = w.toBV := by
      apply BitVec.eq_of_toNat_eq
      rw [U64b.toBV_toNat, U64w.toBV_toNat]
      simp [toU64b, U64b.toNat, U64w.toNat,
            BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
      have h0 := (w[0]).isLt
      have h1 := (w[1]).isLt
      have h2 := (w[2]).isLt
      have h3 := (w[3]).isLt
      simp at h0 h1 h2 h3
      omega

    /-- `toU64b` preserves the underlying natural number. -/
    @[simp]
    lemma toU64b_toNat {w : U64w} : (toU64b w).toNat = w.toNat := by
      rw [← U64b.toBV_toNat, toU64b_toBV, U64w.toBV_toNat]

    /-- `toU64b` preserves the underlying signed integer. -/
    @[simp]
    lemma toU64b_toInt {w : U64w} : (toU64b w).toInt = w.toInt := by
      rw [← U64b.toBV_toInt, toU64b_toBV, U64w.toBV_toInt]

    lemma toU64b_from_split {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8} :
      (toU64b #v[b1 ++ b0, b3 ++ b2, b5 ++ b4, b7 ++ b6]).toBV =
      U64b.toBV #v[b0, b1, b2, b3, b4, b5, b6, b7]
    := by
      unfold toU64b U64b.toBV; simp
      bv_decide

  end toU64b

end U64w

namespace U64b

  section toU64w

    /-- Combine pairs of bytes into u16 limbs, yielding a `U64w` with
        the same underlying `BitVec 64`. Dual of `U64w.toU64b`. -/
    def toU64w (b : U64b) : U64w :=
      #v[ b[1] ++ b[0], b[3] ++ b[2], b[5] ++ b[4], b[7] ++ b[6] ]

    /-- `toU64w` preserves the underlying `BitVec 64`. -/
    @[simp]
    lemma toU64w_toBV {b : U64b} : (toU64w b).toBV = b.toBV := by
      apply BitVec.eq_of_toNat_eq
      rw [U64w.toBV_toNat, U64b.toBV_toNat]
      simp [toU64w, U64w.toNat, U64b.toNat]
      iterate 4 rw [BitVec.toNat_append,
                    ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                    Nat.shiftLeft_eq]
      omega

    /-- `toU64w` preserves the underlying natural number. -/
    @[simp]
    lemma toU64w_toNat {b : U64b} : (toU64w b).toNat = b.toNat := by
      rw [← U64w.toBV_toNat, toU64w_toBV, U64b.toBV_toNat]

    /-- `toU64w` preserves the underlying signed integer. -/
    @[simp]
    lemma toU64w_toInt {b : U64b} : (toU64w b).toInt = b.toInt := by
      rw [← U64w.toBV_toInt, toU64w_toBV, U64b.toBV_toInt]

    /-- Round-trip: byte view → limb view → byte view recovers original. -/
    @[simp]
    lemma toU64w_toU64b {b : U64b} : U64w.toU64b (toU64w b) = b := by
      apply U64b.toBV_inj
      rw [U64w.toU64b_toBV, toU64w_toBV]

  end toU64w

end U64b

namespace U64w

  /-- Round-trip: limb view → byte view → limb view recovers original. -/
  @[simp]
  lemma toU64b_toU64w {w : U64w} : U64b.toU64w (toU64b w) = w := by
    apply U64w.toBV_inj
    rw [U64b.toU64w_toBV, toU64b_toBV]

end U64w

namespace U128b

  /-- `U128b` as a vector of its constituents -/
  lemma destruct (x : U128b)
  : x = #v[ x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
            x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15] ]
  := Vector.ext fun
      | 0, _  | 1, _  | 2, _  | 3, _  | 4, _  | 5, _  | 6, _  | 7, _
      | 8, _  | 9, _  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => by simp
      | n + 16, _ => by omega

  section toBV

    /-- From `U128b` to `BitVec 128` -/
    @[grind →]
    def toBV (x : U128b) : BitVec 128 :=
      x[15] ++ x[14] ++ x[13] ++ x[12] ++ x[11] ++ x[10] ++ x[9] ++ x[8] ++
      x[7] ++ x[6] ++ x[5] ++ x[4] ++ x[3] ++ x[2] ++ x[1] ++ x[0]

    /-- Injectivity of `toBV` -/
    @[simp, grind →]
    lemma toBV_inj {x y : U128b} : x.toBV = y.toBV → x = y := by
      intro h_eq_bv
      simp [toBV] at h_eq_bv
      rw [destruct x, destruct y]
      grind

  end toBV

  section toNat_fromNat

    /-- From `U128b` to `ℕ`. -/
    def toNat (x : U128b) : ℕ :=
      x[0].toNat
      + x[1].toNat  * 256
      + x[2].toNat  * 65536
      + x[3].toNat  * 16777216
      + x[4].toNat  * 4294967296
      + x[5].toNat  * 1099511627776
      + x[6].toNat  * 281474976710656
      + x[7].toNat  * 72057594037927936
      + x[8].toNat  * 18446744073709551616
      + x[9].toNat  * 4722366482869645213696
      + x[10].toNat * 1208925819614629174706176
      + x[11].toNat * 309485009821345068724781056
      + x[12].toNat * 79228162514264337593543950336
      + x[13].toNat * 20282409603651670423947251286016
      + x[14].toNat * 5192296858534827628530496329220096
      + x[15].toNat * 1329227995784915872903807060280344576

    /-- `toNat` compatibility with `toBV` -/
    @[simp]
    lemma toBV_toNat {x : U128b} : x.toBV.toNat = x.toNat := by
      simp [toNat, toBV]
      iterate 15 rw [BitVec.toNat_append,
                     ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                     Nat.shiftLeft_eq]
      omega

    /-- Upper bound of `toNat` -/
    lemma toNat_ub (x : U128b)
    : x.toNat < 340282366920938463463374607431768211456 := by
      simp [toNat]; omega

    grind_pattern toBV_toNat => x.toBV.toNat
    grind_pattern toNat_ub => x.toNat

    /-- Injectivity of `toNat` -/
    @[simp, grind →]
    lemma toNat_inj {x y : U128b} : x.toNat = y.toNat → x = y := by
      rw [← toBV_toNat, ← toBV_toNat, BitVec.toNat_inj]
      exact toBV_inj

    /-- Reconstructing a `U128b` from a `ℕ` -/
    def fromNat (n : ℕ) : U128b :=
      #v[
        ⟨n % 256, by omega⟩,
        ⟨n / 256 % 256, by omega⟩,
        ⟨n / 65536 % 256, by omega⟩,
        ⟨n / 16777216 % 256, by omega⟩,
        ⟨n / 4294967296 % 256, by omega⟩,
        ⟨n / 1099511627776 % 256, by omega⟩,
        ⟨n / 281474976710656 % 256, by omega⟩,
        ⟨n / 72057594037927936 % 256, by omega⟩,
        ⟨n / 18446744073709551616 % 256, by omega⟩,
        ⟨n / 4722366482869645213696 % 256, by omega⟩,
        ⟨n / 1208925819614629174706176 % 256, by omega⟩,
        ⟨n / 309485009821345068724781056 % 256, by omega⟩,
        ⟨n / 79228162514264337593543950336 % 256, by omega⟩,
        ⟨n / 20282409603651670423947251286016 % 256, by omega⟩,
        ⟨n / 5192296858534827628530496329220096 % 256, by omega⟩,
        ⟨n / 1329227995784915872903807060280344576 % 256, by omega⟩
      ]

    /-- `fromNat`-`toNat` invertibility -/
    lemma fromNat_toNat {x : U128b} : fromNat x.toNat = x := by
      rw [destruct x]; simp [fromNat, toNat]
      iterate 16 rw [← BitVec.toNat_inj]
      split_ands
      all_goals
        rw [BitVec.toNat_ofFin]; simp; omega

    /-- `toNat`-`fromNat` invertibility -/
    lemma toNat_fromNat {n : ℕ}
        (_ : n < 340282366920938463463374607431768211456) :
        (fromNat n).toNat = n := by
      simp [fromNat, toNat]; omega

  end toNat_fromNat

  section negative

    /-- Negativity -/
    @[grind →]
    def negative (x : U128b) :=
      ¬ (2 * x.toNat < 340282366920938463463374607431768211456)
    instance : Decidable (negative x) := by unfold negative; infer_instance

    /-- `msb` is `negative` -/
    @[simp]
    lemma toBV_msb_negative {x : U128b} : x.toBV.msb = x.negative := by grind

    /-- `msb` of top byte is the same as `negative` -/
    @[simp] lemma msb_15_negative {x : U128b} : x[15].msb = x.negative := by
      simp [← toBV_msb_negative, U128b.toBV]
      repeat (rw [BitVec.msb_append]; simp)

    grind_pattern toBV_msb_negative => x.toBV.msb
    grind_pattern msb_15_negative => x[15].msb

  end negative

  section toInt_fromInt

    attribute [local grind →] BitVec.toInt

    /-- From `U128b` to `ℤ` -/
    @[grind →]
    def toInt (x : U128b) : ℤ :=
      x.toNat - (if x.negative then 340282366920938463463374607431768211456 else 0)

    /-- `toBV` compatibility with `toInt` -/
    @[simp]
    lemma toBV_toInt {x : U128b} : x.toBV.toInt = x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Range of `toInt` -/
    lemma toInt_range (x : U128b) :
      -170141183460469231731687303715884105728 ≤ x.toInt ∧
      x.toInt < 170141183460469231731687303715884105728 := by
      simp [toInt]; split_ifs <;> grind

    lemma toInt_bmod_eq {x : U128b} :
      x.toInt.bmod 340282366920938463463374607431768211456 = x.toInt
    := by
      have := toInt_range x
      rw [Int.bmod_eq_of_le this.1 this.2]

    grind_pattern toBV_toInt => x.toBV.toInt
    grind_pattern toInt_range => x.toInt

    /-- Injectivity of `toInt` -/
    @[simp, grind →]
    lemma toInt_inj {x y : U128b} : x.toInt = y.toInt → x = y := by
      rw [← toBV_toInt, ← toBV_toInt, BitVec.toInt_inj]
      exact toBV_inj

    /-- `negative` in terms of `toInt` -/
    lemma negative_toInt {x : U128b} : negative x ↔ ¬ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- not `negative` in terms of `toInt` -/
    lemma not_negative_toInt {x : U128b} : ¬ negative x ↔ 0 ≤ x.toInt := by
      simp [toInt]; split_ifs <;> grind

    /-- Reconstructing a `U128b` from an `ℤ` -/
    def fromInt (z : ℤ) : U128b :=
      let y := (z + if z < 0 then 340282366920938463463374607431768211456 else 0).toNat
      #v[
        ⟨y % 256, by omega⟩,
        ⟨y / 256 % 256, by omega⟩,
        ⟨y / 65536 % 256, by omega⟩,
        ⟨y / 16777216 % 256, by omega⟩,
        ⟨y / 4294967296 % 256, by omega⟩,
        ⟨y / 1099511627776 % 256, by omega⟩,
        ⟨y / 281474976710656 % 256, by omega⟩,
        ⟨y / 72057594037927936 % 256, by omega⟩,
        ⟨y / 18446744073709551616 % 256, by omega⟩,
        ⟨y / 4722366482869645213696 % 256, by omega⟩,
        ⟨y / 1208925819614629174706176 % 256, by omega⟩,
        ⟨y / 309485009821345068724781056 % 256, by omega⟩,
        ⟨y / 79228162514264337593543950336 % 256, by omega⟩,
        ⟨y / 20282409603651670423947251286016 % 256, by omega⟩,
        ⟨y / 5192296858534827628530496329220096 % 256, by omega⟩,
        ⟨y / 1329227995784915872903807060280344576 % 256, by omega⟩
      ]

    /-- `fromInt`-`toInt` invertibility -/
    @[simp]
    lemma fromInt_toInt {x : U128b} : fromInt x.toInt = x := by
      rw [toInt]; simp [negative]; split_ifs with neg_x
      all_goals
        simp [fromInt]; simp [toNat] at *
        split_ifs with neg <;> try omega
        conv => rhs; rw [destruct x]
        simp; iterate 16 rw [← BitVec.toNat_inj]
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

  section extractLsb

    /-- Low 64 bits of a 16-byte `U128b` are the first 8 bytes (as a `U64b`). -/
    @[simp]
    lemma extractLsb_low_64 (x : U128b)
    : BitVec.extractLsb 63 0 x.toBV =
        U64b.toBV #v[x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]]
    := by
      simp [← BitVec.toNat_inj, toNat, U64b.toNat]
      have := U64b.toNat_ub #v[x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]]
      simp [U64b.toNat] at this
      omega

    /-- High 64 bits of a 16-byte `U128b` are the last 8 bytes (as a `U64b`). -/
    @[simp]
    lemma extractLsb_high_64 (x : U128b)
    : BitVec.extractLsb 127 64 x.toBV =
        U64b.toBV #v[x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15]]
    := by
      simp [← BitVec.toNat_inj, toNat, U64b.toNat]
      omega

    /-- Low 32 bits of a 16-byte `U128b` are the first 4 bytes (as a `U32b`). -/
    @[simp]
    lemma extractLsb_low_32 (x : U128b)
    : BitVec.extractLsb 31 0 x.toBV =
        U32b.toBV #v[x[0], x[1], x[2], x[3]]
    := by
      simp [← BitVec.toNat_inj, toNat, U32b.toNat]
      have := U32b.toNat_ub #v[x[0], x[1], x[2], x[3]]
      simp [U32b.toNat] at this
      omega

  end extractLsb

  section isolation

    @[simp]
    lemma isolate_byte_0
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] &&& 0xFF) : BitVec 8) = a
    := by
      simp [toNat]; bv_decide

    @[simp]
    lemma isolate_byte_1
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 8 &&& 0xFF) : BitVec 8) = b
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (b.toNat + c.toNat * 256 + d.toNat * 65536 + e.toNat * 16777216
              + f.toNat * 4294967296 + g.toNat * 1099511627776
              + h.toNat * 281474976710656 + i.toNat * 72057594037927936
              + j.toNat * 18446744073709551616
              + k.toNat * 4722366482869645213696
              + l.toNat * 1208925819614629174706176
              + m.toNat * 309485009821345068724781056
              + n.toNat * 79228162514264337593543950336
              + o.toNat * 20282409603651670423947251286016
              + p.toNat * 5192296858534827628530496329220096) % 256 &&& 255
      . congr; omega
      . trans b.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_2
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 16 &&& 0xFF) : BitVec 8) = c
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (c.toNat + d.toNat * 256 + e.toNat * 65536 + f.toNat * 16777216
              + g.toNat * 4294967296 + h.toNat * 1099511627776
              + i.toNat * 281474976710656 + j.toNat * 72057594037927936
              + k.toNat * 18446744073709551616
              + l.toNat * 4722366482869645213696
              + m.toNat * 1208925819614629174706176
              + n.toNat * 309485009821345068724781056
              + o.toNat * 79228162514264337593543950336
              + p.toNat * 20282409603651670423947251286016) % 256 &&& 255
      . congr; omega
      . trans c.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_3
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 24 &&& 0xFF) : BitVec 8) = d
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (d.toNat + e.toNat * 256 + f.toNat * 65536 + g.toNat * 16777216
              + h.toNat * 4294967296 + i.toNat * 1099511627776
              + j.toNat * 281474976710656 + k.toNat * 72057594037927936
              + l.toNat * 18446744073709551616
              + m.toNat * 4722366482869645213696
              + n.toNat * 1208925819614629174706176
              + o.toNat * 309485009821345068724781056
              + p.toNat * 79228162514264337593543950336) % 256 &&& 255
      . congr; omega
      . trans d.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_4
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 32 &&& 0xFF) : BitVec 8) = e
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (e.toNat + f.toNat * 256 + g.toNat * 65536 + h.toNat * 16777216
              + i.toNat * 4294967296 + j.toNat * 1099511627776
              + k.toNat * 281474976710656 + l.toNat * 72057594037927936
              + m.toNat * 18446744073709551616
              + n.toNat * 4722366482869645213696
              + o.toNat * 1208925819614629174706176
              + p.toNat * 309485009821345068724781056) % 256 &&& 255
      . congr; omega
      . trans e.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_5
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 40 &&& 0xFF) : BitVec 8) = f
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (f.toNat + g.toNat * 256 + h.toNat * 65536 + i.toNat * 16777216
              + j.toNat * 4294967296 + k.toNat * 1099511627776
              + l.toNat * 281474976710656 + m.toNat * 72057594037927936
              + n.toNat * 18446744073709551616
              + o.toNat * 4722366482869645213696
              + p.toNat * 1208925819614629174706176) % 256 &&& 255
      . congr; omega
      . trans f.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_6
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 48 &&& 0xFF) : BitVec 8) = g
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (g.toNat + h.toNat * 256 + i.toNat * 65536 + j.toNat * 16777216
              + k.toNat * 4294967296 + l.toNat * 1099511627776
              + m.toNat * 281474976710656 + n.toNat * 72057594037927936
              + o.toNat * 18446744073709551616
              + p.toNat * 4722366482869645213696) % 256 &&& 255
      . congr; omega
      . trans g.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_7
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 56 &&& 0xFF) : BitVec 8) = h
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (h.toNat + i.toNat * 256 + j.toNat * 65536 + k.toNat * 16777216
              + l.toNat * 4294967296 + m.toNat * 1099511627776
              + n.toNat * 281474976710656 + o.toNat * 72057594037927936
              + p.toNat * 18446744073709551616) % 256 &&& 255
      . congr; omega
      . trans h.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_8
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 64 &&& 0xFF) : BitVec 8) = i
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (i.toNat + j.toNat * 256 + k.toNat * 65536 + l.toNat * 16777216
              + m.toNat * 4294967296 + n.toNat * 1099511627776
              + o.toNat * 281474976710656 + p.toNat * 72057594037927936) % 256 &&& 255
      . congr; omega
      . trans i.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_9
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 72 &&& 0xFF) : BitVec 8) = j
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (j.toNat + k.toNat * 256 + l.toNat * 65536 + m.toNat * 16777216
              + n.toNat * 4294967296 + o.toNat * 1099511627776
              + p.toNat * 281474976710656) % 256 &&& 255
      . congr; omega
      . trans j.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_10
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 80 &&& 0xFF) : BitVec 8) = k
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (k.toNat + l.toNat * 256 + m.toNat * 65536 + n.toNat * 16777216
              + o.toNat * 4294967296 + p.toNat * 1099511627776) % 256 &&& 255
      . congr; omega
      . trans k.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_11
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 88 &&& 0xFF) : BitVec 8) = l
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (l.toNat + m.toNat * 256 + n.toNat * 65536 + o.toNat * 16777216
              + p.toNat * 4294967296) % 256 &&& 255
      . congr; omega
      . trans l.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_12
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 96 &&& 0xFF) : BitVec 8) = m
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (m.toNat + n.toNat * 256 + o.toNat * 65536 + p.toNat * 16777216) % 256 &&& 255
      . congr; omega
      . trans m.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_13
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 104 &&& 0xFF) : BitVec 8) = n
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (n.toNat + o.toNat * 256 + p.toNat * 65536) % 256 &&& 255
      . congr; omega
      . trans n.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_14
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 112 &&& 0xFF) : BitVec 8) = o
    := by
      simp [toNat, ← BitVec.toNat_inj]
      simp [Nat.shiftRight_eq_div_pow]
      trans (o.toNat + p.toNat * 256) % 256 &&& 255
      . congr; omega
      . trans o.toNat &&& (255 : BitVec 8).toNat
        . congr; omega
        . rw [← BitVec.toNat_and, BitVec.toNat_inj]
          bv_decide

    @[simp]
    lemma isolate_byte_15
    :
      ((U128b.toNat #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] >>> 120) : BitVec 8) = p
    := by
      simp [toNat, ← BitVec.toNat_inj]
      omega

  end isolation

end U128b

namespace U64b

  section extend

    /-- Sign-extender byte for `U64b`. Returns `255` if `with_sign` is on
        and the value is negative; `0` otherwise. -/
    @[grind]
    def ext (w : U64b) (with_sign : Bool) :=
      if with_sign && w.negative then 255 else 0

    lemma zero_le_ext w with_sign : 0 ≤ ext w with_sign := by grind
    lemma ext_le_255 w with_sign : ext w with_sign ≤ 255 := by grind

    /-- Extension of an 8-byte word to a 16-byte word. With `with_sign`
        true, the upper 8 bytes are filled with `255` when the value is
        negative (and `0` otherwise); with `with_sign` false, the upper
        bytes are all `0`. This corresponds to MulGadget's effective
        operand after the `b_sign_extend` / `c_sign_extend` filling. -/
    def extend (w : U64b) (with_sign : Bool) : U128b :=
      let e := ext w with_sign
      #v[ w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7],
          e, e, e, e, e, e, e, e ]

    /-- The extension yields the same numeric value as the BitVec
        extension primitive. -/
    lemma extend_BitVec_extend {w : U64b} {with_sign : Bool}
    :
      (w.extend with_sign).toBV = BitVec.extend w.toBV 128 with_sign
    := by
      rcases with_sign <;>
        simp [extend, BitVec.extend, ext, ← BitVec.toNat_inj]
      . simp [U128b.toNat, U64b.toNat]
        omega
      . rw [BitVec.toNat_signExtend]
        simp [U64b.toBV_msb_negative]
        by_cases w.negative
        all_goals
          simp_all
          simp only [toNat, U128b.toNat, Vector.getElem_mk,
                     List.getElem_toArray, List.getElem_cons_zero,
                     List.getElem_cons_succ,
                     BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          omega

    /-- Zero-extension preserves the natural number. -/
    @[simp]
    lemma extend_toNat {w : U64b} : (w.extend false).toNat = w.toNat := by
      simp [extend, ext, U64b.toNat, U128b.toNat]

    /-- Sign-extension preserves the (signed) integer. -/
    @[simp]
    lemma extend_toInt {w : U64b}
    :
      (w.extend true).toInt = w.toInt
    := by
      simp [extend, ext, U128b.toInt, toInt, U128b.negative, negative,
            U128b.toNat, toNat]
      split_ifs <;> simp_all <;> omega

    /-- `toU64b` preserves `extend` -/
    @[simp]
    lemma toU64b_extend {w : U64w} : (extend (U64w.toU64b w) sgn).toBV = (U64w.extend w sgn).toBV := by
      cases sgn
      . simp [← BitVec.toNat_inj]
      . simp [← BitVec.toInt_inj]

  end extend

end U64b
