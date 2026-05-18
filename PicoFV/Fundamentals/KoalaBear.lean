import PicoFV.Fundamentals.Core
import PicoFV.Fundamentals.Word

set_option maxHeartbeats 1_000_000_000

notation "KB_prime" => 2130706433
@[simp] lemma KB_eq : KB_prime = 2130706433 := rfl

namespace KoalaBear

  notation "FKB" => Fin KB_prime
  @[simp] lemma F_eq : FKB = Fin KB_prime := rfl

  lemma prime_KoalaBearPrime : Nat.Prime KB_prime := by native_decide

  instance Fact_KBPrime : Fact (Nat.Prime KB_prime) := ⟨prime_KoalaBearPrime⟩
  instance : NeZero KB_prime := by constructor; decide

  instance : NatCast FKB where
    natCast := (Lean.Grind.Fin.instCommRingFinOfNeZeroNat KB_prime).toCommSemiring.toSemiring.natCast.natCast

  instance : Field FKB := ZMod.instField KB_prime
  instance : NoZeroDivisors FKB := Fin.noZeroDivisors_of_prime _ (hp := Fact_KBPrime)

  section coercions

    instance : Coe (BitVec 8) FKB where
      coe b := ⟨ b.toNat, by omega ⟩

    instance : Coe FKB (BitVec 8) where
      coe bb := BitVec.ofNat 8 bb.val

    instance : Coe (BitVec 16) FKB where
      coe b := ⟨ b.toNat, by omega ⟩

    instance : Coe FKB (BitVec 16) where
      coe bb := BitVec.ofNat 16 bb.val

  end coercions

  section U32b

    @[simp, grind]
    def isU32 (v : Vector FKB 4) :=
      v[0].val < 256 ∧ v[1].val < 256 ∧ v[2].val < 256 ∧ v[3].val < 256

    @[simp, grind]
    def toU32 (v : Vector FKB 4) : U32b :=
      #v[ { toFin := ⟨ v[0].val % 256, (by grind)⟩ },
          { toFin := ⟨ v[1].val % 256, (by grind)⟩ },
          { toFin := ⟨ v[2].val % 256, (by grind)⟩ },
          { toFin := ⟨ v[3].val % 256, (by grind)⟩ } ]

    @[simp, grind]
    def toBV32 (v : Vector FKB 4) : BitVec 32 :=
      (toU32 v).toBV

  end U32b

  section toInt

    def toInt (a : FKB) : ℤ :=
      if a.val ≤ KB_prime / 2 then a.val else a.val - KB_prime

    @[simp]
    lemma toInt_inv
      (a : FKB)
    :
      ((toInt a) : FKB) = a
    := by
      simp [toInt]

  end toInt

  section Auxiliaries

    lemma inv_256_eq_one_lr : (2122383361 : FKB) * 256 = 1 := by rfl

    lemma inv256_prod_lt_256
      (x : Fin 256)
    :
      x = 0 ∨ (¬x = 0 ∧ 8323072 < (⟨ x.val, by omega⟩ : FKB) * 2122383361 ∧ (⟨ x.val, by omega⟩ : FKB) * 2122383361 ≤ 2122383361)
    := by
      simp [Fin.lt_def, Fin.val_mul]
      fin_cases x <;> decide

    lemma inv256_prod_mod
      (x : FKB)
    :
      x % 256 = 0 ∨ (¬ x % 256 = 0 ∧ 8323072 < (x % 256) * 2122383361 ∧ (x % 256) * 2122383361 ≤ 2122383361)
    := by
      have := inv256_prod_lt_256 ⟨ (x % 256).val, by grind⟩
      rcases this with hz | ⟨ h_nz, h_lt ⟩ <;> simp_all
      . grind
      . right; constructor
        . grind
        . simp_all [Fin.lt_def, Fin.mul_def]

    lemma inv256_prod_lt_256_mod_zero
      {x : FKB}
      (h_le : x * 2122383361 ≤ 8323072)
    :
      x % 256 = 0
    := by
      by_cases hnz : x = 0 <;> [ simp_all; skip ]
      have h_div_mod : x = (x / 256) * 256 + x % 256
      := by
        simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
        grind
      rw [h_div_mod] at h_le ⊢; clear h_div_mod
      simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
      rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)]
      simp [Nat.add_mod]
      have := inv256_prod_mod x
      rcases this with hz | ⟨ hnz, hmod ⟩
      . simp [Fin.ext_iff] at hz; assumption
      . rw [mul_comm (b := 2122383361), mul_add, mul_comm (b := 256), ← mul_assoc, inv_256_eq_one_lr] at h_le
        simp at h_le
        have ub_x_div : x / 256 ≤ 8323072 := by simp [Fin.le_def]; omega
        suffices : 8323072 < x / 256 + 2122383361 * (x % 256)
        . omega
        . obtain ⟨ lb_mod, ub_mod ⟩ := hmod
          rw [Fin.lt_def] at lb_mod ⊢
          rw [Fin.le_def] at ub_mod h_le ub_x_div
          simp_all [Fin.val_add, Fin.val_mul]
          rw [Nat.add_mod] at h_le ⊢
          rw [Nat.mod_eq_of_lt (a := _ / _) (by omega)] at h_le ⊢
          by_cases h_eq : x.val / 256 = 8323072
          . have : x = 2122383361 := by omega
            simp_all
          . have h_lt : x.val / 256 < 8323072 := by omega
            clear ub_x_div h_eq
            rw [Nat.mod_eq_of_lt (by grind)]
            grind

    lemma inv256_prod_diff_div_mod
      {a b : FKB}
      (ub_a : a.val < 256)
      (h_le : ((b - a) * 2122383361).val < 256)
    : b < 65536 ∧
      a = b % 256 ∧
      (b - a) * 2122383361 = b / 256
    := by
      have h_mod_zero := @inv256_prod_lt_256_mod_zero (b - a) (by omega)
      have h_a_le_b : a ≤ b := by grind
      suffices h_mod : a = b % 256 <;> [ skip; grind ]
      . simp_all
        have : b = (b / 256 * 256) + b % 256
          := by simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]; clear h_le; grind
        have h_split : a = b % 256 ∧ (b - a) * 2122383361 = b / 256 := by omega
        subst a
        split_ands <;> [ skip; tauto ]
        simp [h_split.2] at h_le
        omega

  end Auxiliaries

end KoalaBear
