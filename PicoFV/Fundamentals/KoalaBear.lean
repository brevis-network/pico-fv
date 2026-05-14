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

end KoalaBear
