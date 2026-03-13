import PicoFV.Constraints.BitwiseAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace BitwiseAir.Spec

  open RV32IM_Interactions
  open BitwiseAir.ConstraintsAndBuses
  open BitwiseAir.Interactions

  set_option maxHeartbeats 1_000_000_000

  private lemma FKB.ofNat_xor_eq (a b : FKB) (ha : a.val < 256) (hb : b.val < 256) :
      BitVec.ofNat 8 (a ^^^ b).val = BitVec.ofNat 8 a.val ^^^ BitVec.ofNat 8 b.val := by
    simp only [Fin.xor_val]
    have : a.val ^^^ b.val < 2130706433 := by
      have h1 : a.val < 2 ^ 8 := by omega
      have h2 : b.val < 2 ^ 8 := by omega
      have := Nat.xor_lt_two_pow h1 h2; omega
    simp only [Nat.mod_eq_of_lt this, BitVec.ofNat_xor]

  private lemma FKB.ofNat_or_eq (a b : FKB) (ha : a.val < 256) (hb : b.val < 256) :
      BitVec.ofNat 8 (a ||| b).val = BitVec.ofNat 8 a.val ||| BitVec.ofNat 8 b.val := by
    simp only [Fin.or_val]
    have : a.val ||| b.val < 2130706433 := by
      have h1 : a.val < 2 ^ 8 := by omega
      have h2 : b.val < 2 ^ 8 := by omega
      have := Nat.or_lt_two_pow h1 h2; omega
    simp only [Nat.mod_eq_of_lt this, BitVec.ofNat_or]

  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_BitwiseAir FKB ExtF)
    (row : ℕ)
    (h_constraints : BitwiseAir.Extraction.allHold air row)
  :
    (air.cols.is_xor row 0 = 0 ∨ air.cols.is_xor row 0 = 1) ∧
    (air.cols.is_or row 0 = 0 ∨ air.cols.is_or row 0 = 1) ∧
    (air.cols.is_and row 0 = 0 ∨ air.cols.is_and row 0 = 1) ∧
    ((air.cols.is_xor row 0 + air.cols.is_or row 0) + air.cols.is_and row 0 = 0 ∨
     (air.cols.is_xor row 0 + air.cols.is_or row 0) + air.cols.is_and row 0 = 1)
  := by
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_constraints
    grind

  lemma spec_XOR
    [Field ExtF]
    (air : Valid_BitwiseAir FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseAir.Extraction.allHold air row)
    (h_xor : air.cols.is_xor row 0 = 1)
  :
    ALUBus.Spec 2
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Establish other selectors = 0
    have selectors := selector_breakdown air row h_constraints
    have h_or : air.cols.is_or row 0 = 0 := by grind
    have h_and : air.cols.is_and row 0 = 0 := by grind
    -- Simplify ALUBus.Spec
    simp only [ALUBus.Spec, and_assoc]
    -- Simplify byte bus assumptions
    simp [bus_row_wf_asm, bus_row, h_xor, h_or, h_and, ByteBus.Spec] at h_wf
    -- Extract byte-level XOR facts and bounds
    obtain ⟨⟨h_eq0, h_a0, h_b0, h_c0⟩, ⟨h_eq1, h_a1, h_b1, h_c1⟩,
            ⟨h_eq2, h_a2, h_b2, h_c2⟩, h_eq3, h_a3, h_b3, h_c3⟩ := h_wf
    -- Provide byte bounds
    refine ⟨h_a0, h_a1, h_a2, h_a3, ?_⟩
    -- Prove U32.toBV a = U32.toBV b ^^^ U32.toBV c from byte-level XOR facts
    simp [U32.toBV, *]
    rw [FKB.ofNat_xor_eq _ _ h_b3 h_c3, FKB.ofNat_xor_eq _ _ h_b2 h_c2,
        FKB.ofNat_xor_eq _ _ h_b1 h_c1, FKB.ofNat_xor_eq _ _ h_b0 h_c0,
        BitVec.xor_append, BitVec.xor_append, BitVec.xor_append]

  lemma spec_OR
    [Field ExtF]
    (air : Valid_BitwiseAir FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseAir.Extraction.allHold air row)
    (h_or : air.cols.is_or row 0 = 1)
  :
    ALUBus.Spec 3
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Establish other selectors = 0
    have selectors := selector_breakdown air row h_constraints
    have h_xor : air.cols.is_xor row 0 = 0 := by grind
    have h_and : air.cols.is_and row 0 = 0 := by grind
    -- Simplify ALUBus.Spec
    simp only [ALUBus.Spec, and_assoc]
    -- Simplify byte bus assumptions
    simp [bus_row_wf_asm, bus_row, h_xor, h_or, h_and, ByteBus.Spec] at h_wf
    -- Extract byte-level OR facts and bounds
    obtain ⟨⟨h_eq0, h_a0, h_b0, h_c0⟩, ⟨h_eq1, h_a1, h_b1, h_c1⟩,
            ⟨h_eq2, h_a2, h_b2, h_c2⟩, h_eq3, h_a3, h_b3, h_c3⟩ := h_wf
    -- Provide byte bounds
    refine ⟨h_a0, h_a1, h_a2, h_a3, ?_⟩
    -- Prove U32.toBV a = U32.toBV b ||| U32.toBV c from byte-level OR facts
    simp [U32.toBV, *]
    rw [FKB.ofNat_or_eq _ _ h_b3 h_c3, FKB.ofNat_or_eq _ _ h_b2 h_c2,
        FKB.ofNat_or_eq _ _ h_b1 h_c1, FKB.ofNat_or_eq _ _ h_b0 h_c0,
        BitVec.or_append, BitVec.or_append, BitVec.or_append]

  lemma spec_AND
    [Field ExtF]
    (air : Valid_BitwiseAir FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseAir.Extraction.allHold air row)
    (h_and : air.cols.is_and row 0 = 1)
  :
    ALUBus.Spec 4
      (air.cols.a_0 row 0) (air.cols.a_1 row 0) (air.cols.a_2 row 0) (air.cols.a_3 row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0) (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0) (air.cols.c_2 row 0) (air.cols.c_3 row 0)
  := by
    -- Establish other selectors = 0
    have selectors := selector_breakdown air row h_constraints
    have h_xor : air.cols.is_xor row 0 = 0 := by grind
    have h_or : air.cols.is_or row 0 = 0 := by grind
    -- Simplify ALUBus.Spec
    simp only [ALUBus.Spec, and_assoc]
    -- Simplify byte bus assumptions
    simp [bus_row_wf_asm, bus_row, h_xor, h_or, h_and, ByteBus.Spec] at h_wf
    -- Extract byte-level AND facts and bounds
    obtain ⟨⟨h_eq0, h_a0, h_b0, h_c0⟩, ⟨h_eq1, h_a1, h_b1, h_c1⟩,
            ⟨h_eq2, h_a2, h_b2, h_c2⟩, h_eq3, h_a3, h_b3, h_c3⟩ := h_wf
    -- Provide byte bounds
    refine ⟨h_a0, h_a1, h_a2, h_a3, ?_⟩
    -- Prove U32.toBV a = U32.toBV b &&& U32.toBV c from byte-level AND facts
    simp [U32.toBV, *]
    rw [BitVec.and_append, BitVec.and_append, BitVec.and_append]

  lemma wf_asrt
      [Field ExtF]
      (air : Valid_BitwiseAir FKB ExtF)
      (row : ℕ)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : BitwiseAir.Extraction.allHold air row)
    :
      bus_row_wf_asrt (bus_row air row)
    := by
      -- Set up assumptions
      have h_wf' := h_wf
      simp [bus_row_wf_asm] at h_wf'
      obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state ⟩ := h_wf'
      -- Main proof
      simp [bus_row_wf_asrt]
      constructor
      -- Program
      . simp [bus_row]
      . constructor
        . -- ALU
          simp [bus_row]
          intro h_mult
          have selectors := selector_breakdown air row h_constraints
          obtain ⟨h1, h2, h3, _⟩ := selectors
          -- Case split on which selector is active
          rcases h1 with h_xor | h_xor
          · -- is_xor = 0
            rcases h2 with h_or | h_or
            · -- is_or = 0, so is_and = 1
              have h_and : air.cols.is_and row 0 = 1 := by grind
              simp only [h_xor, h_or, h_and, one_mul, zero_mul, add_zero, zero_add]
              exact spec_AND air row h_wf h_constraints h_and
            · -- is_or = 1
              have h_and : air.cols.is_and row 0 = 0 := by grind
              simp only [h_xor, h_or, h_and, one_mul, zero_mul, add_zero, zero_add]
              exact spec_OR air row h_wf h_constraints h_or
          · -- is_xor = 1
            have h_or : air.cols.is_or row 0 = 0 := by grind
            have h_and : air.cols.is_and row 0 = 0 := by grind
            simp only [h_xor, h_or, h_and, one_mul, zero_mul, add_zero]
            exact spec_XOR air row h_wf h_constraints h_xor
        . constructor
          . -- Byte
            simp [bus_row, ByteBus.Spec]
            have selectors := selector_breakdown air row h_constraints
            split_ands <;> intro h <;> exfalso <;> grind
          . -- Register
            simp [bus_row]

end BitwiseAir.Spec
