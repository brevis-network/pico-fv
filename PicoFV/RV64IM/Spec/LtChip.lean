import PicoFV.RV64IM.Spec.LtSignedGadget
import PicoFV.RV64IM.Constraints.LtChip

open Plonky3
open LeanRV64D.Functions

set_option maxHeartbeats 1_000_000_000

/-!
# LtChip — semantic specification

The `LtChip.Spec` namespace below states the chip's two ALU outputs
and demonstrates re-use of `LtSignedGadget`'s spec:

- `ext_asrt` — externality assertions on the chip's bus row.
  Vacuous: byte entries have trivial `True` externals; the ALU entry
  is served with multiplicity `-(is_slt + is_slt_u)`, so
  `ext_assert_cond` (= multiplicity = 1) never fires.
- `spec_SLT`  — opcode 8 (signed compare). Uses
  `LtSignedGadget.Spec.gadget_spec` at `is_signed = 1` and bridges
  the resulting `bit ↔ b.toInt < c.toInt` to
  `a = zero_extend (bool_to_bit ...)` via the chip's `a_0 = bit`
  identity + `a_{1,2,3} = 0` zeroing (`a_1 = 0` through `is_cmp = 0`,
  which these two now take as a hypothesis: a row with `is_cmp = 1`
  serves 264 / 265 instead).
- `spec_SLTU` — opcode 9 (unsigned compare). Identical to `spec_SLT`
  except `is_signed = 0` (`bit ↔ b.toNat < c.toNat`).
- `spec_CMP_SLT` / `spec_CMP_SLTU` — opcodes 264 / 265, the merged
  branch-comparison rows (`is_cmp = 1`, so the served opcode carries
  `LT_CMP_OPCODE_TAG`). These carry two strict bits rather than one
  word: `a_0 = [b < c]` is the gadget's `bit` as before, and
  `a_1 = Σ u16_flags − bit` is `[c < b]` because the flag sum is the
  inequality indicator (`LtSignedGadget.Spec.flags_sum_spec`).
- `wf_asrt` — dispatches the single ALU entry to one of the four
  specifications, on the active selector and `is_cmp`; byte entries are
  vacuous (`is_real ∈ {0, 1}`, never `-1`).

Re-use pattern (identical to `SubChip.Spec`):

1. `LtChip.Interpretations.allHold_abs` ⇒ `LtSignedGadget.AbsConstraints`.
2. The chip's bus-row hypotheses about the gadget's contribution are
   stated directly via `LtSignedGadget.AbsBuses` (using `bus_row_abs`
   to bridge to the chip's typed `bus_row`).
3. `LtSignedGadget.Spec.gadget_spec` (parametric) ⇒ a bit equal to
   the (signed / unsigned) comparison.

The chip takes operand range hypotheses externally — opcodes 8/9 are
not in `ALUBus.operandsInternal`, so the ALU entry's `ext_assume`
supplies `operand_range` on `b`/`c`.
-/

namespace LtChip.Spec

  open RV64IM_Interactions
  open LtChip.ConstraintsAndBuses
  open LtChip.Interactions
  open LtChip.Interpretations

  set_option maxHeartbeats 1_000_000_000

  --
  -- Auxiliary: derive the chip-level result equation `a = zero_extend bit`.
  --

  /-- Convert the chip's `a_0 = bit`, `a_1 = a_2 = a_3 = 0`, and a
      `bit = 1 ↔ P` iff into the BitVec-level result
      `U64w.toBV [a_0, a_1, a_2, a_3] = BitVec.setWidth 64 (if P then 1#1 else 0#1)`,
      which is the form the executor's `.SLT`/`.SLTU` branches reduce to
      after the simp set unfolds `zero_extend` and `bool_to_bit`. -/
  private lemma a_eq_setWidth_ite
    (a_0 a_1 a_2 a_3 bit : FKB) (P : Prop) [Decidable P]
    (h_a1 : a_1 = 0) (h_a2 : a_2 = 0) (h_a3 : a_3 = 0)
    (h_a0_bit : a_0 = bit)
    (h_bit : bit = 0 ∨ bit = 1)
    (h_p : bit = 1 ↔ P)
  :
    U64w.toBV #v[a_0, a_1, a_2, a_3]
      = BitVec.setWidth 64 (if P then (1#1 : BitVec 1) else 0#1)
  := by
    subst h_a1 h_a2 h_a3
    rcases h_bit with hb | hb
    . -- bit = 0 ⇒ ¬P
      have hnP : ¬ P := by
        intro hp; have := h_p.mpr hp; rw [hb] at this; exact absurd this (by decide)
      rw [if_neg hnP, h_a0_bit, hb]
      simp [U64w.toBV]
    . -- bit = 1 ⇒ P
      have hP : P := h_p.mp hb
      rw [if_pos hP, h_a0_bit, hb]
      simp [U64w.toBV]

  --
  -- Shared row facts
  --

  -- =====================================================================
  -- Everything the four result specifications below need from one real
  -- row: the gadget's comparison bit and its flag sum with what each
  -- means, and the chip's own equations for the four result limbs
  -- (`alu/lt/constraints.rs:54-82`).
  --
  -- The flag sum is what the merged rows turn on. The chip pins
  -- `a_1 = is_cmp · (Σ u16_flags − bit)`, and `Σ u16_flags = [b ≠ c]`
  -- (`LtSignedGadget.Spec.flags_sum_spec`) makes that difference the
  -- strict `[c < b]`.
  --
  -- The operand u16 bounds come from the ALU entry's externals: none of
  -- the four opcodes this chip can serve — 8, 9, 264, 265 — is in
  -- `ALUBus.operandsInternal`.
  -- =====================================================================

  private lemma row_facts
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_real : air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1)
  :
    (air.cols.values.lt_signed.result.bit row 0 = 0 ∨ air.cols.values.lt_signed.result.bit row 0 = 1) ∧
    (air.cols.values.lt_signed.result.u16_flags_0 row 0
      + air.cols.values.lt_signed.result.u16_flags_1 row 0
      + air.cols.values.lt_signed.result.u16_flags_2 row 0
      + air.cols.values.lt_signed.result.u16_flags_3 row 0 = 0 ∨
     air.cols.values.lt_signed.result.u16_flags_0 row 0
      + air.cols.values.lt_signed.result.u16_flags_1 row 0
      + air.cols.values.lt_signed.result.u16_flags_2 row 0
      + air.cols.values.lt_signed.result.u16_flags_3 row 0 = 1) ∧
    ((air.cols.values.lt_signed.result.u16_flags_0 row 0
      + air.cols.values.lt_signed.result.u16_flags_1 row 0
      + air.cols.values.lt_signed.result.u16_flags_2 row 0
      + air.cols.values.lt_signed.result.u16_flags_3 row 0 = 0) ↔
      (U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                  air.cols.values.b_2 row 0, air.cols.values.b_3 row 0]).toNat
        = (U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                  air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]).toNat) ∧
    (air.cols.values.is_slt row 0 = 1 →
      (air.cols.values.lt_signed.result.bit row 0 = 1 ↔
        (U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                  air.cols.values.b_2 row 0, air.cols.values.b_3 row 0]).toInt
          < (U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                  air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]).toInt)) ∧
    (air.cols.values.is_slt row 0 = 0 →
      (air.cols.values.lt_signed.result.bit row 0 = 1 ↔
        (U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                  air.cols.values.b_2 row 0, air.cols.values.b_3 row 0]).toNat
          < (U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                  air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]).toNat)) ∧
    air.cols.values.a_0 row 0 = air.cols.values.lt_signed.result.bit row 0 ∧
    air.cols.values.a_1 row 0 =
      air.cols.values.is_cmp row 0 *
        ((air.cols.values.lt_signed.result.u16_flags_0 row 0
      + air.cols.values.lt_signed.result.u16_flags_1 row 0
      + air.cols.values.lt_signed.result.u16_flags_2 row 0
      + air.cols.values.lt_signed.result.u16_flags_3 row 0) - air.cols.values.lt_signed.result.bit row 0) ∧
    air.cols.values.a_2 row 0 = 0 ∧
    air.cols.values.a_3 row 0 = 0
  := by
    have h_abs := allHold_abs air row h_constraints
    obtain ⟨h_gadget_constraints, h_c29, h_c30, h_c31, h_c32, h_c3, _h_c4⟩ := h_abs
    obtain ⟨h_slt_b, h_slt_u_b, _⟩ := selector_breakdown air row h_constraints
    have h_cmp_b : air.cols.values.is_cmp row 0 = 0 ∨ air.cols.values.is_cmp row 0 = 1 := by
      simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c3; exact h_c3
    have h_sel :
      (air.cols.values.is_slt row 0 = 1 ∧ air.cols.values.is_slt_u row 0 = 0) ∨
      (air.cols.values.is_slt row 0 = 0 ∧ air.cols.values.is_slt_u row 0 = 1) := by
      clear *- h_slt_b h_slt_u_b h_is_real; grind
    -- Split the bus row into the gadget's contribution and the chip's
    -- single ALU entry.
    rw [bus_row_abs, LtChip.AbsBuses, bus_row_ext_asm_append] at h_ext_asm
    rw [bus_row_abs, LtChip.AbsBuses, bus_row_wf_asm_append] at h_wf_asm
    obtain ⟨h_gadget_ext_asm, h_chip_ext_asm⟩ := h_ext_asm
    obtain ⟨h_gadget_wf_asm, _h_chip_wf_asm⟩ := h_wf_asm
    -- Operand ranges, in each of the four (selector, is_cmp) shapes.
    have h_range :
      ALUBus.operandRange
        (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
        (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
        (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
        (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0) := by
      rcases h_sel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h_cmp_b with h3 | h3 <;>
        simp [bus_row_ext_asm, ALUBus.externals, ALUBus.operandsInternal,
              ALUBus.validOpcode, ALUBus.operandRange, h1, h2, h3]
          at h_chip_ext_asm ⊢ <;>
        exact h_chip_ext_asm
    simp only [ALUBus.operandRange] at h_range
    obtain ⟨h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3r⟩ := h_range
    -- The gadget's two specifications.
    have h_gadget_spec := LtSignedGadget.Spec.gadget_spec
      (air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0)
      (air.cols.values.is_slt row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.lt_signed.result.u16_flags_0 row 0)
      (air.cols.values.lt_signed.result.u16_flags_1 row 0)
      (air.cols.values.lt_signed.result.u16_flags_2 row 0)
      (air.cols.values.lt_signed.result.u16_flags_3 row 0)
      (air.cols.values.lt_signed.result.not_eq_inv row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)
      (air.cols.values.lt_signed.result.bit row 0)
      (air.cols.values.lt_signed.b_msb.msb row 0)
      (air.cols.values.lt_signed.c_msb.msb row 0)
      h_gadget_ext_asm h_gadget_wf_asm h_gadget_constraints
      h_is_real
      ⟨h_b0, h_b1, h_b2, h_b3⟩
      ⟨h_c0, h_c1, h_c2, h_c3r⟩
    have h_flags_spec := LtSignedGadget.Spec.flags_sum_spec
      (air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0)
      (air.cols.values.is_slt row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.lt_signed.result.u16_flags_0 row 0)
      (air.cols.values.lt_signed.result.u16_flags_1 row 0)
      (air.cols.values.lt_signed.result.u16_flags_2 row 0)
      (air.cols.values.lt_signed.result.u16_flags_3 row 0)
      (air.cols.values.lt_signed.result.not_eq_inv row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_0 row 0)
      (air.cols.values.lt_signed.result.comparison_limbs_1 row 0)
      (air.cols.values.lt_signed.result.bit row 0)
      (air.cols.values.lt_signed.b_msb.msb row 0)
      (air.cols.values.lt_signed.c_msb.msb row 0)
      h_gadget_wf_asm h_gadget_constraints
      h_is_real h_slt_b
      ⟨h_b0, h_b1, h_b2, h_b3⟩
      ⟨h_c0, h_c1, h_c2, h_c3r⟩
    obtain ⟨h_bit_bool, h_unsigned_iff, h_signed_iff⟩ := h_gadget_spec
    obtain ⟨h_sum_bool, h_sum_iff⟩ := h_flags_spec
    -- The chip's own result-limb equations.
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c29 h_c30 h_c31 h_c32
    refine ⟨h_bit_bool, h_sum_bool, h_sum_iff, h_signed_iff, h_unsigned_iff, ?_, ?_, h_c30, h_c31⟩
    . clear *- h_c32 h_is_real; grind
    . clear *- h_c29; grind

  --
  -- Auxiliaries shared by the four result specifications
  --

  /-- A boolean field element that is `1` exactly when `P` holds is the
      indicator of `P`. -/
  private lemma bool_eq_ite
    (x : FKB) (P : Prop) [Decidable P]
    (h_bool : x = 0 ∨ x = 1) (h_iff : x = 1 ↔ P)
  :
    x = (if P then 1 else 0)
  := by
    rcases h_bool with h | h
    . rw [h, if_neg]
      intro hp
      have := h_iff.mpr hp
      rw [h] at this
      exact absurd this (by decide)
    . rw [h, if_pos (h_iff.mp h)]

  /-- The merged rows' `a_1 = Σ u16_flags − bit` is the strict reverse
      comparison. Stated over any linear order so that the signed rows
      can use it at `BitVec.toInt` and the unsigned ones at
      `BitVec.toNat`: the flag sum is the inequality indicator, `bit` is
      `[x < y]`, and trichotomy turns the difference into `[y < x]`. -/
  private lemma gt_eq_sum_sub_lt
    {α : Type} [LinearOrder α] {x y : α} {s bit a1 : FKB}
    (h_sum_bool : s = 0 ∨ s = 1) (h_bit_bool : bit = 0 ∨ bit = 1)
    (h_sum_iff : s = 0 ↔ x = y) (h_lt_iff : bit = 1 ↔ x < y)
    (h_a1 : a1 = s - bit)
  :
    (a1 = 0 ∨ a1 = 1) ∧ (a1 = 1 ↔ y < x)
  := by
    rcases h_sum_bool with hs | hs
    . -- Equal operands: neither strict comparison holds.
      have hxy : x = y := h_sum_iff.mp hs
      have hbit : bit = 0 := by
        rcases h_bit_bool with h | h
        . exact h
        . exact absurd (h_lt_iff.mp h) (by rw [hxy]; exact lt_irrefl y)
      subst hxy
      rw [h_a1, hs, hbit]
      constructor
      . left; ring
      . constructor
        . intro h; exfalso; revert h; simp
        . intro h; exact absurd h (lt_irrefl x)
    . rcases h_bit_bool with hb | hb
      . -- Not below, and not equal, so above.
        have hne : x ≠ y := by
          intro h
          have h0 : s = 0 := h_sum_iff.mpr h
          rw [h0] at hs
          exact absurd hs (by decide)
        have hnlt : ¬ (x < y) := by
          intro h
          have h1 : bit = 1 := h_lt_iff.mpr h
          rw [h1] at hb
          exact absurd hb (by decide)
        have hgt : y < x := lt_of_le_of_ne (not_lt.mp hnlt) (Ne.symm hne)
        rw [h_a1, hs, hb]
        refine ⟨by right; ring, ?_⟩
        simp [hgt]
      . -- Below, so not above.
        have hlt := h_lt_iff.mp hb
        rw [h_a1, hs, hb]
        refine ⟨by left; ring, ?_⟩
        constructor
        . intro h; exfalso; revert h; simp
        . intro h; exact absurd h (asymm hlt)

  --
  -- spec_SLT — opcode 8 (signed compare, unmerged row)
  --

  -- =====================================================================
  -- spec_SLT: the chip's signed less-than correctness on a row that is
  -- not a merged branch comparison (`is_cmp = 0`, so the served opcode
  -- is 8 and not 264). `row_facts` supplies the gadget's bit at
  -- `is_signed = 1`; `a_1 = is_cmp · (…)` then vanishes, and the result
  -- is `a = zero_extend 64 (bool_to_bit (b.toInt < c.toInt))`.
  -- =====================================================================

  lemma spec_SLT
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_slt : air.cols.values.is_slt row 0 = 1)
    (h_is_cmp : air.cols.values.is_cmp row 0 = 0)
  :
    ALUBus.Spec
      8  -- LtChip emits ALU entries with `ALU_opcode = 8` for SLT
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨h_excl_slt, _⟩ := selector_exclusivity air row h_constraints
    have h_is_slt_u : air.cols.values.is_slt_u row 0 = 0 := h_excl_slt h_is_slt
    have h_is_real : air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1
      := by rw [h_is_slt, h_is_slt_u]; ring
    obtain ⟨h_bit_bool, -, -, h_signed_iff, -, h_a0, h_a1, h_a2, h_a3⟩ :=
      row_facts air row h_ext_asm h_wf_asm h_constraints h_is_real
    have h_iff := h_signed_iff h_is_slt
    rw [h_is_cmp, zero_mul] at h_a1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    . rw [h_a0]; rcases h_bit_bool with hb | hb <;> rw [hb] <;> decide
    . rw [h_a1]; decide
    . rw [h_a2]; decide
    . rw [h_a3]; decide
    simp [RV64IM.execute_RTYPE_pure, zopz0zI_s, U64w.toBV_toInt] at h_iff ⊢
    exact a_eq_setWidth_ite _ _ _ _ _ _ h_a1 h_a2 h_a3 h_a0 h_bit_bool h_iff

  --
  -- spec_SLTU — opcode 9 (unsigned compare, unmerged row)
  --

  lemma spec_SLTU
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_slt_u : air.cols.values.is_slt_u row 0 = 1)
    (h_is_cmp : air.cols.values.is_cmp row 0 = 0)
  :
    ALUBus.Spec
      9  -- LtChip emits ALU entries with `ALU_opcode = 9` for SLTU
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨_, h_excl_slt_u⟩ := selector_exclusivity air row h_constraints
    have h_is_slt : air.cols.values.is_slt row 0 = 0 := h_excl_slt_u h_is_slt_u
    have h_is_real : air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1
      := by rw [h_is_slt, h_is_slt_u]; ring
    obtain ⟨h_bit_bool, -, -, -, h_unsigned_iff, h_a0, h_a1, h_a2, h_a3⟩ :=
      row_facts air row h_ext_asm h_wf_asm h_constraints h_is_real
    have h_iff := h_unsigned_iff h_is_slt
    rw [h_is_cmp, zero_mul] at h_a1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    . rw [h_a0]; rcases h_bit_bool with hb | hb <;> rw [hb] <;> decide
    . rw [h_a1]; decide
    . rw [h_a2]; decide
    . rw [h_a3]; decide
    simp [RV64IM.execute_RTYPE_pure, zopz0zI_u, U64w.toBV_toNat] at h_iff ⊢
    exact a_eq_setWidth_ite _ _ _ _ _ _ h_a1 h_a2 h_a3 h_a0 h_bit_bool h_iff

  --
  -- spec_CMP_SLT — opcode 264 (signed branch comparison, merged row)
  --

  -- =====================================================================
  -- A merged row (`is_cmp = 1`) serves `SLT + LT_CMP_OPCODE_TAG`. It
  -- carries both strict comparison bits: `a_0 = [b < c]` from the
  -- gadget's `bit`, and `a_1 = Σ u16_flags − bit = [c < b]` because the
  -- flag sum is `[b ≠ c]`. The CPU recovers `[b = c]` as
  -- `1 − a_0 − a_1` (`riscv_cpu/branch/constraints.rs:98-117`).
  -- =====================================================================

  lemma spec_CMP_SLT
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_slt : air.cols.values.is_slt row 0 = 1)
    (h_is_cmp : air.cols.values.is_cmp row 0 = 1)
  :
    ALUBus.Spec
      264  -- SLT + LT_CMP_OPCODE_TAG
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨h_excl_slt, _⟩ := selector_exclusivity air row h_constraints
    have h_is_slt_u : air.cols.values.is_slt_u row 0 = 0 := h_excl_slt h_is_slt
    have h_is_real : air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1
      := by rw [h_is_slt, h_is_slt_u]; ring
    obtain ⟨h_bit_bool, h_sum_bool, h_sum_iff, h_signed_iff, -, h_a0, h_a1, h_a2, h_a3⟩ :=
      row_facts air row h_ext_asm h_wf_asm h_constraints h_is_real
    have h_iff := h_signed_iff h_is_slt
    rw [h_is_cmp, one_mul] at h_a1
    -- The flag sum's `toNat` equality lifted to `toInt`, so that both it
    -- and `bit` speak of the same (signed) order.
    have h_sum_iff_int :
      (air.cols.values.lt_signed.result.u16_flags_0 row 0
        + air.cols.values.lt_signed.result.u16_flags_1 row 0
        + air.cols.values.lt_signed.result.u16_flags_2 row 0
        + air.cols.values.lt_signed.result.u16_flags_3 row 0 = 0) ↔
      (U64w.toBV #v[air.cols.values.b_0 row 0, air.cols.values.b_1 row 0,
                    air.cols.values.b_2 row 0, air.cols.values.b_3 row 0]).toInt
        = (U64w.toBV #v[air.cols.values.c_0 row 0, air.cols.values.c_1 row 0,
                        air.cols.values.c_2 row 0, air.cols.values.c_3 row 0]).toInt := by
      rw [h_sum_iff, BitVec.toNat_inj, ← BitVec.toInt_inj]
    obtain ⟨h_a1_bool, h_a1_iff⟩ :=
      gt_eq_sum_sub_lt h_sum_bool h_bit_bool h_sum_iff_int h_iff h_a1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h_a2, h_a3⟩
    . rw [h_a0]; rcases h_bit_bool with hb | hb <;> rw [hb] <;> decide
    . rcases h_a1_bool with hb | hb <;> rw [hb] <;> decide
    . rw [h_a2]; decide
    . rw [h_a3]; decide
    . rw [h_a0]
      simp only [BitVec.slt_eq_decide, decide_eq_true_eq]
      exact bool_eq_ite _ _ h_bit_bool h_iff
    . simp only [BitVec.slt_eq_decide, decide_eq_true_eq]
      exact bool_eq_ite _ _ h_a1_bool h_a1_iff

  --
  -- spec_CMP_SLTU — opcode 265 (unsigned branch comparison, merged row)
  --

  lemma spec_CMP_SLTU
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_slt_u : air.cols.values.is_slt_u row 0 = 1)
    (h_is_cmp : air.cols.values.is_cmp row 0 = 1)
  :
    ALUBus.Spec
      265  -- SLTU + LT_CMP_OPCODE_TAG
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨_, h_excl_slt_u⟩ := selector_exclusivity air row h_constraints
    have h_is_slt : air.cols.values.is_slt row 0 = 0 := h_excl_slt_u h_is_slt_u
    have h_is_real : air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1
      := by rw [h_is_slt, h_is_slt_u]; ring
    obtain ⟨h_bit_bool, h_sum_bool, h_sum_iff, -, h_unsigned_iff, h_a0, h_a1, h_a2, h_a3⟩ :=
      row_facts air row h_ext_asm h_wf_asm h_constraints h_is_real
    have h_iff := h_unsigned_iff h_is_slt
    rw [h_is_cmp, one_mul] at h_a1
    obtain ⟨h_a1_bool, h_a1_iff⟩ :=
      gt_eq_sum_sub_lt h_sum_bool h_bit_bool h_sum_iff h_iff h_a1
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h_a2, h_a3⟩
    . rw [h_a0]; rcases h_bit_bool with hb | hb <;> rw [hb] <;> decide
    . rcases h_a1_bool with hb | hb <;> rw [hb] <;> decide
    . rw [h_a2]; decide
    . rw [h_a3]; decide
    . rw [h_a0]
      simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
      exact bool_eq_ite _ _ h_bit_bool h_iff
    . simp only [BitVec.ult_eq_decide, decide_eq_true_eq]
      exact bool_eq_ite _ _ h_a1_bool h_a1_iff

  --
  -- Externals — vacuous: byte entries have trivial externals; the
  -- chip's ALU entry is emitted with `multiplicity = is_slt + is_slt_u`,
  -- which is never `-1`, so `ext_assert_cond` never fires.
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row, LtChip.AbsBuses,
          LtSignedGadget.AbsBuses, U16MSBGadget.AbsBuses,
          LtWordU16Gadget.AbsBuses]
    intro h; exfalso; grind

  --
  -- wf_asrt — dispatches to the four result specifications
  --

  -- =====================================================================
  -- 3 byte entries (multiplicity `is_slt` or `is_slt + is_slt_u`,
  -- both ∈ {0, 1}) never trigger `wf_assert_cond` (= multiplicity -1),
  -- so they're vacuously well-formed.
  -- 1 ALU entry (multiplicity `-(is_slt + is_slt_u)` ∈ {0, -1}) is
  -- well-formed by one of `spec_SLT` / `spec_SLTU` / `spec_CMP_SLT` /
  -- `spec_CMP_SLTU`: the active selector picks the signedness and
  -- `is_cmp` picks whether the served opcode carries the merged-row
  -- tag.
  -- =====================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row, LtChip.AbsBuses,
          LtSignedGadget.AbsBuses, U16MSBGadget.AbsBuses,
          LtWordU16Gadget.AbsBuses]
    have h_cmp_bool : air.cols.values.is_cmp row 0 = 0 ∨ air.cols.values.is_cmp row 0 = 1 := by
      obtain ⟨-, -, -, -, -, h_c3, -⟩ := allHold_abs air row h_constraints
      simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c3
      exact h_c3
    refine ⟨?_, ?_⟩
    -- ALU entry: the active selector picks the signedness, `is_cmp`
    -- picks whether the opcode carries the merged-row tag.
    . intro h_real
      obtain ⟨h_slt_disj, h_slt_u_disj, _⟩ := selectors
      rcases h_slt_disj with h_slt | h_slt
      . -- is_slt = 0 ⇒ is_slt_u = 1 (since sum = 1)
        have h_slt_u : air.cols.values.is_slt_u row 0 = 1 := by grind
        rcases h_cmp_bool with h_cmp | h_cmp
        . simp [h_slt, h_slt_u, h_cmp]
          exact spec_SLTU air row h_ext_asm h_wf_asm h_constraints h_slt_u h_cmp
        . simp [h_slt, h_slt_u, h_cmp]
          exact spec_CMP_SLTU air row h_ext_asm h_wf_asm h_constraints h_slt_u h_cmp
      . -- is_slt = 1 ⇒ is_slt_u = 0
        have h_slt_u : air.cols.values.is_slt_u row 0 = 0 := by grind
        rcases h_cmp_bool with h_cmp | h_cmp
        . simp [h_slt, h_slt_u, h_cmp]
          exact spec_SLT air row h_ext_asm h_wf_asm h_constraints h_slt h_cmp
        . simp [h_slt, h_slt_u, h_cmp]
          exact spec_CMP_SLT air row h_ext_asm h_wf_asm h_constraints h_slt h_cmp
    -- Byte entries: vacuous (multiplicity ≥ 0, never -1).
    . split_ands <;> intro h <;> exfalso <;> grind

end LtChip.Spec
