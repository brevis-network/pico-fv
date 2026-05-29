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
  is emitted with positive multiplicity `is_slt + is_slt_u`, so
  `ext_assert_cond` (= multiplicity = -1) never fires.
- `spec_SLT`  — opcode 8 (signed compare). Uses
  `LtSignedGadget.Spec.gadget_spec` at `is_signed = 1` and bridges
  the resulting `bit ↔ b.toInt < c.toInt` to
  `a = zero_extend (bool_to_bit ...)` via the chip's `a_0 = bit`
  identity + `a_{1,2,3} = 0` zeroing.
- `spec_SLTU` — opcode 9 (unsigned compare). Identical to `spec_SLT`
  except `is_signed = 0` (`bit ↔ b.toNat < c.toNat`).
- `wf_asrt` — dispatches the single ALU entry to `spec_SLT` /
  `spec_SLTU` based on which selector is active; byte entries are
  vacuous (`-is_real ∈ {0, -1}`, never `1`).

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
  -- spec_SLT — opcode 8 (signed compare)
  --

  -- =====================================================================
  -- spec_SLT: the chip's signed less-than correctness. Defers to
  -- `LtSignedGadget.Spec.gadget_spec` with `is_signed = 1` (taken from
  -- `is_slt = 1`), then bridges to the ALUBus.Spec format via
  -- `a = zero_extend 64 (bool_to_bit (b.toInt < c.toInt))`.
  --
  -- The operand u16-ranges are extracted from the chip's ALU external
  -- assumption: opcode 8 ∉ `ALUBus.operandsInternal`, so externals
  -- supply `ALUBus.operandRange`.
  -- =====================================================================

  lemma spec_SLT
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_slt : air.cols.values.is_slt row 0 = 1)
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
    -- Selector exclusivity: is_slt_u = 0, so is_real = is_slt.
    obtain ⟨h_excl_slt, _⟩ := selector_exclusivity air row h_constraints
    have h_is_slt_u : air.cols.values.is_slt_u row 0 = 0 := h_excl_slt h_is_slt
    have h_is_real : air.cols.values.is_slt row 0 + air.cols.values.is_slt_u row 0 = 1
      := by rw [h_is_slt, h_is_slt_u]; ring
    -- Decompose `allHold` into `LtSignedGadget.AbsConstraints` + chip extras.
    have h_abs := allHold_abs air row h_constraints
    obtain ⟨h_gadget_constraints, h_c27, h_c28, h_c29, h_c30⟩ := h_abs
    -- Decompose chip's `bus_row` into gadget + chip ALU entry.
    rw [bus_row_abs, LtChip.AbsBuses,
        bus_row_ext_asm_append] at h_ext_asm
    rw [bus_row_abs, LtChip.AbsBuses,
        bus_row_wf_asm_append] at h_wf_asm
    obtain ⟨h_gadget_ext_asm, h_chip_ext_asm⟩ := h_ext_asm
    obtain ⟨h_gadget_wf_asm, _h_chip_wf_asm⟩ := h_wf_asm
    -- Extract operand u16 bounds from chip's ALU external assumption
    -- (opcode 8 ∉ operandsInternal, so externals enforce operand_range).
    simp [bus_row_ext_asm, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_slt, h_is_slt_u]
      at h_chip_ext_asm
    obtain ⟨h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3⟩ := h_chip_ext_asm
    -- Apply the gadget's pure spec at is_signed = 1.
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
      ⟨h_c0, h_c1, h_c2, h_c3⟩
    obtain ⟨h_bit_bool, _h_unsigned_iff, h_signed_iff⟩ := h_gadget_spec
    -- Fire the signed branch.
    have h_iff := h_signed_iff h_is_slt
    -- Extract a_1 = a_2 = a_3 = 0 and a_0 = bit from chip's constraints 27-30.
    simp [constraint_and_interaction_simplification] at h_c27 h_c28 h_c29 h_c30
    have h_a0_eq : air.cols.values.a_0 row 0 = air.cols.values.lt_signed.result.bit row 0
      := by clear *- h_c30 h_is_real; grind
    -- For opcode 8, `ALUBus.Spec` reduces to `result_range ∧ a = SLT_pure`.
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    -- Result limb ranges: a_0 ∈ {0, 1}, a_1 = a_2 = a_3 = 0.
    . rw [h_a0_eq]; rcases h_bit_bool with hb | hb <;> rw [hb] <;> decide
    . rw [h_c27]; decide
    . rw [h_c28]; decide
    . rw [h_c29]; decide
    -- Result equation: a = setWidth 64 (if b.toInt < c.toInt then 1 else 0).
    simp [RV64IM.execute_RTYPE_pure, zopz0zI_s, U64w.toBV_toInt] at h_iff ⊢
    exact a_eq_setWidth_ite _ _ _ _ _ _ h_c27 h_c28 h_c29 h_a0_eq h_bit_bool h_iff

  --
  -- spec_SLTU — opcode 9 (unsigned compare)
  --

  -- =====================================================================
  -- spec_SLTU: mirrors `spec_SLT` but with `is_slt = 0` and
  -- `is_slt_u = 1`, firing the gadget's `is_signed = 0` branch
  -- (unsigned `bit = 1 ↔ b.toNat < c.toNat`).
  -- =====================================================================

  lemma spec_SLTU
    [Field ExtF]
    (air : Valid_LtChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : LtChip.Extraction.allHold air row)
    (h_is_slt_u : air.cols.values.is_slt_u row 0 = 1)
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
    have h_abs := allHold_abs air row h_constraints
    obtain ⟨h_gadget_constraints, h_c27, h_c28, h_c29, h_c30⟩ := h_abs
    rw [bus_row_abs, LtChip.AbsBuses,
        bus_row_ext_asm_append] at h_ext_asm
    rw [bus_row_abs, LtChip.AbsBuses,
        bus_row_wf_asm_append] at h_wf_asm
    obtain ⟨h_gadget_ext_asm, h_chip_ext_asm⟩ := h_ext_asm
    obtain ⟨h_gadget_wf_asm, _h_chip_wf_asm⟩ := h_wf_asm
    simp [bus_row_ext_asm, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_slt, h_is_slt_u]
      at h_chip_ext_asm
    obtain ⟨h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3⟩ := h_chip_ext_asm
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
      ⟨h_c0, h_c1, h_c2, h_c3⟩
    obtain ⟨h_bit_bool, h_unsigned_iff, _h_signed_iff⟩ := h_gadget_spec
    have h_iff := h_unsigned_iff h_is_slt
    simp [constraint_and_interaction_simplification] at h_c27 h_c28 h_c29 h_c30
    have h_a0_eq : air.cols.values.a_0 row 0 = air.cols.values.lt_signed.result.bit row 0
      := by clear *- h_c30 h_is_real; grind
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    . rw [h_a0_eq]; rcases h_bit_bool with hb | hb <;> rw [hb] <;> decide
    . rw [h_c27]; decide
    . rw [h_c28]; decide
    . rw [h_c29]; decide
    simp [RV64IM.execute_RTYPE_pure, zopz0zI_u, U64w.toBV_toNat] at h_iff ⊢
    exact a_eq_setWidth_ite _ _ _ _ _ _ h_c27 h_c28 h_c29 h_a0_eq h_bit_bool h_iff

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
  -- wf_asrt — dispatches to spec_SLT / spec_SLTU
  --

  -- =====================================================================
  -- 3 byte entries (multiplicity `-is_slt` or `-(is_slt + is_slt_u)`,
  -- both ∈ {0, -1}) never trigger `wf_assert_cond` (= multiplicity 1),
  -- so they're vacuously well-formed.
  -- 1 ALU entry (multiplicity `is_slt + is_slt_u` ∈ {0, 1}) is
  -- well-formed by `spec_SLT` / `spec_SLTU` based on which selector
  -- is active.
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
    refine ⟨?_, ?_⟩
    -- ALU entry: dispatch to spec_SLT / spec_SLTU based on selector.
    . intro h_real
      obtain ⟨h_slt_disj, h_slt_u_disj, _⟩ := selectors
      rcases h_slt_disj with h_slt | h_slt
      . -- is_slt = 0 ⇒ is_slt_u = 1 (since sum = 1)
        have h_slt_u : air.cols.values.is_slt_u row 0 = 1 := by grind
        simp [h_slt, h_slt_u]
        exact spec_SLTU air row h_ext_asm h_wf_asm h_constraints h_slt_u
      . -- is_slt = 1 ⇒ is_slt_u = 0
        have h_slt_u : air.cols.values.is_slt_u row 0 = 0 := by grind
        simp [h_slt, h_slt_u]
        exact spec_SLT air row h_ext_asm h_wf_asm h_constraints h_slt
    -- Byte entries: vacuous (multiplicity ≤ 0, never 1).
    . split_ands <;> intro h <;> exfalso <;> grind

end LtChip.Spec
