import PicoFV.RV64IM.Constraints.SLLChip
import PicoFV.RV64IM.Spec.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# SLLChip — semantic specification

Ports the RV32 `SllAir.Spec` approach to the RV64 u16-limb width.
There are two ALU outputs (vs one for RV32):

- `spec_SLL`  (opcode 5):  64-bit left shift, shift amount = low 6 bits of `c`.
- `spec_SLLW` (opcode 42): 32-bit left shift, sign-extended to 64 bits;
  shift amount = low 5 bits of `c`.

The proof structure mirrors RV32:

1. Extract operand `< 65536` bounds from the chip's ALU externals
   (opcodes 5 / 42 are not in `ALUBus.operandsInternal`).
2. Extract byte-bus assumptions for each `(lower_limb_i, higher_limb_i)`
   pair (`BitRange` opcode 9) and the SLLW `U16MSBGadget` entry on `a_1`.
3. Simplify the 53 constraints into named hypotheses.
4. Lift the per-limb FKB carry equations
   `b_i · v_0123 = higher_limb_i · 65536 + lower_limb_i · v_0123`
   to Nat-level identities, using the bus bounds and the bit-shift
   booleans on `c_bits_0..3`.
5. Case-split on the low 6 bits (`c_bits_0..5`) — 64 cases for SLL,
   32 for SLLW (the SLLW selector forces `c_bits_5 = 0`-effective via
   the `c_bits_4 + 2·c_bits_5·is_sll` shift_u16 selector wiring).
6. In each case, the concrete values of `v_0123` and `shift_u16`
   resolve the chip's `a_i` assignments. Close with
   `BitVec.eq_of_toNat_eq + omega` (Nat-level shift identity).
-/

namespace SLLChip.Spec

  open RV64IM_Interactions
  open SLLChip.ConstraintsAndBuses
  open SLLChip.Interactions
  open SLLChip.Interpretations
  open LeanRV64D.Functions

  set_option maxHeartbeats 4_000_000_000

  -- Helpers (FKB → Nat carry / limb_result conversions) will be added as
  -- needed once the case-split structure in `spec_SLL` / `spec_SLLW`
  -- is in place.

  --
  -- spec_SLL — opcode 5 (64-bit left shift)
  --

  -- =====================================================================
  -- spec_SLL: 64-case split on c_bits_0..c_bits_5.
  -- For each case, the chip's witnesses (v_0123, shift_u16, lower/higher
  -- limb decomposition) become concrete and the result equation
  --   a = b << (c & 0x3F)
  -- closes via BitVec / omega arithmetic.
  -- =====================================================================

  lemma spec_SLL
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
    (h_is_sll : air.cols.values.is_sll row 0 = 1)
  :
    ALUBus.Spec
      5
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    sorry

  --
  -- spec_SLLW — opcode 42 (32-bit left shift, sign-extended)
  --

  lemma spec_SLLW
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
    (h_is_sllw : air.cols.values.is_sllw row 0 = 1)
  :
    ALUBus.Spec
      42
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    sorry

  --
  -- Externals — vacuous: byte entries have trivial externals; the
  -- ALU entry's `ext_assert_cond` (multiplicity = -1) never fires.
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row]
    intro h; exfalso; grind

  --
  -- wf_asrt — dispatches to spec_SLL / spec_SLLW
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_SLLChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : SLLChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row]
    refine ⟨?_, ?_⟩
    -- ALU entry: dispatch by selector.
    . intro h_real
      obtain ⟨h_sll_disj, h_sllw_disj, _⟩ := selectors
      rcases h_sll_disj with h_sll | h_sll
      . -- is_sll = 0 ⇒ is_sllw = 1
        have h_sllw : air.cols.values.is_sllw row 0 = 1 := by grind
        simp [h_sll, h_sllw]
        exact spec_SLLW air row h_ext h_wf h_constraints h_sllw
      . -- is_sll = 1 ⇒ is_sllw = 0
        have h_sllw : air.cols.values.is_sllw row 0 = 0 := by grind
        simp [h_sll, h_sllw]
        exact spec_SLL air row h_ext h_wf h_constraints h_sll
    -- Byte entries: vacuous (negative multiplicity, never +1).
    . split_ands <;> intro h <;> exfalso <;> grind

end SLLChip.Spec
