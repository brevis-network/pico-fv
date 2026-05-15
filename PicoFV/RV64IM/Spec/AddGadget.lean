import PicoFV.RV64IM.Constraints.AddGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddGadget — semantic specification

The `AddGadget.Spec` namespace below states the semantic content of the
gadget: under the gadget's constraints and external u16-range
assumptions on the operand limbs, the result word satisfies the actual
64-bit addition `value = b + c`. This is the *semantic* counterpart of
`AddGadget.AbsConstraints` (which only states the polynomial constraint
shape).

Layout mirrors `PicoFV.RV32IM.Spec.AddSubAir`:

- `ext_asrt`     — externality assertions on the gadget's bus row
                    (vacuous: the byte bus has no chip-external
                    constraints).
- `spec_addition` — the semantic statement `value = b + c` (RV64
                    analogue of `spec_ADD`).
- `wf_asrt`      — well-formedness assertions on emitted entries
                    (vacuous: all entries have multiplicity `-is_real`,
                    so `wf_assert_cond` is never satisfied).
-/

namespace AddGadget.Spec

  open RV64IM_Interactions
  open AddGadget.ConstraintsAndBuses
  open AddGadget.Interactions
  open AddGadget.Interpretations

  set_option maxHeartbeats 1_000_000_000

  --
  -- Externals
  --

  -- =====================================================================
  -- Externality assertions for the AddGadget bus row.
  -- The gadget emits only `ByteBus` entries, and `ByteBus.externals`
  -- is `fun _ => True`, so `ext_assert` is trivially `True` on every
  -- entry.
  -- =====================================================================

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_AddGadgetAir FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (_h_constraints : AddGadget.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    simp [bus_row_ext_asrt, bus_row, AddGadget.AbsBuses]

  --
  -- Semantic specification
  --

  -- =====================================================================
  -- spec_addition (RV64 analogue of `spec_ADD`): proves the actual
  -- 64-bit addition `value = b + c` (as `BitVec 64` via `U64w.toBV`)
  -- under:
  --   * `is_real = 1`,
  --   * the gadget's constraints,
  --   * the gadget's own wf assumption on the result limbs
  --     (`value_i < 65536`, provided by the byte-bus reads),
  --   * externally-supplied u16 bounds on the operand limbs
  --     `b_i`, `c_i` (which the gadget does *not* enforce on its own —
  --     the chip embedding the gadget is responsible for providing
  --     them, e.g. via its own byte-bus entries or via the ALU bus
  --     externals).
  -- =====================================================================

  /-- Pure / parametric gadget spec: stated entirely in terms of the 13
      `FKB` column values that flow through the gadget. No mention of an
      air or a row. The chip-side spec recovers the gadget's `AbsBuses`
      and `AbsConstraints` hypotheses from its own air-based hypotheses
      via `bus_row_abs` / `allHold_abs` (+ the `_append` lemmas to split
      gadget vs chip portions) and then invokes this lemma with its own
      accessors substituted for the parameters.

      For the standalone `Valid_AddGadgetAir`, the air-based wrapper
      `spec_air` below does the same plumbing with no chip extras. -/
  lemma gadget_spec
    (is_real
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     value_0 value_1 value_2 value_3 : FKB)
    (_h_gadget_ext_asm :
      bus_row_ext_asm
        (AddGadget.AbsBuses is_real value_0 value_1 value_2 value_3))
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (AddGadget.AbsBuses is_real value_0 value_1 value_2 value_3))
    (h_gadget_constraints :
      AddGadget.AbsConstraints
        is_real b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
        value_0 value_1 value_2 value_3)
    (h_is_real : is_real = 1)
    (h_b_range :
      b_0.val < 65536 ∧ b_1.val < 65536 ∧
      b_2.val < 65536 ∧ b_3.val < 65536)
    (h_c_range :
      c_0.val < 65536 ∧ c_1.val < 65536 ∧
      c_2.val < 65536 ∧ c_3.val < 65536)
  :
    value_0.val < 65536 ∧
    value_1.val < 65536 ∧
    value_2.val < 65536 ∧
    value_3.val < 65536 ∧
    U64w.toBV #v[value_0, value_1, value_2, value_3]
    =
    U64w.toBV #v[b_0, b_1, b_2, b_3]
    +
    U64w.toBV #v[c_0, c_1, c_2, c_3]
  := by
    simp [bus_row_wf_asm, AbsBuses, h_is_real, ByteBus.Spec] at h_gadget_wf_asm
    simp [h_gadget_wf_asm]
    simp [AbsConstraints, h_is_real, sub_eq_zero (b := (1 : FKB))] at h_gadget_constraints
    obtain ⟨ h0, h1, h2, h3 ⟩ := h_gadget_constraints
    apply BitVec.eq_of_toNat_eq
    simp [U64w.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
    obtain h0 | h0 := h0 <;>
    simp [h0] at h1 h2 h3 <;>
      obtain h1 | h1 := h1 <;>
      simp [h1] at h2 h3 <;>
        obtain h2 | h2 := h2 <;>
        simp [h2] at h3 <;>
          obtain h3 | h3 := h3  <;>
          omega

  /-- Air-based wrapper for the standalone gadget air: feeds
      `Valid_AddGadgetAir`-shaped hypotheses (typed `bus_row`,
      `Extraction.allHold`) into the pure `spec` by decomposing through
      `bus_row_abs` and `allHold_abs`. -/
  lemma spec
    [Field ExtF]
    (air : Valid_AddGadgetAir FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddGadget.Extraction.allHold air row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_b_range :
      (air.cols.b_0 row 0).val < 65536 ∧
      (air.cols.b_1 row 0).val < 65536 ∧
      (air.cols.b_2 row 0).val < 65536 ∧
      (air.cols.b_3 row 0).val < 65536)
    (h_c_range :
      (air.cols.c_0 row 0).val < 65536 ∧
      (air.cols.c_1 row 0).val < 65536 ∧
      (air.cols.c_2 row 0).val < 65536 ∧
      (air.cols.c_3 row 0).val < 65536)
  :
    (air.cols.gadget.value_0 row 0).val < 65536 ∧
    (air.cols.gadget.value_1 row 0).val < 65536 ∧
    (air.cols.gadget.value_2 row 0).val < 65536 ∧
    (air.cols.gadget.value_3 row 0).val < 65536 ∧
    U64w.toBV
      #v[ air.cols.gadget.value_0 row 0,
          air.cols.gadget.value_1 row 0,
          air.cols.gadget.value_2 row 0,
          air.cols.gadget.value_3 row 0 ]
    =
    U64w.toBV
      #v[ air.cols.b_0 row 0, air.cols.b_1 row 0,
          air.cols.b_2 row 0, air.cols.b_3 row 0 ]
    +
    U64w.toBV
      #v[ air.cols.c_0 row 0, air.cols.c_1 row 0,
          air.cols.c_2 row 0, air.cols.c_3 row 0 ]
  := by
    have h_gadget_constraints := allHold_abs air row h_constraints
    rw [bus_row_abs] at h_ext_asm h_wf_asm
    exact gadget_spec
      (air.cols.is_real row 0)
      (air.cols.b_0 row 0) (air.cols.b_1 row 0)
      (air.cols.b_2 row 0) (air.cols.b_3 row 0)
      (air.cols.c_0 row 0) (air.cols.c_1 row 0)
      (air.cols.c_2 row 0) (air.cols.c_3 row 0)
      (air.cols.gadget.value_0 row 0) (air.cols.gadget.value_1 row 0)
      (air.cols.gadget.value_2 row 0) (air.cols.gadget.value_3 row 0)
      h_ext_asm h_wf_asm h_gadget_constraints
      h_is_real h_b_range h_c_range

  --
  -- Well-formedness
  --

  -- =====================================================================
  -- Well-formedness: trivially holds because every byte-bus entry the
  -- gadget emits has multiplicity `-(is_real)`. Since `is_real ∈ {0, 1}`
  -- (by `selector_breakdown`), the multiplicity is either `0` or `-1` —
  -- never `1` — so `wf_assert_cond` (= multiplicity equals `1`) is
  -- vacuously false on every entry.
  -- =====================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_AddGadgetAir FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddGadget.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row, AddGadget.AbsBuses]
    split_ands <;> intro h <;> exfalso <;> grind

end AddGadget.Spec
