import PicoFV.RV64IM.Spec.AddGadget
import PicoFV.RV64IM.Constraints.AddChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddChip — semantic specification

The `AddChip.Spec` namespace below states the semantic content of the
chip and demonstrates re-use of the gadget's spec:

- `ext_asrt` — externality assertions on the chip's bus row
              (vacuous: byte/ALU buses have no chip-external
              constraints relevant to AddChip).
- `spec`     — the addition correctness `value = operand_1 + operand_2`,
              proved by invoking `AddGadget.Spec.spec` (the gadget
              already does the carry-chain algebra; the chip only
              substitutes its own accessors).
- `wf_asrt`  — well-formedness assertions on emitted entries
              (the byte-bus entries are vacuous, but the ALU entry's
              `wf_assert` requires the spec's conclusion).

Re-use pattern:

1. `AddChip.Interpretations.allHold_abs` ⇒ `AddGadget.AbsConstraints`.
2. The chip's bus-row hypotheses about the gadget's contribution are
   stated directly via `AddGadget.AbsBuses` (using `bus_row_abs` to
   bridge to the chip's typed `bus_row`).
3. `AddGadget.Spec.spec` (parametric) ⇒ the addition correctness.

The chip adds an extra `ALUBus` entry that the gadget doesn't, and
takes operand range hypotheses externally (the chip itself does not
range-check `operand_1` / `operand_2`).
-/

namespace AddChip.Spec

  open RV64IM_Interactions
  open AddChip.ConstraintsAndBuses
  open AddChip.Interactions
  open AddChip.Interpretations

  set_option maxHeartbeats 1_000_000_000

  --
  -- Externals
  --

  -- =====================================================================
  -- Externality assertions for the AddChip bus row.
  -- The chip emits only `ByteBus` and `ALUBus` entries. `ByteBus` has no
  -- chip-external constraints; for `ALUBus`, the externals (opcode-range
  -- + conditional operand-range for shifts/MUL/DIV/W-variants) don't
  -- apply when the chip asserts an entry (multiplicity = +is_add), so
  -- `ext_assert` is trivially `True`.
  -- =====================================================================

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_AddChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row, AddChip.AbsBuses, AddGadget.AbsBuses]
    intro h; exfalso; grind

  --
  -- Semantic specification — reuses AddGadget.Spec.spec
  --

  -- =====================================================================
  -- spec: the chip's addition correctness. Proved entirely by deferring
  -- to `AddGadget.Spec.spec` after substituting the chip's accessors for
  -- the gadget's column-value parameters.
  --
  -- The chip-level wrapper:
  --   * derives `AbsConstraints` from `allHold` via `allHold_abs`,
  --   * passes the AbsBuses-routed bus hypotheses through unchanged,
  --   * accepts operand u16-ranges as external hypotheses (these would
  --     normally come from `CpuChip`'s state bus / range checks).
  -- =====================================================================

  lemma spec
    [Field ExtF]
    (air : Valid_AddChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddChip.Extraction.allHold air row)
    (h_is_add : air.cols.values.is_add row 0 = 1)
  :
    ALUBus.Spec
      0  -- AddChip emits ALU entries with `ALU_opcode = 0` (Opcode::ADD)
      (air.cols.values.add_operation.value_0 row 0)
      (air.cols.values.add_operation.value_1 row 0)
      (air.cols.values.add_operation.value_2 row 0)
      (air.cols.values.add_operation.value_3 row 0)
      (air.cols.values.operand_1_0 row 0)
      (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0)
      (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0)
      (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0)
      (air.cols.values.operand_2_3 row 0)
  := by
    -- Decompose the raw `allHold` into the gadget's `AbsConstraints` plus
    -- the chip's extra `constraint_5`.
    have h_abs := allHold_abs air row h_constraints
    obtain ⟨ h_gadget_constraints, _h_constraint_5 ⟩ := h_abs
    -- Rewrite chip's bus_row into `AddGadget.AbsBuses ++ chip_extras` and
    -- split the bus-side hypotheses via the `_append` lemmas.
    rw [bus_row_abs, AddChip.AbsBuses,
        bus_row_ext_asm_append] at h_ext_asm
    rw [bus_row_abs, AddChip.AbsBuses,
        bus_row_wf_asm_append] at h_wf_asm
    obtain ⟨ h_gadget_ext_asm, h_chip_ext_asm ⟩ := h_ext_asm
    obtain ⟨ h_gadget_wf_asm, _h_chip_wf_asm ⟩ := h_wf_asm
    -- Extract operand u16 bounds from the chip's ALU-entry external
    -- assumption: opcode 0 ∉ `ALUBus.operandsInternal`, so externals
    -- supply `ALUBus.operandRange`.
    simp [bus_row_ext_asm, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_add] at h_chip_ext_asm
    obtain ⟨ h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3 ⟩ := h_chip_ext_asm
    -- Apply the gadget's pure spec with the chip's accessors plugged in
    -- for the 13 column-value parameters. Yields value bounds + the
    -- 64-bit addition equation.
    have h_gadget_spec := AddGadget.Spec.gadget_spec
      (air.cols.values.is_add row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.add_operation.value_0 row 0)
      (air.cols.values.add_operation.value_1 row 0)
      (air.cols.values.add_operation.value_2 row 0)
      (air.cols.values.add_operation.value_3 row 0)
      h_gadget_ext_asm h_gadget_wf_asm h_gadget_constraints
      h_is_add
      ⟨ h_b0, h_b1, h_b2, h_b3 ⟩
      ⟨ h_c0, h_c1, h_c2, h_c3 ⟩
    obtain ⟨ h_v0, h_v1, h_v2, h_v3, h_eq ⟩ := h_gadget_spec
    -- For opcode 0, `ALUBus.Spec` reduces to `result_range ∧ a = b + c`
    -- (the `execute_RTYPE_pure ... .ADD` branch unfolds to `b + c`).
    refine ⟨ ⟨ h_v0, h_v1, h_v2, h_v3 ⟩, ?_ ⟩
    simp [RV64IM.execute_RTYPE_pure]
    exact h_eq

  --
  -- Well-formedness — dispatches to `spec` for the single ALU entry
  --

  -- =====================================================================
  -- Mirrors `RV32IM.AddSubAir.Spec.wf_asrt`:
  --   * 4 byte entries (multiplicity `-is_add` ∈ {0, -1}) never trigger
  --     `wf_assert_cond` (= multiplicity 1), so they're vacuously
  --     well-formed.
  --   * 1 ALU entry (multiplicity `is_add` ∈ {0, 1}) is well-formed by
  --     `spec` whenever `is_add = 1`.
  -- =====================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_AddChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row, AddChip.AbsBuses, AddGadget.AbsBuses]
    refine ⟨?_, ?_⟩
    -- ALU entry: apply spec when is_add = 1
    . intro h_is_add
      exact spec air row h_ext_asm h_wf_asm h_constraints h_is_add
    -- Byte entries: vacuous (multiplicity = -is_add never equals 1)
    . split_ands <;> intro h <;> exfalso <;> grind

end AddChip.Spec
