import PicoFV.RV64IM.Spec.AddwGadget
import PicoFV.RV64IM.Constraints.AddwChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddwChip — semantic specification

The `AddwChip.Spec` namespace below states the semantic content of the
chip and demonstrates re-use of the gadget's spec:

- `ext_asrt` — externality assertions on the chip's bus row
              (vacuous: byte/ALU buses have no chip-external
              constraints relevant to AddwChip).
- `spec`     — the addw correctness `value = execute_RTYPEW_pure b c .ADDW`,
              proved by invoking `AddwGadget.Spec.gadget_spec` (the gadget
              already does the carry-chain algebra + sign-extension
              identity; the chip only substitutes its own accessors).
- `wf_asrt`  — well-formedness assertions on emitted entries
              (the byte-bus entries are vacuous, but the ALU entry's
              `wf_assert` requires the spec's conclusion).

Re-use pattern (identical to `AddChip.Spec` / `SubChip.Spec`):

1. `AddwChip.Interpretations.allHold_abs` ⇒ `AddwGadget.AbsConstraints`.
2. The chip's bus-row hypotheses about the gadget's contribution are
   stated directly via `AddwGadget.AbsBuses` (using `bus_row_abs` to
   bridge to the chip's typed `bus_row`).
3. `AddwGadget.Spec.gadget_spec` (parametric) ⇒ the ADDW correctness
   plus the sign-extension shape.

The chip adds an extra `ALUBus` entry that the gadget doesn't, and
takes operand range hypotheses externally (the chip itself does not
range-check `operand_1` / `operand_2`).
-/

namespace AddwChip.Spec

  open RV64IM_Interactions
  open AddwChip.ConstraintsAndBuses
  open AddwChip.Interactions
  open AddwChip.Interpretations

  set_option maxHeartbeats 1_000_000_000

  --
  -- Externals
  --

  -- =====================================================================
  -- Externality assertions for the AddwChip bus row.
  -- The chip emits only `ByteBus` and `ALUBus` entries. `ByteBus` has no
  -- chip-external constraints; for `ALUBus`, the externals (opcode-range
  -- + conditional operand-range for shifts/MUL/DIV/W-variants) don't
  -- apply when the chip asserts an entry (multiplicity = +is_addw), so
  -- `ext_assert` is trivially `True`.
  -- =====================================================================

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_AddwChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddwChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row, AddwChip.AbsBuses, AddwGadget.AbsBuses]
    intro h; exfalso; grind

  --
  -- Semantic specification — reuses AddwGadget.Spec.gadget_spec
  --

  -- =====================================================================
  -- spec: the chip's ADDW correctness. Proved entirely by deferring to
  -- `AddwGadget.Spec.gadget_spec` after substituting the chip's
  -- accessors for the gadget's column-value parameters.
  --
  -- The chip-level wrapper:
  --   * derives `AbsConstraints` from `allHold` via `allHold_abs`,
  --   * passes the AbsBuses-routed bus hypotheses through unchanged,
  --   * extracts operand u16-ranges from the chip's `ALUBus` external
  --     assumption (these come from `CpuChip`'s state bus / range
  --     checks, transported through the ALU bus to the AddwChip's row).
  -- =====================================================================

  lemma spec
    [Field ExtF]
    (air : Valid_AddwChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddwChip.Extraction.allHold air row)
    (h_is_addw : air.cols.values.is_addw row 0 = 1)
  :
    ALUBus.Spec
      40  -- AddwChip emits ALU entries with `ALU_opcode = 40` (Opcode::ADDW)
      (air.cols.values.addw_operation.value_0 row 0)
      (air.cols.values.addw_operation.value_1 row 0)
      (air.cols.values.addw_operation.msb.msb row 0 * 65535)
      (air.cols.values.addw_operation.msb.msb row 0 * 65535)
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
    -- Rewrite chip's bus_row into `AddwGadget.AbsBuses ++ chip_extras` and
    -- split the bus-side hypotheses via the `_append` lemmas.
    rw [bus_row_abs, AddwChip.AbsBuses,
        bus_row_ext_asm_append] at h_ext_asm
    rw [bus_row_abs, AddwChip.AbsBuses,
        bus_row_wf_asm_append] at h_wf_asm
    obtain ⟨ h_gadget_ext_asm, h_chip_ext_asm ⟩ := h_ext_asm
    obtain ⟨ h_gadget_wf_asm, _h_chip_wf_asm ⟩ := h_wf_asm
    -- Extract operand u16 bounds from the chip's ALU-entry external
    -- assumption: opcode 40 ∉ `ALUBus.operandsInternal`, so externals
    -- supply `ALUBus.operandRange`.
    simp [bus_row_ext_asm, ALUBus.externals, ALUBus.operandsInternal,
          ALUBus.validOpcode, ALUBus.operandRange, h_is_addw] at h_chip_ext_asm
    obtain ⟨ h_b0, h_b1, _h_b2, _h_b3, h_c0, h_c1, _h_c2, _h_c3 ⟩ := h_chip_ext_asm
    -- Apply the gadget's pure spec with the chip's accessors plugged in
    -- for the column-value parameters. Yields value bounds + the
    -- 32-bit ADDW equation with sign-extended high limbs.
    have h_gadget_spec := AddwGadget.Spec.gadget_spec
      (air.cols.values.is_addw row 0)
      (air.cols.values.operand_1_0 row 0) (air.cols.values.operand_1_1 row 0)
      (air.cols.values.operand_1_2 row 0) (air.cols.values.operand_1_3 row 0)
      (air.cols.values.operand_2_0 row 0) (air.cols.values.operand_2_1 row 0)
      (air.cols.values.operand_2_2 row 0) (air.cols.values.operand_2_3 row 0)
      (air.cols.values.addw_operation.value_0 row 0)
      (air.cols.values.addw_operation.value_1 row 0)
      (air.cols.values.addw_operation.msb.msb row 0)
      h_gadget_ext_asm h_gadget_wf_asm h_gadget_constraints
      h_is_addw
      ⟨ h_b0, h_b1 ⟩
      ⟨ h_c0, h_c1 ⟩
    obtain ⟨ h_v0, h_v1, h_v_ext, h_eq ⟩ := h_gadget_spec
    -- For opcode 40, `ALUBus.Spec` reduces to `result_range ∧ a = ADDW`.
    refine ⟨ ⟨ h_v0, h_v1, h_v_ext, h_v_ext ⟩, ?_ ⟩
    exact h_eq

  --
  -- Well-formedness — dispatches to `spec` for the single ALU entry
  --

  -- =====================================================================
  -- Mirrors `AddChip.Spec.wf_asrt`:
  --   * 3 byte entries (multiplicity `-is_addw` ∈ {0, -1}) never trigger
  --     `wf_assert_cond` (= multiplicity 1), so they're vacuously
  --     well-formed.
  --   * 1 ALU entry (multiplicity `is_addw` ∈ {0, 1}) is well-formed by
  --     `spec` whenever `is_addw = 1`.
  -- =====================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_AddwChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddwChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row, AddwChip.AbsBuses, AddwGadget.AbsBuses]
    refine ⟨?_, ?_⟩
    -- ALU entry: apply spec when is_addw = 1
    . intro h_is_addw
      exact spec air row h_ext_asm h_wf_asm h_constraints h_is_addw
    -- Byte entries: vacuous (multiplicity = -is_addw never equals 1)
    . split_ands <;> intro h <;> exfalso <;> grind

end AddwChip.Spec
