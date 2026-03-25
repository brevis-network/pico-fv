import PicoFV.RV32IM.Constraints.AddSubAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace AddSubAir.Spec

  open RV32IM_Interactions
  open AddSubAir.ConstraintsAndBuses
  open AddSubAir.Interactions
  open AddSubAir.Interpretations

  set_option maxHeartbeats 1_000_000_000

  --
  -- Externals
  --

  -- ==============================================
  -- Externality assertions for the AddSub bus row.
  -- ==============================================

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_AddSubAir FKB ExtF)
    (row : ℕ)
    (h_constraints : AddSubAir.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    obtain ⟨ h_b_add, h_b_sub, h_b_sum ⟩ := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row]
    grind (splits := 20)

  --
  -- Opcode specifications
  --

  -- ================================================================
  -- ADD (opcode 0): proves add_value = operand_1 + operand_2 as U32.
  -- Case-splits on 3 carry bits (8 cases), closes with omega.
  -- ================================================================

  lemma spec_ADD
    [Field ExtF]
    (air : Valid_AddSubAir FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddSubAir.Extraction.allHold air row)
    (h_add : air.cols.is_add row 0 = 1)
  :
    ALUBus.Spec
      (air.cols.is_sub row 0)
      (air.cols.add_value_0 row 0)
      (air.cols.add_value_1 row 0)
      (air.cols.add_value_2 row 0)
      (air.cols.add_value_3 row 0)
      (air.cols.operand_1_0 row 0)
      (air.cols.operand_1_1 row 0)
      (air.cols.operand_1_2 row 0)
      (air.cols.operand_1_3 row 0)
      (air.cols.operand_2_0 row 0)
      (air.cols.operand_2_1 row 0)
      (air.cols.operand_2_2 row 0)
      (air.cols.operand_2_3 row 0)
  := by
    -- Establish is_sub = 0
    have selectors := selector_breakdown air row h_constraints
    have h_sub : air.cols.is_sub row 0 = 0 := by grind
    -- Simplify ALUBus.Spec with opcode = 0 (ADD)
    simp only [ALUBus.Spec, h_sub, and_assoc]
    -- Simplify constraints and assumptions
    simp [constraint_and_interaction_simplification, sub_eq_zero, h_add, h_sub] at h_constraints
    simp [bus_row_wf_asm, bus_row, h_add, h_sub, ByteBus.Spec] at h_wf
    -- Extract byte bounds
    obtain ⟨⟨h_op1_0, h_op1_1⟩, ⟨h_op1_2, h_op1_3⟩, ⟨h_op2_0, h_op2_1⟩, ⟨h_op2_2, h_op2_3⟩,
            ⟨h_av0, h_av1⟩, h_av2, h_av3⟩ := h_wf
    -- Extract constraint components
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc10, hc11, hc12⟩ := h_constraints
    -- Provide byte bounds, leaving only the addition equation
    refine ⟨h_av0, h_av1, h_av2, h_av3, h_op1_0, h_op1_1, h_op1_2, h_op1_3, h_op2_0, h_op2_1, h_op2_2, h_op2_3, ?_⟩
    -- Convert BitVec equation to Nat equation
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, U32.toBV_toNat, U32.toNat, BitVec.toNat_ofNat]
    -- Case split on carries and close each case
    rcases hc10 <;> simp_all <;>
    rcases hc11 <;> simp_all <;>
    rcases hc12 <;> simp_all <;>
    omega

  -- =================================================================================
  -- SUB (opcode 1): proves operand_1 = add_value + operand_2
  -- (i.e. add_value = operand_1 - operand_2). Same carry case-split technique as ADD.
  -- =================================================================================

  lemma spec_SUB
    [Field ExtF]
    (air : Valid_AddSubAir FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddSubAir.Extraction.allHold air row)
    (h_add : air.cols.is_sub row 0 = 1)
  :
    ALUBus.Spec
      (air.cols.is_sub row 0)
      (air.cols.operand_1_0 row 0)
      (air.cols.operand_1_1 row 0)
      (air.cols.operand_1_2 row 0)
      (air.cols.operand_1_3 row 0)
      (air.cols.add_value_0 row 0)
      (air.cols.add_value_1 row 0)
      (air.cols.add_value_2 row 0)
      (air.cols.add_value_3 row 0)
      (air.cols.operand_2_0 row 0)
      (air.cols.operand_2_1 row 0)
      (air.cols.operand_2_2 row 0)
      (air.cols.operand_2_3 row 0)
  := by
    -- Establish is_add = 0
    have selectors := selector_breakdown air row h_constraints
    have h_is_add : air.cols.is_add row 0 = 0 := by grind
    -- Simplify ALUBus.Spec with opcode = 1 (SUB)
    simp only [ALUBus.Spec, h_add, and_assoc]
    -- Simplify constraints and assumptions
    simp [constraint_and_interaction_simplification, sub_eq_zero, h_is_add, h_add] at h_constraints
    simp [bus_row_wf_asm, bus_row, h_is_add, h_add, ByteBus.Spec] at h_wf
    -- Extract byte bounds
    obtain ⟨⟨h_op1_0, h_op1_1⟩, ⟨h_op1_2, h_op1_3⟩, ⟨h_op2_0, h_op2_1⟩, ⟨h_op2_2, h_op2_3⟩,
            ⟨h_av0, h_av1⟩, h_av2, h_av3⟩ := h_wf
    -- Extract constraint components
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc10, hc11, hc12⟩ := h_constraints
    -- Provide byte bounds, leaving only the subtraction equation
    refine ⟨h_op1_0, h_op1_1, h_op1_2, h_op1_3, h_av0, h_av1, h_av2, h_av3, h_op2_0, h_op2_1, h_op2_2, h_op2_3, ?_⟩
    -- Convert BitVec equation to Nat equation
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, U32.toBV_toNat, U32.toNat, BitVec.toNat_ofNat]
    -- Case split on carries and close each case
    rcases hc10 <;> simp_all <;>
    rcases hc11 <;> simp_all <;>
    rcases hc12 <;> simp_all <;>
    omega

  --
  -- Well-formedness
  --

  -- =============================================================================
  -- Well-formedness: dispatches to spec_ADD or spec_SUB based on active selector.
  -- =============================================================================

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_AddSubAir FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : AddSubAir.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    -- Set up assumptions
    have h_wf' := h_wf
    simp [bus_row_wf_asm] at h_wf'
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf'
    -- Main proof
    simp [bus_row_wf_asrt]
    constructor
    -- Program
    . simp [bus_row]
    . constructor
      . -- ALU
        simp [bus_row]
        split_ands <;> intro h_opcode
        . apply spec_ADD air row h_wf h_constraints h_opcode
        . apply spec_SUB air row h_wf h_constraints h_opcode
      . constructor
        . -- Byte
          simp [bus_row, ByteBus.Spec]
          have selectors := selector_breakdown air row h_constraints
          split_ands <;> intro h <;> exfalso <;> grind
        . -- Register
          simp [bus_row]

end AddSubAir.Spec
