import PicoFV.Constraints.CpuAir

open Plonky3

set_option maxHeartbeats 1_000_000_000

namespace CpuAir.Spec

  open RV32IM_Interactions
  open CpuAir.ConstraintsAndBuses
  open CpuAir.Interactions
  open CpuAir.Interpretations

  set_option maxRecDepth 2_000_000

  attribute [local simp]
    program_bus_entry

  lemma is_branch_instruction_characterisation
    [Field ExtF]
    (air : Valid_CpuAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_assumptions : bus_row_assumptions (bus_row air row))
    (h_constraints : CpuAir.Extraction.allHold air row)
  :
    bus_row_assertions (bus_row air row)
  := by
    -- Set up selectors
    have selectors := opcode_selectors_breakdown air row h_is_real h_assumptions h_constraints
    have branching := branching_binary air row h_constraints
    have to_lt : ∀ (x : FKB), x = 0 ∨ x = 1 ↔ x < 2 := by clear *-; omega
    simp [to_lt] at selectors branching
    -- Set up assumptions
    simp [bus_row_assumptions] at h_assumptions
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_reg ⟩ := h_assumptions
    -- Main proof
    simp [bus_row_assertions]
    constructor
    -- Program
    simp [bus_row, h_is_real]
    constructor
    -- ALU
    simp [bus_row, Valid_CpuCols.is_branch_instruction]
    split_ands <;> intro h_cond <;> exfalso <;> grind
    constructor
    -- Byte
    simp [bus_row]
    split_ands <;> intro h_cond <;> exfalso <;> grind
    -- Register
    simp [bus_row, h_is_real]
    -- Remove impossible entries
    simp [
      show (air.cols.opcode_selector.imm_b row 0 - 1 = 1) = False by grind,
      show (air.cols.opcode_selector.imm_c row 0 - 1 = 1) = False by grind
    ]
    -- Get Byte bus assumptions
    simp [
      bus_row,
      h_is_real,
      ByteBusEntry.Spec
    ] at asm_byte
    -- Get Register bus assumptions
    simp [
      bus_row,
      h_is_real,
      show (1 - air.cols.opcode_selector.imm_b row 0 = -1) = False by grind,
      show (1 - air.cols.opcode_selector.imm_c row 0 = -1) = False by grind
    ] at asm_reg
    -- Fully simplify
    simp_all

end CpuAir.Spec
