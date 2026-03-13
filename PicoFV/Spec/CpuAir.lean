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

  --
  -- Externals
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_CpuAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuAir.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    -- Process wf-properties
    simp [ bus_row_wf_asm ] at h_wf
    obtain ⟨ h_asm_prog, h_asm_alu, h_asm_byte, h_asm_state, h_asm_mem ⟩ := h_wf
    -- Program
    simp [
      bus_row,
      h_is_real,
      ProgramBusEntry.operand_properties,
      -Vector.getElem_mk,
      -ProgramBusEntry.mk.injEq
    ] at h_asm_prog
    obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_asm_prog
    have h_eq_mult : mult = -1 := by aesop
    subst mult
    have h_opcode_props
      := @ProgramBusEntry.operand_properties_inversion
          instr
          ⟨ -1, data ⟩
          props
          (ProgramBusEntry.deserialise (program_bus_entry air row))
          (by simp [h_eq, h_is_real])
          (by simp [h_is_real]; aesop)
    have h_range
      := @ProgramBusEntry.inversion_opcode_bounds
          instr
          ⟨ -1, data ⟩
          props
          (ProgramBusEntry.deserialise (program_bus_entry air row))
          (by clear h_opcode_props; simp [h_eq, h_is_real])
          (by clear h_opcode_props; simp [h_is_real]; aesop)
    have h_selectors
      := @ProgramBusEntry.inversion_opcode_selectors
          instr
          ⟨ -1, data ⟩
          props
          (ProgramBusEntry.deserialise (program_bus_entry air row))
          (by clear h_opcode_props h_range; simp [h_eq, h_is_real])
          (by clear h_opcode_props h_range; simp [h_is_real]; aesop)
    have h_imm
      := @ProgramBusEntry.ub_imm
          instr
          ⟨ -1, data ⟩
          props
          (ProgramBusEntry.deserialise (program_bus_entry air row))
          (by clear h_opcode_props h_range h_selectors; simp [h_eq, h_is_real])
          (by clear h_opcode_props h_range h_selectors; simp [h_is_real]; aesop)
    simp [program_bus_entry] at h_opcode_props h_range h_selectors h_imm
    clear h_eq h_eq_entry
    obtain ⟨ ub_opcode, opcode_neq_26, opcode_neq_29 ⟩ := h_range
    -- ALU
    simp [bus_row, h_is_real] at h_asm_alu
    obtain ⟨ h_alu_alu, h_alu_branching_addr, h_alu_branch_comp0, h_alu_branch_comp1,
             h_alu_jal, h_alu_jalr, h_alu_auipc ⟩ := h_asm_alu
    clear h_alu_branch_comp0 h_alu_branch_comp1
    -- Byte
    simp [bus_row, h_is_real] at h_asm_byte
    replace h_asm_byte := h_asm_byte.2.2.2.2.2.2
    obtain ⟨ ub_a01, ub_a23, h_asm_byte ⟩ := h_asm_byte; clear h_asm_byte
    simp [ByteBus.Spec] at ub_a01 ub_a23
    obtain ⟨ ub_a0, ub_a1 ⟩ := ub_a01; obtain ⟨ ub_a2, ub_a3 ⟩ := ub_a23
    -- State
    simp [bus_row, h_is_real] at h_asm_state
    obtain ⟨ ub_nonimm_b, u0, ub_nonimm_c, u1, ub_ap ⟩ := h_asm_state; clear u0 u1
    obtain ⟨ ub_ap0, ub_ap1, ub_ap2, ub_ap3 ⟩ := ub_ap
    -- Memory
    clear h_asm_mem
    -- Immediate auxiliaries
    have imm_b_eqs := imm_b_eqs air row h_constraints
    have imm_c_eqs := imm_c_eqs air row h_constraints
    -- Expand goal
    simp [
      bus_row_ext_asrt,
      bus_row,
      h_is_real,
      Valid_CpuCols.is_branch_instruction,
      Valid_CpuCols.is_memory_instruction,
    ]
    repeat rw [Fin.ext_iff (a := air.cols.instruction.opcode row 0)] at h_opcode_props
    repeat rw [Fin.ext_iff (a := air.cols.instruction.opcode row 0)] at h_selectors
    interval_cases eq_opcode : (air.cols.instruction.opcode row 0).val
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 0 := by clear *- eq_opcode; omega
      simp [h_selectors, eq_opcode_KB]
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 1 := by clear *- eq_opcode; omega
      simp [h_selectors, eq_opcode_KB]
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 2 := by clear *- eq_opcode; omega
      simp [h_selectors, eq_opcode_KB]
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 3 := by clear *- eq_opcode; omega
      simp [h_selectors, eq_opcode_KB]
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 4 := by clear *- eq_opcode; omega
      simp [h_selectors, eq_opcode_KB]
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 5 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 6 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 7 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 8 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 9 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 10 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 11 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 12 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 13 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 14 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 15 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 16 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 17 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 18 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 19 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 20 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 21 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 22 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 23 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 24 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 25 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 26 := by clear *- eq_opcode; omega
      clear *- opcode_neq_26; grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 27 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 28 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 29 := by clear *- eq_opcode; omega
      clear *- opcode_neq_29; grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 30 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 31 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 32 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 33 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 34 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 35 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 36 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind
    . have eq_opcode_KB : air.cols.instruction.opcode row 0 = 37 := by clear *- eq_opcode; omega
      simp at h_opcode_props h_selectors ⊢
      simp [h_selectors, eq_opcode_KB] at h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ⊢
      clear *- h_opcode_props h_imm ub_nonimm_b ub_nonimm_c imm_b_eqs imm_c_eqs ub_a0 ub_a1 ub_a2 ub_a3
      grind

  --
  -- Well-formedness
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_CpuAir FKB ExtF)
    (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuAir.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    -- Set up selectors
    have selectors := opcode_selectors_breakdown air row h_is_real h_wf h_constraints
    have branching := branching_binary air row h_constraints
    have to_lt : ∀ (x : FKB), x = 0 ∨ x = 1 ↔ x < 2 := by clear *-; omega
    simp [to_lt] at selectors branching
    -- Set up assumptions
    simp [bus_row_wf_asm] at h_wf
    obtain ⟨ asm_prog, asm_alu, asm_byte, asm_state, asm_mem ⟩ := h_wf
    -- Main proof
    simp [bus_row_wf_asrt]
    constructor
    . -- Program
      simp [bus_row, h_is_real]
    . constructor
      . -- ALU
        simp [bus_row, Valid_CpuCols.is_branch_instruction]
        split_ands <;> intro h_cond <;> exfalso <;> grind
      . constructor
        . -- Byte
          simp [bus_row]
          split_ands <;> intro h_cond <;> exfalso <;> grind
        . constructor
          . -- Register
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
              ByteBus.Spec
            ] at asm_byte
            -- Get Register bus assumptions
            simp [
              bus_row,
              h_is_real,
              show (1 - air.cols.opcode_selector.imm_b row 0 = -1) = False by grind,
              show (1 - air.cols.opcode_selector.imm_c row 0 = -1) = False by grind
            ] at asm_state
            -- Fully simplify
            simp_all
          . -- Memory
            simp [bus_row, h_is_real, Valid_CpuCols.is_memory_instruction]
            intro h; exfalso; grind

end CpuAir.Spec
