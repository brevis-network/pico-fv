import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.Constraints.CpuChipInterpretations

import PicoFV.RV64IM.RVSail.Opcodes.Opcodes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  attribute [local simp]
    program_bus_entry

  section Auxiliaries

    /-- The chip's `op_a` operand value at `row`, packaged as a `U64w` (4 u16
    limbs). Sugar over `air.cols.op_a_access.access.value_*`. -/
    def op_a_value (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_a_access.access.value_0 row 0,
          air.cols.op_a_access.access.value_1 row 0,
          air.cols.op_a_access.access.value_2 row 0,
          air.cols.op_a_access.access.value_3 row 0 ]

    /-- The chip's `op_b` operand value at `row`, packaged as a `U64w`. -/
    def op_b_value (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_b_access.access.value_0 row 0,
          air.cols.op_b_access.access.value_1 row 0,
          air.cols.op_b_access.access.value_2 row 0,
          air.cols.op_b_access.access.value_3 row 0 ]

    /-- The chip's `op_c` operand value at `row`, packaged as a `U64w`. -/
    def op_c_value (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_c_access.access.value_0 row 0,
          air.cols.op_c_access.access.value_1 row 0,
          air.cols.op_c_access.access.value_2 row 0,
          air.cols.op_c_access.access.value_3 row 0 ]

    /-- CPU bus operations: the chip's bus emissions as a Sail `Operation` list,
    appended with a `.WritePC` capturing the chip's `next_pc` value (3 u16 limbs
    zero-padded into a 64-bit BV). Mirrors RV32's `CPU_bus_operations`
    (CpuAir.lean:2996), with the PC limbs composed for the RV64 64-bit PC type. -/
    def CPU_bus_operations (air : Valid_CpuChip FKB ExtF) (row : ℕ) :=
      RV64IM.bus_operations (deserialise_bus_row (raw_bus_row air row)) ++
      [ .WritePC (U64w.toBV (next_pc air row)) ]

    /-- Program well-formedness assumption (mirrors RV32's
    `pico_CpuAir_control_flow_assumptions`, CpuAir.lean:3023):
    public_values 43 (the low u16 limb of the terminating PC) is 4-byte aligned.
    Since `pc.toNat % 4 = pc_0.val % 4`, this gives `next_pc % 4 = 0` on the
    last real row (where the chip pins `next_pc_0 = public_values 43`). -/
    def pico_CpuChip_control_flow_assumptions
      (air : Valid_CpuChip FKB ExtF)
    :=
      (air.public_values 43).val % 4 = 0

    -- ========================================================================
    -- PC alignment lemmas (mirroring RV32IM/Equivalence/Equivalence.lean:88-194).
    -- ========================================================================

    /-- `pc_0` at `row + 1` is 4-aligned, on a transition row with `is_real = 1`
    at rotation 1. Bridge: rotate `pc_0 row 1 = pc_0 (row + 1) 0`, then apply
    the Program-bus axiom at `row + 1`. -/
    lemma pc_next_row_mod_four_eq_zero
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_transition_row : ¬ (Circuit.isTransitionRow air row = 0))
      (h_is_real : air.cols.is_real row 1 = 1)
      (h_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
    :
      (air.cols.pc_0 row 1).val % 4 = 0
    := by
      replace h_row : (row + 1) ≤ air.last_row := by
        simp [Circuit.isTransitionRow] at h_transition_row
        simp [Circuit.last_row] at h_transition_row
        omega
      rw [is_real_rotation, Nat.mod_eq_of_lt (by omega)] at h_is_real
      rw [pc_0_rotation, Nat.mod_eq_of_lt (b := air.last_row + 1) (by omega)]
      specialize h_axioms (row + 1) (by omega)
      simp [bus_row_axioms, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_axioms
      grind

    /-- `next_pc_0` is 4-aligned on every real row. Three cases:
      * **Last row** (`isTransitionRow = 0`): c181 pins `next_pc_0 = public_values 43`.
      * **Transition + `is_real (row+1) = 0`** (final real row before padding):
        c178 pins `next_pc_0 = public_values 43`.
      * **Transition + `is_real (row+1) = 1`** (internal row): use
        `instruction_breakdown` to dispatch, then for each class show
        `next_pc_0 = pc_0 (row + 1)` (cross-row link) and chain into
        `pc_next_row_mod_four_eq_zero`. -/
    lemma next_pc_mod_four_eq_zero
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (h_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
    :
      (air.cols.next_pc_0 row 0).val % 4 = 0
    := by
      -- Current-row pc_0 % 4 = 0 from Program-bus axiom + is_real = 1.
      have h_pc_0_mod_4 : (air.cols.pc_0 row 0).val % 4 = 0 := by
        have h_ax : bus_row_axioms (bus_row air row) := by grind
        simp [bus_row_axioms, bus_row, deserialise_bus_row, raw_bus_row, h_is_real]
          at h_ax
        grind
      -- u16 bounds on pc / next_pc limbs at this row.
      have h_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (h_constraints row h_row)
      by_cases h_transition : Circuit.isTransitionRow air row = 0
      ----------------------------------------------------------------------
      -- Case 1: Last row (isTransitionRow = 0). c178 pins next_pc_0 = public 43.
      ----------------------------------------------------------------------
      . have h_c178 : constraint_178 air row := by
          have h_cs := h_constraints row h_row
          simp [allHold_simplified] at h_cs
          grind
        simp [Circuit.isTransitionRow] at h_transition
        simp [constraint_178, constraint_and_interaction_simplification,
              Circuit.isLastRow, ← h_transition, h_is_real, sub_eq_zero] at h_c178
        rw [← h_c178]; exact pico_assumptions
      ----------------------------------------------------------------------
      -- Case 2/3: Transition row.
      ----------------------------------------------------------------------
      . by_cases h_is_real_next : air.cols.is_real row 1 = 0
        --------------------------------------------------------------------
        -- Case 2: Final real row (is_real(row+1) = 0). c175 pins next_pc_0 = public 43.
        --------------------------------------------------------------------
        . have h_c175 : constraint_175 air row := by
            have h_cs := h_constraints row h_row
            simp [allHold_simplified] at h_cs
            grind
          have h_trans : Circuit.isTransitionRow air row = 1 := by
            simp [Circuit.isTransitionRow] at h_transition ⊢; grind
          simp [constraint_175, constraint_and_interaction_simplification,
                sub_eq_zero, h_trans, h_is_real, h_is_real_next] at h_c175
          rw [← h_c175]; exact pico_assumptions
        --------------------------------------------------------------------
        -- Case 3: Internal row. Dispatch via instruction_breakdown.
        --------------------------------------------------------------------
        . have h_trans : Circuit.isTransitionRow air row = 1 := by
            simp [Circuit.isTransitionRow] at h_transition ⊢; grind
          have h_row_next : row + 1 ≤ air.last_row := by
            simp [Circuit.isTransitionRow] at h_transition
            simp [Circuit.last_row] at h_transition; omega
          -- Bridge: from `is_real row 1 ≠ 0` and c20 at row+1 (is_real bool),
          -- conclude `is_real row 1 = 1`.
          have h_is_real_next' : air.cols.is_real row 1 = 1 := by
            have h_c20 : constraint_20 air (row + 1) := by
              have h_cs := h_constraints (row + 1) h_row_next
              simp [allHold_simplified] at h_cs; grind
            have h_mod : (row + 1) % (air.last_row + 1) = row + 1 :=
              Nat.mod_eq_of_lt (by omega)
            have h_eq : air.cols.is_real row 1 = air.cols.is_real (row + 1) 0 := by
              rw [is_real_rotation]; simp [h_mod]
            rw [h_eq] at h_is_real_next ⊢
            simp [constraint_20, constraint_and_interaction_simplification,
                  sub_eq_zero] at h_c20
            grind
          -- Cross-row PC alignment: pc_0(row+1) % 4 = 0.
          have h_pc_next_mod_4 : (air.cols.pc_0 row 1).val % 4 = 0 :=
            pc_next_row_mod_four_eq_zero air row h_row h_transition h_is_real_next' (by grind)
          have h_breakdown :=
            instruction_breakdown air row h_is_real (by grind) (h_constraints row h_row)
          rcases h_breakdown with h_seq | h_branch | h_jal | h_jalr | h_ecall
          ------------------------------------------------------------------
          -- 3a. is_sequential_instr = 1 (sequential class): c166 + pc % 4 = 0.
          ------------------------------------------------------------------
          . have h_c166 : constraint_166 air row := by
              have h_cs := h_constraints row h_row
              simp [allHold_simplified] at h_cs; grind
            have h_ra := is_real_active_constraints air row h_is_real (by grind)
                          (h_constraints row h_row)
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
                    h_cb_b0, _, _, _, _, _, _, _, _, _⟩ := h_ra
            simp [constraint_166, constraint_and_interaction_simplification,
                  h_is_real, h_seq, sub_eq_zero] at h_c166
            -- h_c166 : pc_0 + 4 = next_pc_0 + pc_carry_b_0 * 65536 (in FKB).
            -- With pc_0.val < 65536, pc_carry_b_0 ∈ {0,1}, derive Nat eq and conclude.
            rcases h_cb_b0 with h_cb | h_cb <;> simp [h_cb] at h_c166 <;> grind
          ------------------------------------------------------------------
          -- 3b. branch_sum = 1: split on branching ∈ {0, 1}.
          ------------------------------------------------------------------
          . have h_ib := is_branching_active_constraints air row h_row h_is_real (by grind) h_branch
                          (h_constraints row h_row)
            obtain ⟨_, _, _, _, h_branching_bool, _, _, h_cross, _h_not_br⟩ := h_ib
            rcases h_branching_bool with h_br_0 | h_br_1
            -- branching = 0: c37 → next_pc_0 = pc_0 + 4 - pc_carry_b_0 * 65536
            . -- branching = 0 ⟹ not_branching = 1 (c42 mutex)
              have h_c42 : constraint_42 air row := by
                have h_cs := h_constraints row h_row
                simp [allHold_simplified] at h_cs; grind
              simp [constraint_42, constraint_and_interaction_simplification,
                    h_branch, h_br_0, sub_eq_zero] at h_c42
              -- h_c42 : not_branching = 1
              have h_c37 : constraint_37 air row := by
                have h_cs := h_constraints row h_row
                simp [allHold_simplified] at h_cs; grind
              have h_ra := is_real_active_constraints air row h_is_real (by grind)
                            (h_constraints row h_row)
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
                      h_cb_b0, _, _, _, _, _, _, _, _, _⟩ := h_ra
              simp [constraint_37, constraint_and_interaction_simplification,
                    h_is_real, h_c42, sub_eq_zero] at h_c37
              rcases h_cb_b0 with h_cb | h_cb <;> simp [h_cb] at h_c37 <;> grind
            -- branching = 1: c28 → next_pc_0 = pc_0(row+1)
            . have h_c28 : constraint_28 air row := by
                have h_cs := h_constraints row h_row
                simp [allHold_simplified] at h_cs; grind
              simp [constraint_28, constraint_and_interaction_simplification,
                    h_trans, h_is_real_next', h_br_1, sub_eq_zero] at h_c28
              rw [h_c28]; exact h_pc_next_mod_4
          ------------------------------------------------------------------
          -- 3c. is_jal = 1: c67 → next_pc_0 = pc_0(row+1). Need is_jalr = 0
          -- to make the `is_jal + is_jalr` factor reduce cleanly.
          ------------------------------------------------------------------
          . have h_excl := selector_exclusivity air row h_is_real (by grind)
            have h_op := (is_jal_eq_one_iff air row h_is_real (by grind)).mp h_jal
            simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
            have h_no_jalr : air.cols.opcode_selector.is_jalr row 0 = 0 := by grind
            have h_c67 : constraint_67 air row := by
              have h_cs := h_constraints row h_row
              simp [allHold_simplified] at h_cs; grind
            simp [constraint_67, constraint_and_interaction_simplification,
                  h_trans, h_is_real_next', h_jal, h_no_jalr, sub_eq_zero] at h_c67
            rw [h_c67]; exact h_pc_next_mod_4
          ------------------------------------------------------------------
          -- 3d. is_jalr = 1: symmetric — need is_jal = 0.
          ------------------------------------------------------------------
          . have h_excl := selector_exclusivity air row h_is_real (by grind)
            have h_op := (is_jalr_eq_one_iff air row h_is_real (by grind)).mp h_jalr
            simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
            have h_no_jal : air.cols.opcode_selector.is_jal row 0 = 0 := by grind
            have h_c67 : constraint_67 air row := by
              have h_cs := h_constraints row h_row
              simp [allHold_simplified] at h_cs; grind
            simp [constraint_67, constraint_and_interaction_simplification,
                  h_trans, h_is_real_next', h_jalr, h_no_jal, sub_eq_zero] at h_c67
            rw [h_c67]; exact h_pc_next_mod_4
          ------------------------------------------------------------------
          -- 3e. ECALL halt (specific_9 * is_ecall = 1): c145 → next_pc_0 = 0.
          ------------------------------------------------------------------
          . have h_c145 : constraint_145 air row := by
              have h_cs := h_constraints row h_row
              simp [allHold_simplified] at h_cs; grind
            simp [constraint_145, constraint_and_interaction_simplification,
                  h_ecall] at h_c145
            rw [h_c145]; simp

  end Auxiliaries

  section RTYPE

    -- ========================================================================
    -- R-type ALU operand setup. Packages the Program-bus inversion + chip-side
    -- column-equation extraction common to every RTYPE ALU opcode (ADD, SUB,
    -- AND, OR, XOR, SLL, SRL, SRA, SLT, SLTU). Caller supplies `op : rop` +
    -- `h_opcode : opcode = opcode_of_rop op` + `h_imm_c : imm_c = 0`; lemma
    -- returns ∃ rs2 rs1 rd, the 16 column equations (op_a/b/c limbs, x0 flag,
    -- imm_b), the 23-selector pattern (`is_alu = 1` and all others 0), and the
    -- u5 register-id bounds on op_a/b/c_0.
    -- ========================================================================

    /-- Operand-setup lemma for the RTYPE ALU class. Mirrors the
    Program-bus inversion + column-equation extraction in
    `equivalence_ADD` (lines 138-173 of this file); usable verbatim by
    every per-opcode RTYPE equivalence theorem. -/
    lemma rtype_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (op : rop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_rop op)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
    :
      ∃ (rs2 rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = Transpiler.reg_to_KB rs2 ∧
        air.cols.instruction.op_c_1 row 0 = 0 ∧
        air.cols.instruction.op_c_2 row 0 = 0 ∧
        air.cols.instruction.op_c_3 row 0 = 0 ∧
        air.cols.instruction.op_a_is_x0 row 0 =
          (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32 ∧
        (air.cols.instruction.op_c_0 row 0).val < 32
    := by
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      cases op <;>
        ( simp [Transpiler.opcode_of_rop] at h_opcode
          simp [h_opcode, h_imm_c] at h_opcode_props
          obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ rs2, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data, Transpiler.opcode_of_rop] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0, eq_imm_b,
                  h_selectors,
                  h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ )

    -- ========================================================================
    -- R-type ALU bus setup. Packages the post-operand-setup chunk that
    -- extracts the ALU-bus consumer assumption + the four Sail register/PC
    -- read assumptions from `h_bus_hypotheses`. Output (in order):
    --   1. `h_wf_alu` — the ALU-bus `wf_assume` conjunction (used to extract
    --      `a = execute_RTYPE_pure b c op` from the chip's ALU lookup).
    --   2. `h_pc` — the Sail PC read; PC value is in raw limb-sum BV form.
    --   3. `h_reg1` — the rs1 (op_b) register read; value as `U64w.toBV` of
    --      `op_b_value` (4-limb form).
    --   4. `h_reg2` — the rs2 (op_c) register read; value as `U64w.toBV` of
    --      `op_c_value` (4-limb form).
    --   5. `h_reg0` — the rd (op_a previous) register read; value as
    --      `U64w.toBV` of the 4-limb `prev_value_*` form.
    -- All five hypotheses are stated in the forms that drop straight into
    -- the per-opcode equivalence proof (post-rtype_operand_setup, used in
    -- Phases 4-6 of the original equivalence_ADD proof).
    -- ========================================================================

    /-- Bus-side setup lemma for the RTYPE ALU class. Mirrors the post-setup
    chunk of `equivalence_ADD` (lines 287-294 in the original proof). The
    23-selector pattern, register-id bounds, opcode equality and imm_b/imm_c
    flags should be supplied as obtained from `rtype_operand_setup`. -/
    lemma rtype_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (op : rop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_rop op)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (eq_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
      (h_reg_rs2 : (air.cols.instruction.op_c_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_c_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_c_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, eq_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1, h_reg_rs2
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      show _ ∧ _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . simp only [op_c_value]; exact h_reg2
      . exact h_reg0

    -- ==========================================================================
    -- Per-opcode RTYPE equivalence theorems.
    -- ==========================================================================

    /-- Equivalence for ADD (opcode 0, R-type ALU `.ADD`).
    Pattern: under the chip's row constraints + bus assumptions + program
    well-formedness + a state pre-condition (`h_bus_hypotheses`), the chip's
    emitted bus operations, applied to a Sail `state`, produce the same
    post-state as one Sail step of `instruction.RTYPE (rs2, rs1, rd, .ADD)`. -/
    theorem equivalence_ADD
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses to the current row + pull
      -- common chip-side facts (sequential active constraints, pc/next_pc u16 bounds).
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      -- Phase 2: RTYPE operand extraction via the class-level setup lemma.
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .ADD (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      -- Phase 3: package the ALU-bus + PC/reg read assumptions via rtype_bus_setup.
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .ADD
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      -- Phase 4: bridge Sail RTYPE → spec_ADD via execute_ADD_equiv.
      rw [
        OpcodeSpec.RV64.execute_ADD_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      -- Phase 5: state equality.
      . simp [
          OpcodeSpec.RV64.spec_ADD,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      -- Phase 6: discharge execute_ADD_equiv hypothesis side-goal.
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SUB (opcode 1, R-type ALU `.SUB`). -/
    theorem equivalence_SUB
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 1 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SUB (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SUB
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SUB_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SUB,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for XOR (opcode 2, R-type ALU `.XOR`). -/
    theorem equivalence_XOR
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 2 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.XOR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .XOR (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .XOR
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_XOR_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_XOR,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for OR (opcode 3, R-type ALU `.OR`). -/
    theorem equivalence_OR
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 3 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.OR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .OR (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .OR
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_OR_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_OR,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for AND (opcode 4, R-type ALU `.AND`). -/
    theorem equivalence_AND
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 4 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.AND)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .AND (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .AND
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_AND_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_AND,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLL (opcode 5, R-type ALU `.SLL`). -/
    theorem equivalence_SLL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 5 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SLL (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLL
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLL_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRL (opcode 6, R-type ALU `.SRL`). -/
    theorem equivalence_SRL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 6 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SRL (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SRL
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SRL_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRA (opcode 7, R-type ALU `.SRA`). -/
    theorem equivalence_SRA
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 7 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRA)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SRA (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SRA
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SRA_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRA,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLT (opcode 8, R-type ALU `.SLT`). -/
    theorem equivalence_SLT
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 8 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SLT (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLT
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLT_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLT,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLTU (opcode 9, R-type ALU `.SLTU`). -/
    theorem equivalence_SLTU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 9 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SLTU (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLTU
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLTU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLTU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end RTYPE

  section RTYPEW

    -- ========================================================================
    -- RTYPEW (32-bit word R-type) — RV64-only ALU class spanning 5 opcodes:
    --   ADDW = 40, SUBW = 41, SLLW = 42, SRLW = 43, SRAW = 44.
    -- Bus layout matches RTYPE (3 register operands, imm_b = 0, imm_c = 0,
    -- is_alu = 1). The chip's ALUBus.Spec arms 40..44 apply `setWidth 32`
    -- to both operands and produce `sign_extend 64 (...)`. The inversion at
    -- opcodes 40/42/43/44 is a 2-way disjunction with ADDIW / SHIFTIWOP
    -- (disambiguated by imm_c), so `h_imm_c = 0` is required to collapse it.
    -- ========================================================================

    inductive RtypewVariant where
      | ADDW | SUBW | SLLW | SRLW | SRAW
      deriving DecidableEq, Repr

    def opcode_of_RtypewVariant : RtypewVariant → FKB
      | .ADDW => 40
      | .SUBW => 41
      | .SLLW => 42
      | .SRLW => 43
      | .SRAW => 44

    /-- Operand-setup lemma for the RTYPEW class. Mirrors `mul_operand_setup`. -/
    lemma rtypew_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (var : RtypewVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_RtypewVariant var)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
    :
      ∃ (rs2 rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = Transpiler.reg_to_KB rs2 ∧
        air.cols.instruction.op_c_1 row 0 = 0 ∧
        air.cols.instruction.op_c_2 row 0 = 0 ∧
        air.cols.instruction.op_c_3 row 0 = 0 ∧
        air.cols.instruction.op_a_is_x0 row 0 =
          (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32 ∧
        (air.cols.instruction.op_c_0 row 0).val < 32
    := by
      replace h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      cases var <;>
        ( simp [opcode_of_RtypewVariant] at h_opcode
          simp [h_opcode, h_imm_c] at h_opcode_props
          obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ rs2, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, Transpiler.opcode_of_ropw, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0,
                  eq_imm_b,
                  h_selectors,
                  h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ )

    /-- Bus-side setup lemma for the RTYPEW class. -/
    lemma rtypew_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (var : RtypewVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_RtypewVariant var)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd  : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
      (h_reg_rs2 : (air.cols.instruction.op_c_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_c_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_c_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1, h_reg_rs2
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses; simp at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses; simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      show _ ∧ _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . simp only [op_c_value]; exact h_reg2
      . exact h_reg0

    /-- Equivalence for ADDW (opcode 40, RV64-only word ADD). -/
    theorem equivalence_ADDW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 40 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.ADDW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := rtypew_operand_setup air row h_row h_is_real (by grind) .ADDW
             (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtypew_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .ADDW
          (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) eq_imm_b h_opcode.2
          h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_ADDW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_ADDW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_opcode.2, h_selectors, eq_imm_b,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SUBW (opcode 41, RV64-only word SUB). -/
    theorem equivalence_SUBW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 41 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SUBW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := rtypew_operand_setup air row h_row h_is_real (by grind) .SUBW
             (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtypew_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SUBW
          (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) eq_imm_b h_opcode.2
          h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SUBW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SUBW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_opcode.2, h_selectors, eq_imm_b,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLLW (opcode 42, RV64-only word logical shift left). -/
    theorem equivalence_SLLW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 42 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := rtypew_operand_setup air row h_row h_is_real (by grind) .SLLW
             (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtypew_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SLLW
          (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) eq_imm_b h_opcode.2
          h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLLW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLLW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_opcode.2, h_selectors, eq_imm_b,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRLW (opcode 43, RV64-only word logical shift right). -/
    theorem equivalence_SRLW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 43 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SRLW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := rtypew_operand_setup air row h_row h_is_real (by grind) .SRLW
             (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtypew_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SRLW
          (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) eq_imm_b h_opcode.2
          h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SRLW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRLW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_opcode.2, h_selectors, eq_imm_b,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRAW (opcode 44, RV64-only word arithmetic shift right). -/
    theorem equivalence_SRAW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 44 ∧
                  air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPEW (rs2, rs1, rd, ropw.SRAW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := rtypew_operand_setup air row h_row h_is_real (by grind) .SRAW
             (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtypew_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SRAW
          (by simp [opcode_of_RtypewVariant]; exact h_opcode.1) eq_imm_b h_opcode.2
          h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SRAW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRAW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_opcode.2, h_selectors, eq_imm_b,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end RTYPEW

  section ITYPE

    -- ========================================================================
    -- ITYPE operand setup. Like `rtype_operand_setup` but for the ITYPE branch
    -- of `operand_properties_inversion`. Caller supplies `op : iop` +
    -- `h_opcode : opcode = opcode_of_iop op` + `h_imm_b : imm_b = 0` +
    -- `h_imm_c : imm_c = 1`. `h_imm_b` is needed only for opcode 0 (where
    -- the inversion has a 3-way disjunction including UTYPE LUI); for other
    -- ITYPE opcodes it's redundant but kept for uniformity.
    -- Output: ∃ (imm : BitVec 12) (rs1 rd : regidx), the 12 op_a/b column
    -- equations (with rs1, rd), 4 op_c column equations binding op_c_i to
    -- `(imm_to_KB imm true)[i]`, op_a_is_x0 + imm_c flags, selector pattern,
    -- and 2 register-id bounds (rd, rs1).
    -- ========================================================================

    /-- Operand-setup lemma for the ITYPE ALU class (6 opcodes: ADDI/XORI/
    ORI/ANDI/SLTI/SLTIU). Mirrors `rtype_operand_setup` from the RTYPE
    section. -/
    lemma itype_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (op : iop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_iop op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 12) (rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = (Transpiler.imm_to_KB imm true)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.imm_to_KB imm true)[1] ∧
        air.cols.instruction.op_c_2 row 0 = (Transpiler.imm_to_KB imm true)[2] ∧
        air.cols.instruction.op_c_3 row 0 = (Transpiler.imm_to_KB imm true)[3] ∧
        air.cols.instruction.op_a_is_x0 row 0 =
          (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32
    := by
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      cases op <;>
        ( simp [Transpiler.opcode_of_iop] at h_opcode
          simp [h_opcode, h_imm_b, h_imm_c] at h_opcode_props
          obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ imm, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data, Transpiler.opcode_of_iop] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0,
                  h_selectors,
                  h_reg_rd, h_reg_rs1 ⟩ )

    -- ========================================================================
    -- ITYPE bus setup. Mirrors `rtype_bus_setup` but for the ITYPE class.
    -- Differences: no `op_c` register read (since `imm_c = 1` filters the op_c
    -- State-bus entries out via `bus_operations`'s `filterMap` on multiplicity);
    -- one fewer reg-bound input (`h_reg_rs2` absent); 4-tuple output (no
    -- `h_reg2`).
    -- ========================================================================

    /-- Bus-side setup lemma for the ITYPE ALU class. -/
    lemma itype_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (op : iop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_iop op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      show _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . exact h_reg0

    /-- Equivalence for ADDI (opcode 0, I-type ALU `.ADDI`). `imm` is reconstructed
    from the chip's `op_c` columns (low 12 bits of the sign-extended 64-bit form). -/
    theorem equivalence_ADDI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ADDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses + sequential active constraints + pc bounds.
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      -- Phase 2: ITYPE operand extraction.
      obtain ⟨ imm', rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0,
              h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        itype_operand_setup air row h_is_real (by grind) .ADDI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      -- Bridge: the let-bound imm equals the existential imm'. The chip stores
      -- op_c via `op_c_access.access.value_*` (register-access form), while
      -- itype_operand_setup's column equations are on `instruction.op_c_*`
      -- (Program-bus form). `imm_c_eq_1_constraints` (c4-c7) bridges these
      -- two: under `imm_c = 1`, `op_c_access.access.value_i = instruction.op_c_i`.
      -- Then `instruction.op_c_i = (imm_to_KB imm' true)[i]` (from eq_c0..eq_c3)
      -- and `imm_to_KB_BV_sgn` collapses the 4-limb form to `signExtend 64 imm'`.
      -- We state h_op_c_bv in the unrolled #v[...] form (matching what simp
      -- produces inside h_spec) so that `rw [h_op_c_bv] at h_spec` fires.
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      -- Phase 3: ITYPE bus setup.
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        itype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .ADDI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      extract_lets reg0 reg1 imm
      -- Phase 4: rewrite the let-imm to imm' and apply execute_ADDI_equiv.
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_ADDI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      -- Phase 5: state equality.
      . simp [
          OpcodeSpec.RV64.spec_ADDI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        -- The op_a write: we need to show op_a value = op_b + signExtend 64 imm' (per ADDI spec)
        -- This comes from the ALU bus spec at opcode 0 (ADD), which the chip emits for ITYPE too.
        -- Wait — the chip emits an ALU bus lookup for is_alu = 1 (which is set for both RTYPE and ITYPE).
        -- The lookup is `[4, opcode, op_a, op_b, op_c]` at opcode 0 → spec is `op_a = op_b + op_c`.
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        -- Fold the immediate into h_spec: the simp above turned the c-operand
        -- into `U64w.toBV #v[(imm_to_KB imm' true)[i]]` (via eq_c*), and
        -- `imm_to_KB_BV_sgn` collapses that to `signExtend 64 imm'`. After
        -- this rewrite, h_spec matches the shape spec_ADDI expects.
        rw [Transpiler.imm_to_KB_BV_sgn imm'] at h_spec
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      -- Phase 6: discharge execute_ADDI_equiv hypothesis side-goal (PC + rs1 reads).
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for XORI (opcode 2, I-type ALU `.XORI`). Note: opcodes 2/3/4
    use the ALU `operand_range` path in `ALUBus.Spec`, so the h_wf_alu
    destructure picks up an extra `_h_operands` slot. -/
    theorem equivalence_XORI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 2 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.XORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ imm', rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0,
              h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        itype_operand_setup air row h_is_real (by grind) .XORI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        itype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .XORI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_XORI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_XORI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_BV_sgn imm'] at h_spec
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for ORI (opcode 3, I-type ALU `.ORI`). -/
    theorem equivalence_ORI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 3 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ORI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ imm', rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0,
              h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        itype_operand_setup air row h_is_real (by grind) .ORI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        itype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .ORI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_ORI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_ORI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_BV_sgn imm'] at h_spec
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for ANDI (opcode 4, I-type ALU `.ANDI`). -/
    theorem equivalence_ANDI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 4 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.ANDI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ imm', rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0,
              h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        itype_operand_setup air row h_is_real (by grind) .ANDI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        itype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .ANDI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_ANDI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_ANDI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_BV_sgn imm'] at h_spec
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLTI (opcode 8, I-type ALU `.SLTI`). -/
    theorem equivalence_SLTI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 8 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ imm', rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0,
              h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        itype_operand_setup air row h_is_real (by grind) .SLTI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        itype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLTI
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SLTI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLTI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_Int_sgn imm'] at h_spec
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLTIU (opcode 9, I-type ALU `.SLTIU`). -/
    theorem equivalence_SLTIU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 9 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ITYPE (imm, rs1, rd, iop.SLTIU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ imm', rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0,
              h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        itype_operand_setup air row h_is_real (by grind) .SLTIU
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        itype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLTIU
          (by simp [Transpiler.opcode_of_iop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SLTIU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLTIU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_Nat_sgn imm'] at h_spec
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end ITYPE

  section ADDIW

    -- ========================================================================
    -- ADDIW — RV64-only sign-extending 32-bit ADD-immediate, opcode 40 with
    -- `imm_c = 1`. Singleton class (no enum). Shares the chip-side bus shape
    -- with ITYPE (1 reg read, imm_b = 0, imm_c = 1, is_alu = 1), and shares
    -- the ALUBus.Spec arm 40 with RTYPEW.ADDW — disambiguated by imm_c at
    -- the operand_properties_inversion level.
    -- ========================================================================

    /-- Equivalence for ADDIW (opcode 40, `instruction.ADDIW`). `imm` is
    reconstructed from the chip's `op_c` columns (low 12 bits of the sign-
    extended 64-bit form). The close needs a `(b.setWidth 32) +
    (c.setWidth 32) = (b + c).setWidth 32` bridge between the chip's ALU
    output and `spec_ADDIW`'s `setWidth 32 (r1 + signExtend 64 imm)` form;
    we discharge it inside the folded `h_spec'`. -/
    theorem equivalence_ADDIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 40 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ADDIW (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode.1, h_opcode.2.2] at h_opcode_props
      obtain ⟨ imm', rs1, rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      simp [h_eq_data] at h_eq_entry
      simp [h_props, Transpiler.is_register] at h_eq_props
      obtain ⟨ _eq_opcode,
               eq_a0, eq_a1, eq_a2, eq_a3,
               eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
               _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
      simp [← eq_a0, ← eq_b0] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      simp [Fin.lt_def] at h_reg_rd h_reg_rs1
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      have h_all_wf' : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf'
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf'
      have h_bus :
        Sail.readReg Register.PC state =
          EStateM.Result.ok
            (BitVec.ofNatLT (w := 64)
              (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
               4294967296 * ↑(air.cols.pc_2 row 0))
              (by
                have := (air.cols.pc_0 row 0).isLt
                have := (air.cols.pc_1 row 0).isLt
                have := (air.cols.pc_2 row 0).isLt
                omega))
            state ∧
        read_xreg
            (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
            state =
          EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
        read_xreg
            (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
            state =
          EStateM.Result.ok
            (U64w.toBV
              #v[ air.cols.op_a_access.prev_value_0 row 0,
                  air.cols.op_a_access.prev_value_1 row 0,
                  air.cols.op_a_access.prev_value_2 row 0,
                  air.cols.op_a_access.prev_value_3 row 0 ])
            state := by
        simp [
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ] at h_bus_hypotheses
        rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
        simp at h_bus_hypotheses
        obtain ⟨ h_pc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
        simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
        refine ⟨ h_pc, ?_, h_reg0 ⟩
        simp only [op_b_value]; exact h_reg1
      obtain ⟨ h_pc, h_reg1, h_reg0 ⟩ := h_bus
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_ADDIW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_ADDIW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.immw_to_KB_BV_sgn imm'] at h_spec
        -- Fold the chip's `sign_extend 64 (b32 + c32)` form into spec_ADDIW's
        -- `signExtend 64 (setWidth 32 (b + signExtend 64 imm'))` form by
        -- exploiting `b32 + c32 = (b + c).setWidth 32` for c = signExtend 64 imm'.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = BitVec.signExtend 64
                (BitVec.setWidth 32
                  (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm')) := by
          rw [h_spec]; simp [op_b_value]; clear *-; congr
          simp [← BitVec.toNat_inj, U32w.toNat, U64w.toNat,
                BitVec.toNat_signExtend, BitVec.msb_eq_decide]
          split_ifs with h_msb <;> omega
        rw [← h_spec']; simp [BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end ADDIW

  section SHIFTIOP

    -- ========================================================================
    -- SHIFTIOP operand setup. Like `itype_operand_setup` but for the SHIFTIOP
    -- branch of `operand_properties_inversion`. Caller supplies `op : sop` +
    -- `h_opcode : opcode = opcode_of_sop op` + `h_imm_b : imm_b = 0` +
    -- `h_imm_c : imm_c = 1`. `h_imm_b` is not strictly needed for the inversion
    -- (opcodes 5/6/7 only have a 2-way disjunction: RTYPE vs SHIFTIOP), but it
    -- is required by `shiftiop_bus_setup` so we propagate it through here too.
    -- Output: ∃ (imm : BitVec 6) (rs1 rd : regidx), the 12 op_a/b column
    -- equations (with rs1, rd), 4 op_c column equations binding op_c_i to
    -- `(imm_to_KB imm false)[i]` (UNSIGNED zero-extend, unlike ITYPE which
    -- sign-extends), op_a_is_x0 flag, selector pattern, and 2 register-id
    -- bounds (rd, rs1).
    -- ========================================================================

    /-- Operand-setup lemma for the SHIFTIOP class (3 opcodes: SLLI/SRLI/
    SRAI). Mirrors `itype_operand_setup` from the ITYPE section. -/
    lemma shiftiop_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (op : sop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_sop op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 6) (rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = (Transpiler.imm_to_KB imm false)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.imm_to_KB imm false)[1] ∧
        air.cols.instruction.op_c_2 row 0 = (Transpiler.imm_to_KB imm false)[2] ∧
        air.cols.instruction.op_c_3 row 0 = (Transpiler.imm_to_KB imm false)[3] ∧
        air.cols.instruction.op_a_is_x0 row 0 = (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      replace h_all_wf := h_all_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_all_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_all_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      cases op <;>
        ( simp [Transpiler.opcode_of_sop] at h_opcode
          simp [h_opcode, h_imm_b, h_imm_c] at h_opcode_props
          obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ imm, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data, Transpiler.opcode_of_sop] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0,
                  h_selectors,
                  h_reg_rd, h_reg_rs1 ⟩ )

    -- ========================================================================
    -- SHIFTIOP bus setup. Identical in shape to `itype_bus_setup` since the
    -- chip-side bus emission for SHIFTIOP and ITYPE is the same: `imm_c = 1`
    -- filters the op_c State-bus entry, and the op_a/op_b reads use the same
    -- shape as for ITYPE. The only opcode-dependent piece is `h_opcode`,
    -- which we keep parameterised over `op : sop`.
    -- ========================================================================

    /-- Bus-side setup lemma for the SHIFTIOP class. -/
    lemma shiftiop_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (op : sop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_sop op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      show _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . exact h_reg0

    /-- Equivalence for SLLI (opcode 5, SHIFTIOP `.SLLI`). `imm` is reconstructed
    from the chip's `op_c` columns (low 6 bits of the zero-extended 64-bit form). -/
    theorem equivalence_SLLI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 5 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (U64w.toBV (op_c_value air row)).setWidth 6
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SLLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, h_selectors, h_reg_rd, h_reg_rs1 ⟩
        := shiftiop_operand_setup air row h_row h_is_real (by grind) .SLLI
          (by simp [Transpiler.opcode_of_sop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        shiftiop_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SLLI
          (by simp [Transpiler.opcode_of_sop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.zeroExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_usgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 6 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SLLI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLLI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_Nat_usgn imm'] at h_spec
        -- Fold the chip's shift form (`Sail.shift_bits_left b (extractLsb (zeroExtend 64 imm') 5 0)`)
        -- into the Sail-spec form (`b <<< imm'.toNat`) so that `simp [← h_spec', …]`
        -- closes the rd_val side without any `congr 1` step.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = U64w.toBV (op_b_value air row) <<< imm'.toNat := by
          simp [h_spec, op_b_value]
          suffices h_imm : imm'.toNat % 64 = imm'.toNat
          . simp [h_imm]
          . simp [← h_imm_eq]
        simp [h_spec', BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        simp [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRLI (opcode 6, SHIFTIOP `.SRLI`). -/
    theorem equivalence_SRLI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 6 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (U64w.toBV (op_c_value air row)).setWidth 6
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRLI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, h_selectors, h_reg_rd, h_reg_rs1 ⟩
        := shiftiop_operand_setup air row h_row h_is_real (by grind) .SRLI
          (by simp [Transpiler.opcode_of_sop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        shiftiop_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SRLI
          (by simp [Transpiler.opcode_of_sop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.zeroExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_usgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 6 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SRLI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRLI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_Nat_usgn imm'] at h_spec
        -- Fold the chip's shift form (`Sail.shift_bits_left b (extractLsb (zeroExtend 64 imm') 5 0)`)
        -- into the Sail-spec form (`b <<< imm'.toNat`) so that `simp [← h_spec', …]`
        -- closes the rd_val side without any `congr 1` step.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = U64w.toBV (op_b_value air row) >>> imm'.toNat := by
          simp [h_spec, op_b_value]
          suffices h_imm : imm'.toNat % 64 = imm'.toNat
          . simp [h_imm]
          . simp [← h_imm_eq]
        simp [h_spec', BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        simp [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRAI (opcode 7, SHIFTIOP `.SRAI`). Note Sail spec uses
    `BitVec.sshiftRight` (arithmetic shift); chip computes the same via
    `execute_RTYPE_pure ... .SRA = BitVec.sshiftRight b (extractLsb c 5 0).toNat`. -/
    theorem equivalence_SRAI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 7 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 6 := (U64w.toBV (op_c_value air row)).setWidth 6
      execute_instruction (instruction.SHIFTIOP (imm, rs1, rd, sop.SRAI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, h_selectors, h_reg_rd, h_reg_rs1 ⟩
        := shiftiop_operand_setup air row h_row h_is_real (by grind) .SRAI
          (by simp [Transpiler.opcode_of_sop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        shiftiop_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SRAI
          (by simp [Transpiler.opcode_of_sop]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.zeroExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_usgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 6 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SRAI_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRAI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.imm_to_KB_Nat_usgn imm'] at h_spec
        -- Fold the chip's shift form (`Sail.shift_bits_left b (extractLsb (zeroExtend 64 imm') 5 0)`)
        -- into the Sail-spec form (`b <<< imm'.toNat`) so that `simp [← h_spec', …]`
        -- closes the rd_val side without any `congr 1` step.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = (U64w.toBV (op_b_value air row)).sshiftRight (imm'.toNat) := by
          simp [h_spec, op_b_value]
          suffices h_imm : imm'.toNat % 64 = imm'.toNat
          . simp [h_imm]
          . simp [← h_imm_eq]
        simp [h_spec', BitVec.ofNatLT_eq_ofNat, op_b_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        simp [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end SHIFTIOP

  section SHIFTIWOP

    -- ========================================================================
    -- SHIFTIWOP — RV64-only 32-bit-word shift-immediate, 3 opcodes:
    --   SLLIW = 42, SRLIW = 43, SRAIW = 44.
    -- 5-bit shift amount (vs SHIFTIOP's 6-bit on RV64), zero-extended. Bus
    -- shape mirrors SHIFTIOP / ITYPE (1 reg read, imm_b = 0, imm_c = 1,
    -- is_alu = 1). Each opcode's inversion is a 2-way disjunction with
    -- RTYPEW.{SLLW,SRLW,SRAW} (disambiguated by imm_c) — `h_imm_c = 1`
    -- collapses it.
    -- ========================================================================

    inductive ShiftiwopVariant where
      | SLLIW | SRLIW | SRAIW
      deriving DecidableEq, Repr

    def opcode_of_ShiftiwopVariant : ShiftiwopVariant → FKB
      | .SLLIW => 42
      | .SRLIW => 43
      | .SRAIW => 44

    /-- Operand-setup lemma for the SHIFTIWOP class. Mirrors `shiftiop_operand_setup`. -/
    lemma shiftiwop_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (var : ShiftiwopVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_ShiftiwopVariant var)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ (imm : BitVec 5) (rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = (Transpiler.imm_to_KB imm false)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.imm_to_KB imm false)[1] ∧
        air.cols.instruction.op_c_2 row 0 = (Transpiler.imm_to_KB imm false)[2] ∧
        air.cols.instruction.op_c_3 row 0 = (Transpiler.imm_to_KB imm false)[3] ∧
        air.cols.instruction.op_a_is_x0 row 0 =
          (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32
    := by
      replace h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      cases var <;>
        ( simp [opcode_of_ShiftiwopVariant] at h_opcode
          simp [h_opcode, h_imm_b, h_imm_c] at h_opcode_props
          obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ imm, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, Transpiler.opcode_of_sopw, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0,
                  h_selectors,
                  h_reg_rd, h_reg_rs1 ⟩ )

    /-- Bus-side setup lemma for the SHIFTIWOP class. -/
    lemma shiftiwop_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (var : ShiftiwopVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_ShiftiwopVariant var)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      show _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . exact h_reg0

    /-- Equivalence for SLLIW (opcode 42, RV64-only 32-bit logical shift-left
    immediate). 5-bit shamt, zero-extended into the chip's `op_c`. -/
    theorem equivalence_SLLIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 42 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (U64w.toBV (op_c_value air row)).setWidth 5
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SLLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, h_selectors, h_reg_rd, h_reg_rs1 ⟩
        := shiftiwop_operand_setup air row h_row h_is_real (by grind) .SLLIW
             (by simp [opcode_of_ShiftiwopVariant]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        shiftiwop_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SLLIW
          (by simp [opcode_of_ShiftiwopVariant]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.zeroExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_usgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 5 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SLLIW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLLIW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.immw_to_KB_Nat_usgn imm'] at h_spec
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = BitVec.signExtend 64
                (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.op_b_access.access.value_0 row 0),
                              BitVec.ofNat 16 ↑(air.cols.op_b_access.access.value_1 row 0)] <<< imm'.toNat) := by
          rw [h_spec]; simp; rw [Nat.mod_eq_of_lt (by grind)]
        simp [op_b_value]; rw [← h_spec']; simp [BitVec.ofNatLT_eq_ofNat]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRLIW (opcode 43, RV64-only 32-bit logical shift-right
    immediate). -/
    theorem equivalence_SRLIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 43 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (U64w.toBV (op_c_value air row)).setWidth 5
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRLIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, h_selectors, h_reg_rd, h_reg_rs1 ⟩
        := shiftiwop_operand_setup air row h_row h_is_real (by grind) .SRLIW
             (by simp [opcode_of_ShiftiwopVariant]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        shiftiwop_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SRLIW
          (by simp [opcode_of_ShiftiwopVariant]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.zeroExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_usgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 5 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SRLIW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRLIW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.immw_to_KB_Nat_usgn imm'] at h_spec
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = BitVec.signExtend 64
                (U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.op_b_access.access.value_0 row 0),
                              BitVec.ofNat 16 ↑(air.cols.op_b_access.access.value_1 row 0)] >>> imm'.toNat) := by
          rw [h_spec]; simp; rw [Nat.mod_eq_of_lt (by grind)]
        simp [op_b_value]; rw [← h_spec']; simp [BitVec.ofNatLT_eq_ofNat]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRAIW (opcode 44, RV64-only 32-bit arithmetic
    shift-right immediate). The `.SRAW` ALU arm already takes `.toNat`, so
    the only bridge needed is `(extractLsb (c.setWidth 32) 4 0).toNat = imm'.toNat`. -/
    theorem equivalence_SRAIW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 44 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 5 := (U64w.toBV (op_c_value air row)).setWidth 5
      execute_instruction (instruction.SHIFTIWOP (imm, rs1, rd, sopw.SRAIW)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, h_selectors, h_reg_rd, h_reg_rs1 ⟩
        := shiftiwop_operand_setup air row h_row h_is_real (by grind) .SRAIW
             (by simp [opcode_of_ShiftiwopVariant]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg0 ⟩ :=
        shiftiwop_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .SRAIW
          (by simp [opcode_of_ShiftiwopVariant]; exact h_opcode.1) h_opcode.2.1 h_opcode.2.2
          h_selectors h_reg_rd h_reg_rs1
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.zeroExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_usgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 5 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_SRAIW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRAIW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPEW_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        rw [Transpiler.immw_to_KB_Nat_usgn imm'] at h_spec
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = BitVec.signExtend 64
                ((U32w.toBV #v[BitVec.ofNat 16 ↑(air.cols.op_b_access.access.value_0 row 0),
                              BitVec.ofNat 16 ↑(air.cols.op_b_access.access.value_1 row 0)]).sshiftRight imm'.toNat) := by
          rw [h_spec]; simp; rw [Nat.mod_eq_of_lt (by grind)]
        simp [op_b_value]; rw [← h_spec']; simp [BitVec.ofNatLT_eq_ofNat]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value] at *
        split_ands <;> [ simp; skip; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end SHIFTIWOP

  section MUL_FAMILY

    -- ========================================================================
    -- MUL-family variant tag. The MUL family spans 5 chip opcodes:
    --   MUL    = 30   — low 64 bits, signedness-agnostic (5-existential inversion)
    --   MULH   = 31   — high 64 bits, signed × signed
    --   MULHU  = 32   — high 64 bits, unsigned × unsigned
    --   MULHSU = 33   — high 64 bits, signed × unsigned
    --   MULW   = 48   — 32-bit × 32-bit → 32-bit sign-extended to 64
    -- All five share the same Program-bus column layout (3 register operands,
    -- imm_b = 0, imm_c = 0, is_alu = 1), so the operand/bus setups can be
    -- factored exactly as for `rtype_operand_setup` / `rtype_bus_setup`.
    -- ========================================================================

    inductive MulVariant where
      | MUL | MULH | MULHU | MULHSU | MULW
      deriving DecidableEq, Repr

    def opcode_of_MulVariant : MulVariant → FKB
      | .MUL    => 30
      | .MULH   => 31
      | .MULHU  => 32
      | .MULHSU => 33
      | .MULW   => 48

    -- ========================================================================
    -- MUL-family operand setup. Mirrors `rtype_operand_setup` but for the
    -- five MUL/MULW chip opcodes. Caller supplies `var : MulVariant` +
    -- `h_opcode : opcode = opcode_of_MulVariant var`. The chip-side imm_b /
    -- imm_c flags are returned (eq_imm_b, eq_imm_c) — for the MUL family
    -- the transpiler emits both as 0, so callers can pattern-match them out.
    -- For `.MUL` (opcode 30) the underlying inversion is 5-existential
    -- (∃ rs2 rs1 rd sl sr, …); we drop the irrelevant sl/sr and return a
    -- 3-existential, matching the shape of the other 4 variants. The
    -- caller's `equivalence_MUL` will then universally quantify the
    -- signedness fields at the theorem statement (mirroring
    -- `execute_MUL_equiv` in `mul.lean:88`).
    -- ========================================================================

    /-- Operand-setup lemma for the MUL family (5 opcodes: MUL/MULH/MULHU/
    MULHSU/MULW). Mirrors `rtype_operand_setup`. -/
    lemma mul_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (var : MulVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_MulVariant var)
    :
      ∃ (rs2 rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = Transpiler.reg_to_KB rs2 ∧
        air.cols.instruction.op_c_1 row 0 = 0 ∧
        air.cols.instruction.op_c_2 row 0 = 0 ∧
        air.cols.instruction.op_c_3 row 0 = 0 ∧
        air.cols.instruction.op_a_is_x0 row 0 = (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        air.cols.opcode_selector.imm_c row 0 = 0 ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32 ∧
        (air.cols.instruction.op_c_0 row 0).val < 32
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      replace h_all_wf := h_all_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_all_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_all_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      -- ------------------------------------------------------------------
      -- Dispatch on the variant. .MUL is 5-existential; the rest are
      -- 3-existential. The post-`obtain` body is otherwise identical.
      -- ------------------------------------------------------------------
      cases var
      -- .MUL (opcode 30): 5-existential — drop sl / sr.
      . simp [opcode_of_MulVariant] at h_opcode
        simp [h_opcode] at h_opcode_props
        obtain ⟨ rs2, rs1, rd, sl, sr, h_eq_instr ⟩ := h_opcode_props
        refine ⟨ rs2, rs1, rd, ?_ ⟩
        simp [h_eq_instr] at h_eq
        simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
        simp [h_eq_data] at h_eq_entry
        simp [h_props, Transpiler.is_register] at h_eq_props
        obtain ⟨ _eq_opcode,
                 eq_a0, eq_a1, eq_a2, eq_a3,
                 eq_b0, eq_b1, eq_b2, eq_b3,
                 eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                 eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
        simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
        obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
        simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
        exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                eq_b0, eq_b1, eq_b2, eq_b3,
                eq_c0, eq_c1, eq_c2, eq_c3,
                eq_a_is_x0,
                eq_imm_b, eq_imm_c,
                h_selectors,
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULH (opcode 31): 3-existential, fixed (.High, .Signed, .Signed).
      . simp [opcode_of_MulVariant] at h_opcode
        simp [h_opcode] at h_opcode_props
        obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
        refine ⟨ rs2, rs1, rd, ?_ ⟩
        simp [h_eq_instr] at h_eq
        simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
        simp [h_eq_data] at h_eq_entry
        simp [h_props, Transpiler.is_register] at h_eq_props
        obtain ⟨ _eq_opcode,
                 eq_a0, eq_a1, eq_a2, eq_a3,
                 eq_b0, eq_b1, eq_b2, eq_b3,
                 eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                 eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
        simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
        obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
        simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
        exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                eq_b0, eq_b1, eq_b2, eq_b3,
                eq_c0, eq_c1, eq_c2, eq_c3,
                eq_a_is_x0,
                eq_imm_b, eq_imm_c,
                h_selectors,
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULHU (opcode 32).
      . simp [opcode_of_MulVariant] at h_opcode
        simp [h_opcode] at h_opcode_props
        obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
        refine ⟨ rs2, rs1, rd, ?_ ⟩
        simp [h_eq_instr] at h_eq
        simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
        simp [h_eq_data] at h_eq_entry
        simp [h_props, Transpiler.is_register] at h_eq_props
        obtain ⟨ _eq_opcode,
                 eq_a0, eq_a1, eq_a2, eq_a3,
                 eq_b0, eq_b1, eq_b2, eq_b3,
                 eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                 eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
        simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
        obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
        simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
        exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                eq_b0, eq_b1, eq_b2, eq_b3,
                eq_c0, eq_c1, eq_c2, eq_c3,
                eq_a_is_x0,
                eq_imm_b, eq_imm_c,
                h_selectors,
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULHSU (opcode 33).
      . simp [opcode_of_MulVariant] at h_opcode
        simp [h_opcode] at h_opcode_props
        obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
        refine ⟨ rs2, rs1, rd, ?_ ⟩
        simp [h_eq_instr] at h_eq
        simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
        simp [h_eq_data] at h_eq_entry
        simp [h_props, Transpiler.is_register] at h_eq_props
        obtain ⟨ _eq_opcode,
                 eq_a0, eq_a1, eq_a2, eq_a3,
                 eq_b0, eq_b1, eq_b2, eq_b3,
                 eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                 eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
        simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
        obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
        simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
        exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                eq_b0, eq_b1, eq_b2, eq_b3,
                eq_c0, eq_c1, eq_c2, eq_c3,
                eq_a_is_x0,
                eq_imm_b, eq_imm_c,
                h_selectors,
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULW (opcode 48).
      . simp [opcode_of_MulVariant] at h_opcode
        simp [h_opcode] at h_opcode_props
        obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
        refine ⟨ rs2, rs1, rd, ?_ ⟩
        simp [h_eq_instr] at h_eq
        simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
        simp [h_eq_data] at h_eq_entry
        simp [h_props, Transpiler.is_register] at h_eq_props
        obtain ⟨ _eq_opcode,
                 eq_a0, eq_a1, eq_a2, eq_a3,
                 eq_b0, eq_b1, eq_b2, eq_b3,
                 eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                 eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
        simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
        obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
        simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
        exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                eq_b0, eq_b1, eq_b2, eq_b3,
                eq_c0, eq_c1, eq_c2, eq_c3,
                eq_a_is_x0,
                eq_imm_b, eq_imm_c,
                h_selectors,
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩

    -- ========================================================================
    -- MUL-family bus setup. Identical in shape to `rtype_bus_setup` — the
    -- chip's State-bus emission for MUL/MULW is the same as for RTYPE
    -- (imm_b = imm_c = 0 means op_a/op_b/op_c are all register reads). The
    -- ALU-bus shape only differs by opcode value (handled by `h_opcode`).
    -- ========================================================================

    /-- Bus-side setup lemma for the MUL family. -/
    lemma mul_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (var : MulVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_MulVariant var)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd  : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
      (h_reg_rs2 : (air.cols.instruction.op_c_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_c_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_c_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1, h_reg_rs2
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses; simp at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses; simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      show _ ∧ _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . simp only [op_c_value]; exact h_reg2
      . exact h_reg0

    /-- Equivalence for MULH (opcode 31, `instruction.MUL` with
    `result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed`).
    Probe equivalence for the MUL family: validates that the chip's
    `execute_MUL_pure b c .MULH` matches the Sail spec's
    `execute_MUL_pure r1_val r2_val .MULH` without any bridge work
    (no immediate, no shift extraction). Note the `h_wf_alu` destructure
    has the extra `_h_operands` slot because every MUL/MULW arm of
    `ALUBus.Spec` carries `operand_range ∧ …` (same as XOR/OR/AND). -/
    theorem equivalence_MULH
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 31)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Signed })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses to the current row + pull common facts.
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULH
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULH
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      -- Phase 2: bridge Sail MUL → spec_MULH via execute_MULH_equiv.
      rw [
        OpcodeSpec.RV64.execute_MULH_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      -- Phase 3: state equality.
      . simp [
          OpcodeSpec.RV64.spec_MULH,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        -- ALU arms 30..33 / 48 all wrap their spec as `operand_range ∧ …`,
        -- so the destructure picks up an extra `_h_operands` slot (same as
        -- the XOR/OR/AND RTYPE pattern).
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      -- Phase 4: discharge execute_MULH_equiv hypothesis side-goal.
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MUL (opcode 30, `instruction.MUL` with
    `result_part := .Low`). The Sail spec for MUL is parametric in the
    signedness fields (the low 64 bits of the product do not depend on
    sign), so the theorem universally quantifies `srs1 srs2 : Signedness`
    just like `OpcodeSpec.RV64.execute_MUL_equiv`. Internally the
    `mul_operand_setup .MUL` invocation handles the 5-existential
    inversion (it drops the irrelevant `sl / sr` returned by
    `operand_properties_inversion`). -/
    theorem equivalence_MUL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 30)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (srs1 srs2 : Signedness)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.Low,
            signed_rs1   := srs1,
            signed_rs2   := srs2 })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MUL
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MUL
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MUL_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MUL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MULHU (opcode 32, `instruction.MUL` with
    `result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned`). -/
    theorem equivalence_MULHU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 32)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Unsigned,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULHU
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULHU
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MULHU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MULHU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MULHSU (opcode 33, `instruction.MUL` with
    `result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned`). -/
    theorem equivalence_MULHSU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 33)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULHSU
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULHSU
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MULHSU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MULHSU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MULW (opcode 48, `instruction.MULW`). Distinct
    constructor (`.MULW` vs `.MUL`) and the spec applies `setWidth 32`
    to the operands before multiplying — matching the chip's ALU bus
    arm 48 (`a = execute_MULW_pure (b.setWidth 32) (c.setWidth 32)`). -/
    theorem equivalence_MULW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 48)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MULW (rs2, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULW
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULW
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MULW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MULW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end MUL_FAMILY

  section DIV_FAMILY

    -- ========================================================================
    -- DIV-family variant tag. The DIV family spans 8 chip opcodes:
    --   DIV   = 34   — 64-bit signed division
    --   DIVU  = 35   — 64-bit unsigned division
    --   REM   = 36   — 64-bit signed remainder
    --   REMU  = 37   — 64-bit unsigned remainder
    --   DIVW  = 49   — 32-bit signed division (RV64-only)
    --   DIVUW = 50   — 32-bit unsigned division (RV64-only)
    --   REMW  = 51   — 32-bit signed remainder (RV64-only)
    --   REMUW = 52   — 32-bit unsigned remainder (RV64-only)
    -- All eight share the MUL-family bus layout (3 register operands,
    -- imm_b = 0, imm_c = 0, is_alu = 1), and unlike the MUL family their
    -- ALUBus.Spec arms do *not* prepend `operand_range ∧ …`, so the
    -- h_wf_alu destructure matches the ADD/SUB shape (no `_h_operands`).
    -- Every variant's inversion is 3-existential (no MUL-Low-style edge
    -- case), so `cases var <;> (…)` with a single common body suffices.
    -- ========================================================================

    inductive DivVariant where
      | DIV | DIVU | REM | REMU | DIVW | DIVUW | REMW | REMUW
      deriving DecidableEq, Repr

    def opcode_of_DivVariant : DivVariant → FKB
      | .DIV   => 34
      | .DIVU  => 35
      | .REM   => 36
      | .REMU  => 37
      | .DIVW  => 49
      | .DIVUW => 50
      | .REMW  => 51
      | .REMUW => 52

    /-- Operand-setup lemma for the DIV family. Mirrors `mul_operand_setup`. -/
    lemma div_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (var : DivVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_DivVariant var)
    :
      ∃ (rs2 rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = Transpiler.reg_to_KB rs2 ∧
        air.cols.instruction.op_c_1 row 0 = 0 ∧
        air.cols.instruction.op_c_2 row 0 = 0 ∧
        air.cols.instruction.op_c_3 row 0 = 0 ∧
        air.cols.instruction.op_a_is_x0 row 0 =
          (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        air.cols.opcode_selector.imm_c row 0 = 0 ∧
        (air.cols.opcode_selector.is_alu row 0 = 1 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32 ∧
        (air.cols.instruction.op_c_0 row 0).val < 32
    := by
      replace h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      -- All 8 variants are 3-existential and share an identical post-`obtain`
      -- body — closing over them with `cases var <;> (…)`.
      cases var <;>
        ( simp [opcode_of_DivVariant] at h_opcode
          simp [h_opcode] at h_opcode_props
          obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ rs2, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0,
                  eq_imm_b, eq_imm_c,
                  h_selectors,
                  h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ )

    /-- Bus-side setup lemma for the DIV family. Identical in shape to
    `mul_bus_setup`. -/
    lemma div_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (var : DivVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_DivVariant var)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 1 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = 0 ∧
        air.cols.opcode_selector.is_bne row 0 = 0 ∧
        air.cols.opcode_selector.is_blt row 0 = 0 ∧
        air.cols.opcode_selector.is_bge row 0 = 0 ∧
        air.cols.opcode_selector.is_bltu row 0 = 0 ∧
        air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rd  : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32)
      (h_reg_rs2 : (air.cols.instruction.op_c_0 row 0).val < 32)
    :
      List.Forall
        (fun a => a.multiplicity = 1 →
          ALUBus.Spec a.ALU_opcode
            a.a_0 a.a_1 a.a_2 a.a_3 a.b_0 a.b_1 a.b_2 a.b_3 a.c_0 a.c_1 a.c_2 a.c_3)
        (bus_row air row).ALU ∧
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_c_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_c_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1, h_reg_rs2
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses; simp at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses; simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      grind [op_b_value, op_c_value]

    /-- Equivalence for DIV (opcode 34, signed 64-bit division,
    `instruction.DIV (…, false)` in Sail). Probe equivalence for the DIV
    family — same close as `equivalence_MULH` but without the extra
    `_h_operands` slot in the destructure (DIV/REM/DIVW/REMW ALUBus.Spec
    arms don't carry `operand_range ∧ …`). -/
    theorem equivalence_DIV
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 34)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIV
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIV
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIV_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIV,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for DIVU (opcode 35, unsigned 64-bit division). -/
    theorem equivalence_DIVU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 35)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIVU
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIVU
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIVU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIVU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REM (opcode 36, signed 64-bit remainder). -/
    theorem equivalence_REM
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 36)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REM
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REM
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REM_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REM,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REMU (opcode 37, unsigned 64-bit remainder). -/
    theorem equivalence_REMU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 37)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REMU
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REMU
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REMU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REMU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for DIVW (opcode 49, signed 32-bit division, RV64-only). -/
    theorem equivalence_DIVW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 49)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIVW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIVW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIVW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIVW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for DIVUW (opcode 50, unsigned 32-bit division, RV64-only). -/
    theorem equivalence_DIVUW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 50)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIVUW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIVUW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIVUW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIVUW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REMW (opcode 51, signed 32-bit remainder, RV64-only). -/
    theorem equivalence_REMW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 51)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REMW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REMW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REMW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REMW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REMUW (opcode 52, unsigned 32-bit remainder, RV64-only). -/
    theorem equivalence_REMUW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 52)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REMUW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REMUW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REMUW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REMUW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end DIV_FAMILY

  section UTYPE

    -- ========================================================================
    -- UTYPE — `instruction.UTYPE (imm, rd, uop)` with `imm : BitVec 20` and
    -- `uop ∈ { .LUI, .AUIPC }`. Sail semantics for both:
    --   LUI    rd_val = signExtend 64 (imm ++ 0#12)
    --   AUIPC  rd_val = pc       + signExtend 64 (imm ++ 0#12)
    -- Chip encoding: both use `imm_b = 1` AND `imm_c = 1` (so neither op_b
    -- nor op_c is a register read). The chip's columns are:
    --   LUI   : opcode = 0,  is_alu = 1,  is_auipc = 0,
    --           op_b = 0 (literal), op_c = imm_KB (signExtend 64 (imm ++ 0#12))
    --   AUIPC : opcode = 27, is_alu = 0,  is_auipc = 1,
    --           op_b = op_c = imm_KB
    -- LUI is computed via the standard ALU bus arm 0 (`a = b + c = 0 + imm`).
    -- AUIPC is computed via a dedicated ALU bus row whose `b` is `pc` and
    -- `c` is `op_b` (see `auipc_op_a_eq_pc_plus_op_b`).
    -- ========================================================================

    /-- Equivalence for LUI (opcode 0, `instruction.UTYPE (imm, rd, .LUI)`).
    Inversion at opcode 0 is a 3-way disjunction (RTYPE.ADD / ITYPE.ADDI /
    UTYPE.LUI); `imm_b = 1, imm_c = 1` selects LUI. The 20-bit `imm` is
    recovered from the chip's `op_c` columns as `((op_c >>> 12).setWidth 20)`
    — chip stores `signExtend 64 (imm ++ 0#12)`. -/
    theorem equivalence_LUI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let imm : BitVec 20 := (U64w.toBV (op_c_value air row) >>> 12).setWidth 20
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      -- Operand extraction (inline; 2-existential ⟨imm, rd⟩).
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode.1, h_opcode.2.1, h_opcode.2.2] at h_opcode_props
      obtain ⟨ imm', rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, Transpiler.opcode_of_uop, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      simp [h_eq_data] at h_eq_entry
      simp [h_props, Transpiler.is_register] at h_eq_props
      obtain ⟨ _eq_opcode,
               eq_a0, eq_a1, eq_a2, eq_a3,
               eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
               _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
      simp [← eq_a0] at h_eq_props
      simp [Fin.lt_def] at h_eq_props
      have h_reg_rd := h_eq_props
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      -- Bridge: op_c stores `signExtend 64 (imm' ++ 0#12)` via `imm_c = 1`.
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 (imm' ++ 0#12) := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn (imm' ++ 0#12)
      have h_imm_eq : ((U64w.toBV (op_c_value air row)) >>> 12).setWidth 20 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      -- Bridge: op_b is literally 0 (no register read, no immediate either —
      -- LUI uses `imm_b = 1` with `instruction.op_b_*` all hardcoded to 0).
      have h_imm_b_eqs := imm_b_eq_1_constraints air row h_opcode.2.1 h_all_constraints
      have h_op_b_zero :
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] = (0 : BitVec 64) := by
        simp only [h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1, h_imm_b_eqs.2.2.2,
                   eq_b0, eq_b1, eq_b2, eq_b3]
        rw [← BitVec.toNat_inj]; simp [U64w.toNat]
      -- Bus extraction (only pc + op_a write; no op_b/op_c reads under imm_b=imm_c=1).
      have h_all_wf' : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_all_wf'
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf'
      have h_bus :
        Sail.readReg Register.PC state =
          EStateM.Result.ok
            (BitVec.ofNatLT (w := 64)
              (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
               4294967296 * ↑(air.cols.pc_2 row 0))
              (by
                have := (air.cols.pc_0 row 0).isLt
                have := (air.cols.pc_1 row 0).isLt
                have := (air.cols.pc_2 row 0).isLt
                omega))
            state ∧
        read_xreg
            (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
            state =
          EStateM.Result.ok
            (U64w.toBV
              #v[ air.cols.op_a_access.prev_value_0 row 0,
                  air.cols.op_a_access.prev_value_1 row 0,
                  air.cols.op_a_access.prev_value_2 row 0,
                  air.cols.op_a_access.prev_value_3 row 0 ])
            state := by
        simp [
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd
        ] at h_bus_hypotheses
        obtain ⟨ h_pc, h_reg0, _ ⟩ := h_bus_hypotheses
        simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
        exact ⟨ h_pc, h_reg0 ⟩
      obtain ⟨ h_pc, h_reg0 ⟩ := h_bus
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_LUI_equiv
        (pc_val := U64w.toBV (pc air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_LUI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd
        ]
        subst reg0
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        -- Fold h_spec into the Sail-spec form: `0 + signExtend 64 (imm' ++ 0#12) = signExtend …`.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = BitVec.signExtend 64 (imm' ++ 0#12) := by
          rw [h_spec, Transpiler.imm_to_KB_BV_sgn]
          simp [U64w.toBV]
        simp [← h_spec', BitVec.ofNatLT_eq_ofNat]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [OpcodeSpec.RV64.spec_LUI, operation_list_effect, operation_effect]
        simp [Sail.writeReg, PreSail.writeReg]
        simp [h_pc, pc, ← BitVec.toNat_inj, U64w.toNat]
        clear *- pc_npc_bounds; omega

    /-- Equivalence for AUIPC (opcode 27, `instruction.UTYPE (imm, rd, .AUIPC)`).
    Inversion is single-arm. Chip computes `op_a = pc + op_b` via the dedicated
    AUIPC ALU bus row (see `auipc_op_a_eq_pc_plus_op_b`); `imm_b = 1` forces
    `op_b = signExtend 64 (imm ++ 0#12)`. -/
    theorem equivalence_AUIPC
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 27 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_is_auipc : air.cols.opcode_selector.is_auipc row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let imm : BitVec 20 := (U64w.toBV (op_b_value air row) >>> 12).setWidth 20
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints :=
        is_auipc_active_constraints air row h_row h_is_real (by grind) h_is_auipc
          (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode.1] at h_opcode_props
      obtain ⟨ imm', rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, Transpiler.opcode_of_uop, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      simp [h_eq_data] at h_eq_entry
      simp [h_props, Transpiler.is_register] at h_eq_props
      obtain ⟨ _eq_opcode,
               eq_a0, eq_a1, eq_a2, eq_a3,
               eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
               _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
      simp [← eq_a0] at h_eq_props
      simp [Fin.lt_def] at h_eq_props
      have h_reg_rd := h_eq_props
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      -- Bridge: op_b stores `signExtend 64 (imm' ++ 0#12)` via `imm_b = 1`.
      have h_imm_b_eqs := imm_b_eq_1_constraints air row h_opcode.2.1 h_all_constraints
      have h_op_b_bv :
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 (imm' ++ 0#12) := by
        simp only [h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1, h_imm_b_eqs.2.2.2,
                   eq_b0, eq_b1, eq_b2, eq_b3]
        exact Transpiler.imm_to_KB_BV_sgn (imm' ++ 0#12)
      have h_imm_eq : ((U64w.toBV (op_b_value air row)) >>> 12).setWidth 20 = imm' := by
        simp only [op_b_value]; rw [h_op_b_bv]; bv_decide
      -- The dedicated AUIPC ALU bridge: `op_a = pc + op_b`.
      have h_auipc := auipc_op_a_eq_pc_plus_op_b air row h_is_real (by grind) h_is_auipc
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
        h_reg_rd
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_AUIPC_equiv
        (pc_val := U64w.toBV (pc air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_AUIPC,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd
        ]
        subst reg0
        rw [operation_list_effect_state_swap_writePC_writeReg]
        -- Fold `op_a = pc + op_b = pc + signExtend 64 (imm' ++ 0#12)` into h_spec'.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = U64w.toBV (pc air row) + BitVec.signExtend 64 (imm' ++ 0#12) := by
          rw [h_auipc, h_op_b_bv]
        simp [← h_spec', BitVec.ofNatLT_eq_ofNat]
        rw [seq_constraints.2.1]
      . simp [OpcodeSpec.RV64.spec_AUIPC, operation_list_effect, operation_effect]
        simp [Sail.writeReg, PreSail.writeReg]
        simp [h_pc, pc, ← BitVec.toNat_inj, U64w.toNat]
        clear *- pc_npc_bounds; omega

  end UTYPE

  section JUMPS

    -- ========================================================================
    -- JAL / JALR — unconditional jumps. Both consume the link via
    -- `op_a = pc + 4` (when `op_a_is_x0 = 0`) and produce a new `next_pc`
    -- via dedicated ALU bus rows.
    --
    -- Chip encoding:
    --   JAL  (opcode 24): imm_b = 1, imm_c = 1, is_jal  = 1.
    --                     op_b = imm_KB (= signExtend 64 imm), op_c = 0.
    --                     `jal_next_pc_eq_pc_plus_op_b`: next_pc = pc + op_b.
    --   JALR (opcode 25): imm_b = 0, imm_c = 1, is_jalr = 1.
    --                     op_b = rs1, op_c = imm_KB (= signExtend 64 imm).
    --                     `jalr_next_pc_plus_specific_eq_op_b_plus_op_c`:
    --                     [next_pc_0 + specific_0, next_pc_1, next_pc_2, 0]
    --                       = op_b + op_c.  specific_0 ∈ {0,1} is the JALR
    --                     low-bit clear witness.
    --
    -- For both, `is_jal_active_constraints` / `is_jalr_active_constraints`
    -- supply `op_a = pc + 4` (gated on `op_a_is_x0 = 0`).
    --
    -- Both Sail specs (`execute_JAL_equiv`, `execute_JALR_equiv`) carry an
    -- `h_success` precondition (target 4-aligned for JAL; bit 1 of the
    -- un-masked target = 0 for JALR). Both are discharged from
    -- `next_pc_mod_four_eq_zero` + the per-opcode ALU bridge.
    -- ========================================================================

    /-- Equivalence for JAL (opcode 24, `instruction.JAL (imm, rd)`).
    Mirrors RV32's `equivalence_JAL` template. -/
    theorem equivalence_JAL
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 24 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_is_jal : air.cols.opcode_selector.is_jal row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let imm : BitVec 21 := (U64w.toBV (op_b_value air row)).setWidth 21
      execute_instruction (instruction.JAL (imm, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses + pull common chip-side facts.
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_next_pc := jal_next_pc_eq_pc_plus_op_b air row h_is_real (by grind) h_is_jal
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      have jal_constraints :=
        is_jal_active_constraints air row h_row h_is_real (by grind) (by grind) h_is_jal h_constraints
      -- Phase 2: operand extraction (inline; 2-existential ⟨imm, rd⟩).
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode.1] at h_opcode_props
      obtain ⟨ imm', rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      simp [h_eq_data] at h_eq_entry
      simp [h_props, Transpiler.is_register] at h_eq_props
      obtain ⟨ _eq_opcode,
               eq_a0, eq_a1, eq_a2, eq_a3,
               eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
               _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
      simp [← eq_a0] at h_eq_props
      simp [Fin.lt_def] at h_eq_props
      obtain ⟨ h_reg_rd, _h_imm_mod_2 ⟩ := h_eq_props
      -- Phase 3: B-value equalities (op_b stores `signExtend 64 imm'` via `imm_b = 1`).
      have h_imm_b_eqs := imm_b_eq_1_constraints air row h_opcode.2.1 h_constraints
      have h_op_b_bv :
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1, h_imm_b_eqs.2.2.2,
                   eq_b0, eq_b1, eq_b2, eq_b3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_b_value air row)).setWidth 21 = imm' := by
        simp only [op_b_value]; rw [h_op_b_bv]; bv_decide
      -- Phase 4: next_pc = pc + op_b = pc + signExtend 64 imm'.
      have h_next_pc_eq :
          U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + BitVec.signExtend 64 imm' := by
        rw [h_next_pc, h_op_b_bv]
      -- Phase 5: bus extraction (only pc + op_a write under imm_b = imm_c = 1).
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
        h_reg_rd
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
      -- Phase 6: success precondition (target 4-aligned) from next_pc_mod_four_eq_zero.
      have h_success :
          (U64w.toBV (pc air row) + BitVec.signExtend 64 imm') % 4 = 0 := by
        rw [BitVec.mod_4_zero_equiv_64, ← h_next_pc_eq]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind
      -- Phase 7: SE round-trip.
      have h_se : BitVec.signExtend 64 ((BitVec.signExtend 64 imm').setWidth 21) =
                  BitVec.signExtend 64 imm' := by bv_decide
      -- Phase 8: apply execute_JAL_equiv.
      extract_lets reg0 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_JAL_equiv
        (pc_val := U64w.toBV (pc air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
        (h_success := by clear *- h_success; rw [BitVec.mod_4_zero_equiv_64] at h_success; grind)
      ]
      -- Phase 9: state equality.
      . simp [
          OpcodeSpec.RV64.spec_JAL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd
        ]
        subst reg0
        rw [operation_list_effect_state_swap_writePC_writeReg]
        rw [h_next_pc_eq]
        -- Handle the WriteReg for the link register, split on op_a_is_x0.
        by_cases h_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0
        . -- rd ≠ x0: chip's op_a = pc + 4, matches Sail's `pc + 4#64`.
          have h_op_a := jal_constraints.1 h_x0
          have h_op_a_pc4 :
            U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ]
            = U64w.toBV (pc air row) + 4#64 := by
            have h_v3 : air.cols.op_a_access.access.value_3 row 0 = (0 : BitVec 16)
              := by simp [jal_constraints.2.1]
            simp [h_v3, h_op_a]
          simp [← h_op_a_pc4, BitVec.ofNatLT_eq_ofNat]
        . -- rd = x0: chip's WriteReg x0 v is a no-op (x0 hardwired); Sail's
          -- WriteReg x0 (pc + 4) is also a no-op via write_xreg.
          push_neg at h_x0
          have h_a0_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            simp [eq_a_is_x0] at h_x0; simp_all
            simp [Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            grind
          simp [
            operation_list_effect, operation_effect,
            write_xreg, regidx_to_fin, h_a0_zero
          ]
      -- Phase 10: PC read condition discharge.
      . simp [OpcodeSpec.RV64.spec_JAL, operation_list_effect, operation_effect]
        simp [Sail.writeReg, PreSail.writeReg]
        simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
        clear *- pc_npc_bounds; omega

    /-- Equivalence for JALR (opcode 25, `instruction.JALR (imm, rs1, rd)`).
    Mirrors `equivalence_JAL` but with: op_b is a register read (rs1) since
    `imm_b = 0`; op_c is the immediate (`imm_c = 1`); the next_pc relation is
    `[next_pc_0 + specific_0, next_pc_1, next_pc_2, 0] = op_b + op_c` with
    `specific_0 ∈ {0,1}` (`is_jalr_active_constraints.2.2.2`), so
    `mask &&& (op_b + op_c) = next_pc` after factoring out `specific_0`. The
    Sail success precondition `(rs1 + signExtend 64 imm)[1] = 0` follows from
    `next_pc_0[1] = 0` (via `next_pc_mod_four_eq_zero`) + `specific_0 ∈ {0,1}`. -/
    theorem equivalence_JALR
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 25 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_is_jalr : air.cols.opcode_selector.is_jalr row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.JALR (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses + pull common chip-side facts.
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_jalr_next_pc :=
        jalr_next_pc_plus_specific_eq_op_b_plus_op_c air row h_is_real (by grind) h_is_jalr
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      have jalr_constraints :=
        is_jalr_active_constraints air row h_row h_is_real (by grind) (by grind) h_is_jalr h_constraints
      -- Phase 2: operand extraction (inline; 3-existential ⟨imm, rs1, rd⟩).
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      simp [h_opcode.1] at h_opcode_props
      obtain ⟨ imm', rs1', rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      simp [h_eq_data] at h_eq_entry
      simp [h_props, Transpiler.is_register] at h_eq_props
      obtain ⟨ _eq_opcode,
               eq_a0, eq_a1, eq_a2, eq_a3,
               eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
               _eq_imm_b, _eq_imm_c, h_selectors ⟩ := h_eq_entry
      simp [← eq_a0, ← eq_b0] at h_eq_props
      simp [Fin.lt_def] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1, _h_imm_mod_2 ⟩ := h_eq_props
      -- Phase 3: C-value equalities (op_c stores `signExtend 64 imm'` via `imm_c = 1`).
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      -- Phase 4: bus extraction (pc + op_b read + op_a write).
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
        h_reg_rd, h_reg_rs1
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg0
      -- Phase 5: derive `(op_b + op_c) % 4 = 0`-ish — bit 0 = specific_0, bit 1 = 0.
      -- Helper: the chip's LHS `next_pc + specific_0` in U64w form.
      have h_specific_bool := jalr_constraints.2.2.2
      have h_npc_sum :
          U64w.toBV (op_b_value air row) + U64w.toBV (op_c_value air row) =
          U64w.toBV #v[ ((air.cols.next_pc_0 row 0 + air.cols.opcode_specific.specific_0 row 0
                          : FKB) : BitVec 16),
                        air.cols.next_pc_1 row 0,
                        air.cols.next_pc_2 row 0,
                        0#16 ] := by
        simp only [op_b_value, op_c_value]
        rw [← h_jalr_next_pc]
      -- Bit 1 of `op_b + op_c` = 0 (success precondition for Sail). Stated
      -- without indexing — converted to the `[1]`-form via
      -- `BitVec.mod_4_lt_two_equiv_64` at the call site.
      have h_success :
          (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm') % 4 < 2 := by
        rw [BitVec.mod_4_lt_two_equiv_64,
            show BitVec.signExtend 64 imm' = U64w.toBV (op_c_value air row) from h_op_c_bv.symm,
            h_npc_sum]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4 h_specific_bool h_npc0_lt
        grind
      -- Phase 6: `mask &&& (op_b + op_c) = next_pc` (BV).
      have h_mask_eq :
          (0xFFFFFFFFFFFFFFFE#64) &&& (U64w.toBV (op_b_value air row) +
                                       U64w.toBV (op_c_value air row)) =
          U64w.toBV (next_pc air row) := by
        rw [h_npc_sum]
        clear *- h_npc_mod4 h_specific_bool pc_npc_bounds
        simp [next_pc, U64w.toBV]
        rw [show 18446744073709551614#64 = 65535#16 ++ 65535#16 ++ 65535#16 ++ 65534#16 by simp]
        repeat rw [BitVec.and_append]
        simp; congr <;> [ bv_decide; bv_decide; skip ]
        suffices h_mod_4_zero : BitVec.ofNat 16 ↑(air.cols.next_pc_0 row 0) % 4 = 0
        . rw [BitVec.mod_4_zero_equiv_16] at h_mod_4_zero
          obtain h_specific_bool | h_specific_bool := h_specific_bool <;> simp [h_specific_bool]
          . bv_decide
          . simp [Fin.val_add]; rw [Nat.mod_eq_of_lt (by omega)]
            simp [BitVec.ofNat_add]
            bv_decide
        . simpa [← BitVec.toNat_inj]
      -- Phase 7: SE round-trip.
      have h_se : BitVec.signExtend 64 ((BitVec.signExtend 64 imm').setWidth 12) =
                  BitVec.signExtend 64 imm' := by bv_decide
      -- Phase 8: apply execute_JALR_equiv.
      extract_lets reg0 reg1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_JALR_equiv
        (pc_val := U64w.toBV (pc air row))
        (rs1_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
        (h_cur_privilege := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
        (h_mseccfg := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
        (h_success := by
          clear *- h_success
          rw [BitVec.mod_4_lt_two_equiv_64] at h_success
          grind)
      ]
      -- Phase 9: state equality.
      . simp [
          OpcodeSpec.RV64.spec_JALR,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd, h_reg_rs1
        ]
        subst reg0 reg1
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        -- Fold `0xFFFE &&& (op_b + signExtend 64 imm') = next_pc` via h_mask_eq.
        rw [show U64w.toBV (next_pc air row) =
              (0xFFFFFFFFFFFFFFFE#64) &&& (U64w.toBV (op_b_value air row) +
                                           U64w.toBV (op_c_value air row))
              from h_mask_eq.symm]
        rw [show U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' from h_op_c_bv]
        -- Handle the WriteReg for the link register, split on op_a_is_x0.
        by_cases h_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0
        . -- rd ≠ x0: chip's op_a = pc + 4, matches Sail's `pc + 4#64`.
          have h_op_a := jalr_constraints.1 h_x0
          have h_op_a_pc4 :
            U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ]
            = U64w.toBV (pc air row) + 4#64 := by
            have h_v3 : air.cols.op_a_access.access.value_3 row 0 = (0 : BitVec 16)
              := by simp [jalr_constraints.2.1]
            simp [h_v3, h_op_a]
          simp [← h_op_a_pc4, BitVec.ofNatLT_eq_ofNat, op_b_value]
        . -- rd = x0: both Sail and chip writes reduce to write_xreg no-ops.
          push_neg at h_x0
          have h_a0_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            simp [eq_a_is_x0] at h_x0; simp_all
            simp [Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            grind
          simp [
            operation_list_effect, operation_effect,
            write_xreg, regidx_to_fin, h_a0_zero
          ]
      -- Phase 10: PC read condition discharge.
      . simp [OpcodeSpec.RV64.spec_JALR, operation_list_effect, operation_effect]
        simp [Sail.writeReg, PreSail.writeReg]
        split_ands
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [op_b_value]; rw [← h_reg1]

  end JUMPS

  section BTYPE

    -- ========================================================================
    -- BTYPE — branch instructions (BEQ, BNE, BLT, BGE, BLTU, BGEU).
    -- Chip encoding:
    --   * opcode ∈ {18..23} via `opcode_of_bop`
    --   * imm_b = 0, imm_c = 1 (op_c holds the 13-bit immediate)
    --   * op_a stores rs1, op_b stores rs2 — no rd (branches do not write any
    --     register; `op_a_is_x0 = 0` literally and op_a's value is constrained
    --     to equal its prev_value via `branching_eq_one_characterisation` /
    --     `is_branching_active_constraints`)
    --   * exactly one of `is_beq`/`is_bne`/`is_blt`/`is_bge`/`is_bltu`/`is_bgeu`
    --     is 1 (`branch_sum = 1`).
    -- Helpers used:
    --   * `is_branching_active_constraints` — `op_a = prev_value`; `branching` ∈ {0,1};
    --     `branching = 1 → next_pc = pc(row+1)` (transition); `not_branching = 1 →
    --     next_pc = pc + 4` (same-row).
    --   * `branching_next_pc_eq_pc_plus_op_c` — `next_pc = pc + op_c` when `branching = 1`.
    --   * `branch_instruction_a_lt_b` / `a_gt_b` — `specific_2 / specific_1` =
    --     comparison witnesses (signed when `is_blt + is_bge ≠ 0`, unsigned otherwise).
    --   * `imm_c_eq_1_constraints` — op_c stores the immediate.
    --   * `next_pc_mod_four_eq_zero` — needed to discharge the (guarded) Sail
    --     `h_success` (target 4-aligned), via `branching_next_pc_eq_pc_plus_op_c`.
    -- Per-branch `h_eq_branching` witness is built inline in each equivalence
    -- proof (mirroring RV32's pattern at `RV32IM/Equivalence/Equivalence.lean:3818`).
    -- ========================================================================

    /-- Operand-setup lemma for the BTYPE class. Mirrors `mul_operand_setup`
    but for the 6 branch opcodes. Returns the 13-bit immediate, rs2, rs1, the
    column equations, the imm_b = 0 / imm_c = 1 flags, the specific-branch
    selector via `(if (op == .X) then 1 else 0)`, and the two reg bounds and
    `imm % 2 = 0` precondition from the chip's BTYPE transpiler entry. -/
    lemma btype_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (op : bop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_bop op)
    :
      ∃ (imm : BitVec 13) (rs2 rs1 : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs2 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = (Transpiler.imm_to_KB imm true)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.imm_to_KB imm true)[1] ∧
        air.cols.instruction.op_c_2 row 0 = (Transpiler.imm_to_KB imm true)[2] ∧
        air.cols.instruction.op_c_3 row 0 = (Transpiler.imm_to_KB imm true)[3] ∧
        air.cols.instruction.op_a_is_x0 row 0 = 0 ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        air.cols.opcode_selector.imm_c row 0 = 1 ∧
        (air.cols.opcode_selector.is_alu row 0 = 0 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = (if (op == .BEQ) then 1 else 0) ∧
         air.cols.opcode_selector.is_bne row 0 = (if (op == .BNE) then 1 else 0) ∧
         air.cols.opcode_selector.is_blt row 0 = (if (op == .BLT) then 1 else 0) ∧
         air.cols.opcode_selector.is_bge row 0 = (if (op == .BGE) then 1 else 0) ∧
         air.cols.opcode_selector.is_bltu row 0 = (if (op == .BLTU) then 1 else 0) ∧
         air.cols.opcode_selector.is_bgeu row 0 = (if (op == .BGEU) then 1 else 0) ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32 ∧
        imm % 2 = 0
    := by
      replace h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      cases op <;>
        ( simp [Transpiler.opcode_of_bop] at h_opcode
          simp [h_opcode] at h_opcode_props
          obtain ⟨ imm, rs2, rs1, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ imm, rs2, rs1, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, Transpiler.opcode_of_bop, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0] at h_eq_props
          obtain ⟨ h_reg_rs1, h_reg_rs2, h_imm_mod_2 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rs1 h_reg_rs2
          refine ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3,
                   eq_a_is_x0,
                   eq_imm_b, eq_imm_c,
                   h_selectors,
                   h_reg_rs1, h_reg_rs2, h_imm_mod_2 ⟩ )

    /-- Bus-side setup lemma for the BTYPE class. Bus emits: PC read, rs2 read
    (via op_b, since `imm_b = 0`), rs1 read (via op_a — op_a stores rs1's
    register index for BTYPE, with the chip emitting a `WriteReg` of the
    prev_value as the no-op rd write). The `op_a` WriteReg is handled by
    `operation_list_effect_hypotheses_writeReg_same` inside the proof. -/
    lemma btype_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (_h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (op : bop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_bop op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_selectors :
        air.cols.opcode_selector.is_alu row 0 = 0 ∧
        air.cols.opcode_selector.is_ecall row 0 = 0 ∧
        air.cols.opcode_selector.is_lb row 0 = 0 ∧
        air.cols.opcode_selector.is_lbu row 0 = 0 ∧
        air.cols.opcode_selector.is_lh row 0 = 0 ∧
        air.cols.opcode_selector.is_lhu row 0 = 0 ∧
        air.cols.opcode_selector.is_lw row 0 = 0 ∧
        air.cols.opcode_selector.is_lwu row 0 = 0 ∧
        air.cols.opcode_selector.is_ld row 0 = 0 ∧
        air.cols.opcode_selector.is_sb row 0 = 0 ∧
        air.cols.opcode_selector.is_sh row 0 = 0 ∧
        air.cols.opcode_selector.is_sw row 0 = 0 ∧
        air.cols.opcode_selector.is_sd row 0 = 0 ∧
        air.cols.opcode_selector.is_beq row 0 = (if (op == .BEQ) then 1 else 0) ∧
        air.cols.opcode_selector.is_bne row 0 = (if (op == .BNE) then 1 else 0) ∧
        air.cols.opcode_selector.is_blt row 0 = (if (op == .BLT) then 1 else 0) ∧
        air.cols.opcode_selector.is_bge row 0 = (if (op == .BGE) then 1 else 0) ∧
        air.cols.opcode_selector.is_bltu row 0 = (if (op == .BLTU) then 1 else 0) ∧
        air.cols.opcode_selector.is_bgeu row 0 = (if (op == .BGEU) then 1 else 0) ∧
        air.cols.opcode_selector.is_jalr row 0 = 0 ∧
        air.cols.opcode_selector.is_jal row 0 = 0 ∧
        air.cols.opcode_selector.is_auipc row 0 = 0 ∧
        air.cols.opcode_selector.is_unimpl row 0 = 0)
      (h_reg_rs1 : (air.cols.instruction.op_a_0 row 0).val < 32)
      (h_reg_rs2 : (air.cols.instruction.op_b_0 row 0).val < 32)
    :
      Sail.readReg Register.PC state =
        EStateM.Result.ok
          (BitVec.ofNatLT (w := 64)
            (↑(air.cols.pc_0 row 0) + 65536 * ↑(air.cols.pc_1 row 0) +
             4294967296 * ↑(air.cols.pc_2 row 0))
            (by
              have := (air.cols.pc_0 row 0).isLt
              have := (air.cols.pc_1 row 0).isLt
              have := (air.cols.pc_2 row 0).isLt
              omega))
          state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_b_0 row 0))))
          state =
        EStateM.Result.ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg
          (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0))))
          state =
        EStateM.Result.ok
          (U64w.toBV
            #v[ air.cols.op_a_access.prev_value_0 row 0,
                air.cols.op_a_access.prev_value_1 row 0,
                air.cols.op_a_access.prev_value_2 row 0,
                air.cols.op_a_access.prev_value_3 row 0 ])
          state
    := by
      cases op <;>
        ( simp [
            CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors, h_imm_b, h_imm_c,
            h_reg_rs1, h_reg_rs2, Transpiler.opcode_of_bop
          ] at h_bus_hypotheses
          rw [operation_list_effect_hypotheses_writeReg_same (by simp [h_bus_hypotheses])] at h_bus_hypotheses; simp at h_bus_hypotheses
          obtain ⟨ h_pc, h_reg2, h_reg1, _ ⟩ := h_bus_hypotheses
          simp [BitVec.ofNatLT_eq_ofNat] at h_reg2 h_reg1
          refine ⟨ h_pc, ?_, h_reg1 ⟩
          simp only [op_b_value]; exact h_reg2 )

    /-- Equivalence for BEQ (opcode 18, `instruction.BTYPE (imm, rs2, rs1, .BEQ)`).
    Probe equivalence for the BTYPE class. Inlines the per-branch witness
    `op_a == op_b ↔ branching = 1` via c45/c46 + c53-c56 + `specific_0`. -/
    theorem equivalence_BEQ
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 18)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BEQ)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses + pull common chip-side facts.
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      -- Phase 2: BTYPE operand extraction (class-level).
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs1, h_reg_rs2, _h_imm_mod_2 ⟩ :=
        btype_operand_setup air row h_row h_is_real (by grind) .BEQ
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
      -- Phase 3: branch_sum = 1; pull branching active constraints + ALU lookups.
      have h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 +
          air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 +
          air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 +
          air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        simp [h_selectors]
      have branch_constraints := is_branching_active_constraints air row h_row h_is_real
                                  (by grind) h_branch_sum h_constraints
      have h_npc_branching := branching_next_pc_eq_pc_plus_op_c air row h_is_real (by grind)
      have h_lt := branch_instruction_a_lt_b air row h_is_real (by grind) h_branch_sum
      have h_gt := branch_instruction_a_gt_b air row h_is_real (by grind) h_branch_sum
      -- Phase 4: C-value bridge — op_c stores `signExtend 64 imm'`.
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      -- Phase 5: BTYPE bus extraction (class-level).
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ :=
        btype_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .BEQ
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rs1 h_reg_rs2
      -- Phase 6: op_a value = prev_value (branches don't write rd).
      have h_prev_eq : U64w.toBV (op_a_value air row) =
                      U64w.toBV #v[ air.cols.op_a_access.prev_value_0 row 0,
                                    air.cols.op_a_access.prev_value_1 row 0,
                                    air.cols.op_a_access.prev_value_2 row 0,
                                    air.cols.op_a_access.prev_value_3 row 0 ] := by
        obtain ⟨h_p0, h_p1, h_p2, h_p3, _⟩ := branch_constraints
        simp only [op_a_value]
        rw [h_p0, h_p1, h_p2, h_p3]
      -- Phase 7: inline `h_eq_branching` — chip's `branching` flag tracks `op_a == op_b`.
      -- Uses c45 (branching = 1 → specific_0 = 1), c46 (branching = 0 → specific_1 + specific_2 = 1),
      -- c53-c56 (specific_0 = 1 → op_a == op_b per limb), and the LT/GT comparison witnesses.
      have h_is_beq : air.cols.opcode_selector.is_beq row 0 = 1 := by simp [h_selectors]
      have h_b_branching :
          air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1 :=
        branch_constraints.2.2.2.2.1
      have h_eq_branching :
          U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row) ↔
          air.cols.branching row 0 = 1 := by
        obtain ⟨ h_c45, h_c46, h_c53, h_c54, h_c55, h_c56 ⟩
          : constraint_45 air row ∧ constraint_46 air row ∧
            constraint_53 air row ∧ constraint_54 air row ∧
            constraint_55 air row ∧ constraint_56 air row := by
          rw [allHold_iff_allHold_simplified] at h_constraints
          simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
          clear *- h_constraints; aesop
        simp [constraint_and_interaction_simplification, h_is_beq, h_selectors, sub_eq_zero,
              mul_eq_zero, one_mul] at h_c45 h_c46 h_c53 h_c54 h_c55 h_c56
        simp [h_selectors] at h_lt h_gt
        simp only [op_a_value, op_b_value]
        constructor
        . -- op_a == op_b → branching = 1
          intro h_eq; simp [← BitVec.toNat_inj] at h_eq
          rw [if_neg (by omega)] at h_lt; rw [if_neg (by omega)] at h_gt
          simp [h_lt, h_gt] at h_c46
          assumption
        . -- branching = 1 → op_a == op_b (via c53-c56 with specific_0 = 1 from c45)
          intro h_b
          simp [h_b] at h_c45
          simp [h_c45] at h_c53 h_c54 h_c55 h_c56
          rw [← BitVec.toNat_inj, U64w.toBV_toNat, U64w.toBV_toNat, U64w.toNat, U64w.toNat]
          grind
      -- Phase 8: apply execute_BEQ_equiv.
      extract_lets reg1 reg2 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_BEQ_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_a_value air row))
        (r2_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
      ]
      -- Phase 9: state equality.
      . simp [
          OpcodeSpec.RV64.spec_BEQ,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row, BitVec.ofNatLT_eq_ofNat,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rs1, h_reg_rs2,
        ]
        simp [op_b_value] at h_reg2
        subst reg1 reg2
        rw [operation_list_effect_state_writeReg_same (by simp [← h_reg2])]; simp
        rw [operation_list_effect_state_writeReg_same (by simp [h_reg1, branch_constraints])]
        -- Dispatch on `r1 == r2`, using h_eq_branching to convert to `branching`.
        by_cases h_eq : U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
        . -- Equal: branch taken (branching = 1), next_pc = pc + signExtend 64 imm'.
          have h_branching := h_eq_branching.mp h_eq
          have h_next_pc := h_npc_branching h_branching
          simp [h_eq, h_next_pc, h_op_c_bv]
        . -- Not equal: not branching, next_pc = pc + 4.
          have h_not_branching : air.cols.not_branching row 0 = 1 := by
            rcases h_b_branching with h | h
            . obtain ⟨_, _, _, _, _, h_not_b_bool, h_sum, _⟩ := branch_constraints
              rcases h_not_b_bool with h_nb | h_nb
              . exfalso
                have : air.cols.branching row 0 + air.cols.not_branching row 0 = 0 := by
                  simp [h, h_nb]
                grind
              . exact h_nb
            . exfalso; exact h_eq (h_eq_branching.mpr h)
          have h_next_pc := branch_constraints.2.2.2.2.2.2.2.2 h_not_branching
          simp [h_eq, h_next_pc]
      -- Phase 10: PC read condition.
      . simp [OpcodeSpec.RV64.spec_BEQ]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [h_prev_eq, ← h_reg1]
        . subst reg2; simp [← h_reg2]
      -- Phase 11: h_success — when r1 == r2, target is 4-aligned.
      . intro h_eq
        have h_branching := h_eq_branching.mp h_eq
        have h_next_pc := h_npc_branching h_branching
        rw [BitVec.mod_4_zero_equiv_64]
        rw [show U64w.toBV (pc air row) + BitVec.signExtend 64 imm' =
              U64w.toBV (next_pc air row) from by rw [h_next_pc, h_op_c_bv]]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind

    /-- Equivalence for BNE (opcode 19, `instruction.BTYPE (imm, rs2, rs1, .BNE)`).
    Mirrors `equivalence_BEQ` but with the inequality witness — `op_a ≠ op_b ↔
    branching = 1` — via c47/c48 + c53-c56. -/
    theorem equivalence_BNE
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 19)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BNE)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs1, h_reg_rs2, _h_imm_mod_2 ⟩ :=
        btype_operand_setup air row h_row h_is_real (by grind) .BNE
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
      have h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 +
          air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 +
          air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 +
          air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        simp [h_selectors]
      have branch_constraints := is_branching_active_constraints air row h_row h_is_real
                                  (by grind) h_branch_sum h_constraints
      have h_npc_branching := branching_next_pc_eq_pc_plus_op_c air row h_is_real (by grind)
      have h_lt := branch_instruction_a_lt_b air row h_is_real (by grind) h_branch_sum
      have h_gt := branch_instruction_a_gt_b air row h_is_real (by grind) h_branch_sum
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ :=
        btype_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .BNE
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rs1 h_reg_rs2
      have h_prev_eq : U64w.toBV (op_a_value air row) =
                      U64w.toBV #v[ air.cols.op_a_access.prev_value_0 row 0,
                                    air.cols.op_a_access.prev_value_1 row 0,
                                    air.cols.op_a_access.prev_value_2 row 0,
                                    air.cols.op_a_access.prev_value_3 row 0 ] := by
        obtain ⟨h_p0, h_p1, h_p2, h_p3, _⟩ := branch_constraints
        simp only [op_a_value]
        rw [h_p0, h_p1, h_p2, h_p3]
      have h_is_bne : air.cols.opcode_selector.is_bne row 0 = 1 := by simp [h_selectors]
      have h_b_branching :
          air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1 :=
        branch_constraints.2.2.2.2.1
      have h_eq_branching :
          U64w.toBV (op_a_value air row) ≠ U64w.toBV (op_b_value air row) ↔
          air.cols.branching row 0 = 1 := by
        obtain ⟨ h_c47, h_c48, h_c53, h_c54, h_c55, h_c56 ⟩
          : constraint_47 air row ∧ constraint_48 air row ∧
            constraint_53 air row ∧ constraint_54 air row ∧
            constraint_55 air row ∧ constraint_56 air row := by
          rw [allHold_iff_allHold_simplified] at h_constraints
          simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
          clear *- h_constraints; aesop
        simp [constraint_and_interaction_simplification, h_is_bne, h_selectors, sub_eq_zero,
              mul_eq_zero, one_mul] at h_c47 h_c48 h_c53 h_c54 h_c55 h_c56
        simp [h_selectors] at h_lt h_gt
        simp only [op_a_value, op_b_value]
        constructor
        . -- op_a ≠ op_b → branching = 1: rule out specific_0 = 1 via c53-c56.
          intro h_neq
          rcases h_c48 with h_b | h_s0
          . exact h_b
          . exfalso
            apply h_neq
            simp [h_s0] at h_c53 h_c54 h_c55 h_c56
            rw [← BitVec.toNat_inj, U64w.toBV_toNat, U64w.toBV_toNat, U64w.toNat, U64w.toNat]
            grind
        . -- branching = 1 → op_a ≠ op_b: from c47 s1+s2=1, h_lt/h_gt rule out equality.
          intro h_b h_eq
          simp [h_b] at h_c47
          simp [← BitVec.toNat_inj] at h_eq
          rw [if_neg (by omega)] at h_lt; rw [if_neg (by omega)] at h_gt
          simp [h_lt, h_gt] at h_c47
      extract_lets reg1 reg2 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_BNE_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_a_value air row))
        (r2_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
      ]
      . simp [
          OpcodeSpec.RV64.spec_BNE,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row, BitVec.ofNatLT_eq_ofNat,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rs1, h_reg_rs2,
        ]
        simp [op_b_value] at h_reg2
        subst reg1 reg2
        rw [operation_list_effect_state_writeReg_same (by simp [← h_reg2])]; simp
        rw [operation_list_effect_state_writeReg_same (by simp [h_reg1, branch_constraints])]
        by_cases h_eq : U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
        . -- Equal: NOT taken for BNE (increment = 4).
          have h_not_branching : air.cols.not_branching row 0 = 1 := by
            rcases h_b_branching with h | h
            . obtain ⟨_, _, _, _, _, h_not_b_bool, h_sum, _⟩ := branch_constraints
              rcases h_not_b_bool with h_nb | h_nb
              . exfalso
                have : air.cols.branching row 0 + air.cols.not_branching row 0 = 0 := by
                  simp [h, h_nb]
                grind
              . exact h_nb
            . exfalso; exact (h_eq_branching.mpr h) h_eq
          have h_next_pc := branch_constraints.2.2.2.2.2.2.2.2 h_not_branching
          simp [h_eq, h_next_pc]
        . -- Not equal: taken for BNE (increment = signExtend imm').
          have h_branching := h_eq_branching.mp h_eq
          have h_next_pc := h_npc_branching h_branching
          simp [h_eq, h_next_pc, h_op_c_bv]
      . simp [OpcodeSpec.RV64.spec_BNE]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [h_prev_eq, ← h_reg1]
        . subst reg2; simp [← h_reg2]
      . intro h_neq
        have h_branching := h_eq_branching.mp h_neq
        have h_next_pc := h_npc_branching h_branching
        rw [BitVec.mod_4_zero_equiv_64]
        rw [show U64w.toBV (pc air row) + BitVec.signExtend 64 imm' =
              U64w.toBV (next_pc air row) from by rw [h_next_pc, h_op_c_bv]]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind

    /-- Equivalence for BLT (opcode 20, signed less-than).
    `op_a.toInt < op_b.toInt ↔ branching = 1` via c49/c50 + signed comparison
    (`h_lt`/`h_gt` with `is_blt = 1` selects the `.toInt` arm of
    `branch_instruction_a_lt_b`). -/
    theorem equivalence_BLT
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 20)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs1, h_reg_rs2, _h_imm_mod_2 ⟩ :=
        btype_operand_setup air row h_row h_is_real (by grind) .BLT
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
      have h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 +
          air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 +
          air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 +
          air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        simp [h_selectors]
      have branch_constraints := is_branching_active_constraints air row h_row h_is_real
                                  (by grind) h_branch_sum h_constraints
      have h_npc_branching := branching_next_pc_eq_pc_plus_op_c air row h_is_real (by grind)
      have h_lt := branch_instruction_a_lt_b air row h_is_real (by grind) h_branch_sum
      have h_gt := branch_instruction_a_gt_b air row h_is_real (by grind) h_branch_sum
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ :=
        btype_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .BLT
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rs1 h_reg_rs2
      have h_prev_eq : U64w.toBV (op_a_value air row) =
                      U64w.toBV #v[ air.cols.op_a_access.prev_value_0 row 0,
                                    air.cols.op_a_access.prev_value_1 row 0,
                                    air.cols.op_a_access.prev_value_2 row 0,
                                    air.cols.op_a_access.prev_value_3 row 0 ] := by
        obtain ⟨h_p0, h_p1, h_p2, h_p3, _⟩ := branch_constraints
        simp only [op_a_value]
        rw [h_p0, h_p1, h_p2, h_p3]
      have h_is_blt : air.cols.opcode_selector.is_blt row 0 = 1 := by simp [h_selectors]
      have h_b_branching :
          air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1 :=
        branch_constraints.2.2.2.2.1
      have h_eq_branching :
          U64w.toInt (op_a_value air row) < U64w.toInt (op_b_value air row) ↔
          air.cols.branching row 0 = 1 := by
        obtain ⟨ h_c49, h_c50, h_c53, h_c54, h_c55, h_c56 ⟩
          : constraint_49 air row ∧ constraint_50 air row ∧
            constraint_53 air row ∧ constraint_54 air row ∧
            constraint_55 air row ∧ constraint_56 air row := by
          rw [allHold_iff_allHold_simplified] at h_constraints
          simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
          clear *- h_constraints; aesop
        simp [constraint_and_interaction_simplification, h_is_blt, h_selectors, sub_eq_zero,
              mul_eq_zero, one_mul] at h_c49 h_c50 h_c53 h_c54 h_c55 h_c56
        simp [h_selectors] at h_lt h_gt
        simp only [op_a_value, op_b_value]
        constructor
        . intro h_a_lt_b
          rw [if_pos h_a_lt_b] at h_lt
          rw [if_neg (by clear *- h_a_lt_b; omega)] at h_gt
          rcases h_c50 with h_b | h_s
          . exact h_b
          . exfalso
            simp [h_gt] at h_s
            simp [h_s] at h_c53 h_c54 h_c55 h_c56
            rw [h_c53, h_c54, h_c55, h_c56] at h_a_lt_b; clear *- h_a_lt_b; omega
        . intro h_b
          rcases h_c49 with h_b0 | h_s2
          . simp [h_b0] at h_b
          . simp [h_s2] at h_lt
            assumption
      extract_lets reg1 reg2 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_BLT_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_a_value air row))
        (r2_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
      ]
      . simp [
          OpcodeSpec.RV64.spec_BLT,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row, BitVec.ofNatLT_eq_ofNat,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rs1, h_reg_rs2,
        ]
        simp [op_b_value] at h_reg2
        subst reg1 reg2
        rw [operation_list_effect_state_writeReg_same (by simp [← h_reg2])]; simp
        rw [operation_list_effect_state_writeReg_same (by simp [h_reg1, branch_constraints])]
        by_cases h_lt_cond : U64w.toInt (op_a_value air row) <
                              U64w.toInt (op_b_value air row)
        . have h_branching := h_eq_branching.mp h_lt_cond
          have h_next_pc := h_npc_branching h_branching
          simp [h_lt_cond, h_next_pc, h_op_c_bv]
        . have h_not_branching : air.cols.not_branching row 0 = 1 := by
            rcases h_b_branching with h | h
            . obtain ⟨_, _, _, _, _, h_not_b_bool, h_sum, _⟩ := branch_constraints
              rcases h_not_b_bool with h_nb | h_nb
              . exfalso
                have : air.cols.branching row 0 + air.cols.not_branching row 0 = 0 := by
                  simp [h, h_nb]
                grind
              . exact h_nb
            . exfalso; exact h_lt_cond (h_eq_branching.mpr h)
          have h_next_pc := branch_constraints.2.2.2.2.2.2.2.2 h_not_branching
          simp [h_lt_cond, h_next_pc]
      . simp [OpcodeSpec.RV64.spec_BLT]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [h_prev_eq, ← h_reg1]
        . subst reg2; simp [← h_reg2]
      . intro h_lt_cond; simp at h_lt_cond
        have h_branching := h_eq_branching.mp h_lt_cond
        have h_next_pc := h_npc_branching h_branching
        rw [BitVec.mod_4_zero_equiv_64]
        rw [show U64w.toBV (pc air row) + BitVec.signExtend 64 imm' =
              U64w.toBV (next_pc air row) from by rw [h_next_pc, h_op_c_bv]]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind

    /-- Equivalence for BGE (opcode 21, signed greater-or-equal).
    `op_a.toInt ≥ op_b.toInt ↔ branching = 1` via c51/c52 + signed comparison. -/
    theorem equivalence_BGE
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 21)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BGE)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs1, h_reg_rs2, _h_imm_mod_2 ⟩ :=
        btype_operand_setup air row h_row h_is_real (by grind) .BGE
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
      have h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 +
          air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 +
          air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 +
          air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        simp [h_selectors]
      have branch_constraints := is_branching_active_constraints air row h_row h_is_real
                                  (by grind) h_branch_sum h_constraints
      have h_npc_branching := branching_next_pc_eq_pc_plus_op_c air row h_is_real (by grind)
      have h_lt := branch_instruction_a_lt_b air row h_is_real (by grind) h_branch_sum
      have h_gt := branch_instruction_a_gt_b air row h_is_real (by grind) h_branch_sum
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ :=
        btype_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .BGE
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rs1 h_reg_rs2
      have h_prev_eq : U64w.toBV (op_a_value air row) =
                      U64w.toBV #v[ air.cols.op_a_access.prev_value_0 row 0,
                                    air.cols.op_a_access.prev_value_1 row 0,
                                    air.cols.op_a_access.prev_value_2 row 0,
                                    air.cols.op_a_access.prev_value_3 row 0 ] := by
        obtain ⟨h_p0, h_p1, h_p2, h_p3, _⟩ := branch_constraints
        simp only [op_a_value]
        rw [h_p0, h_p1, h_p2, h_p3]
      have h_is_bge : air.cols.opcode_selector.is_bge row 0 = 1 := by simp [h_selectors]
      have h_b_branching :
          air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1 :=
        branch_constraints.2.2.2.2.1
      have h_eq_branching :
          U64w.toInt (op_a_value air row) ≥ U64w.toInt (op_b_value air row) ↔
          air.cols.branching row 0 = 1 := by
        obtain ⟨ h_c51, h_c52, h_c53, h_c54, h_c55, h_c56 ⟩
          : constraint_51 air row ∧ constraint_52 air row ∧
            constraint_53 air row ∧ constraint_54 air row ∧
            constraint_55 air row ∧ constraint_56 air row := by
          rw [allHold_iff_allHold_simplified] at h_constraints
          simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
          clear *- h_constraints; aesop
        simp [constraint_and_interaction_simplification, h_is_bge, h_selectors, sub_eq_zero,
              mul_eq_zero, one_mul] at h_c51 h_c52 h_c53 h_c54 h_c55 h_c56
        simp [h_selectors] at h_lt h_gt
        simp only [op_a_value, op_b_value]
        constructor
        . intro h_a_ge_b
          rcases h_c52 with h_b0 | h_s2
          . rcases h_b_branching with h | h
            . exfalso; simp [h] at h_b0
            . exact h
          . exfalso
            simp [h_s2] at h_lt
            simp at h_a_ge_b
            clear *- h_lt h_a_ge_b
            omega
        . intro h_b
          simp [h_b] at h_c51
          split_ifs at h_lt with h_lt_if
          . split_ifs at h_gt with h_gt_if
            . clear *- h_gt_if; omega
            . simp [h_gt] at h_c51
              simp [h_c51] at h_c53 h_c54 h_c55 h_c56
              simp [h_c53, h_c54, h_c55, h_c56]
          . clear *- h_lt_if; omega
      extract_lets reg1 reg2 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_BGE_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_a_value air row))
        (r2_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
      ]
      . simp [
          OpcodeSpec.RV64.spec_BGE,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row, BitVec.ofNatLT_eq_ofNat,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rs1, h_reg_rs2,
        ]
        simp [op_b_value] at h_reg2
        subst reg1 reg2
        rw [operation_list_effect_state_writeReg_same (by simp [← h_reg2])]; simp
        rw [operation_list_effect_state_writeReg_same (by simp [h_reg1, branch_constraints])]
        by_cases h_ge_cond : U64w.toInt (op_a_value air row) ≥
                              U64w.toInt (op_b_value air row)
        . have h_branching := h_eq_branching.mp h_ge_cond
          have h_next_pc := h_npc_branching h_branching
          simp [h_ge_cond, h_next_pc, h_op_c_bv]
        . have h_not_branching : air.cols.not_branching row 0 = 1 := by
            rcases h_b_branching with h | h
            . obtain ⟨_, _, _, _, _, h_not_b_bool, h_sum, _⟩ := branch_constraints
              rcases h_not_b_bool with h_nb | h_nb
              . exfalso
                have : air.cols.branching row 0 + air.cols.not_branching row 0 = 0 := by
                  simp [h, h_nb]
                grind
              . exact h_nb
            . exfalso; exact h_ge_cond (h_eq_branching.mpr h)
          have h_next_pc := branch_constraints.2.2.2.2.2.2.2.2 h_not_branching
          rw [if_neg (by clear *- h_ge_cond; simp at h_ge_cond; omega)]
          simp [h_next_pc]
      . simp [OpcodeSpec.RV64.spec_BGE]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [h_prev_eq, ← h_reg1]
        . subst reg2; simp [← h_reg2]
      . intro h_ge_cond; simp at h_ge_cond
        have h_branching := h_eq_branching.mp h_ge_cond
        have h_next_pc := h_npc_branching h_branching
        rw [BitVec.mod_4_zero_equiv_64]
        rw [show U64w.toBV (pc air row) + BitVec.signExtend 64 imm' =
              U64w.toBV (next_pc air row) from by rw [h_next_pc, h_op_c_bv]]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind

    /-- Equivalence for BLTU (opcode 22, unsigned less-than).
    `op_a.toNat < op_b.toNat ↔ branching = 1` via c49/c50 + unsigned comparison
    (`is_blt + is_bge = 0` selects the `.toNat` arm). -/
    theorem equivalence_BLTU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 22)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs1, h_reg_rs2, _h_imm_mod_2 ⟩ :=
        btype_operand_setup air row h_row h_is_real (by grind) .BLTU
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
      have h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 +
          air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 +
          air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 +
          air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        simp [h_selectors]
      have branch_constraints := is_branching_active_constraints air row h_row h_is_real
                                  (by grind) h_branch_sum h_constraints
      have h_npc_branching := branching_next_pc_eq_pc_plus_op_c air row h_is_real (by grind)
      have h_lt := branch_instruction_a_lt_b air row h_is_real (by grind) h_branch_sum
      have h_gt := branch_instruction_a_gt_b air row h_is_real (by grind) h_branch_sum
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ :=
        btype_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .BLTU
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rs1 h_reg_rs2
      have h_prev_eq : U64w.toBV (op_a_value air row) =
                      U64w.toBV #v[ air.cols.op_a_access.prev_value_0 row 0,
                                    air.cols.op_a_access.prev_value_1 row 0,
                                    air.cols.op_a_access.prev_value_2 row 0,
                                    air.cols.op_a_access.prev_value_3 row 0 ] := by
        obtain ⟨h_p0, h_p1, h_p2, h_p3, _⟩ := branch_constraints
        simp only [op_a_value]
        rw [h_p0, h_p1, h_p2, h_p3]
      have h_is_bltu : air.cols.opcode_selector.is_bltu row 0 = 1 := by simp [h_selectors]
      have h_b_branching :
          air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1 :=
        branch_constraints.2.2.2.2.1
      have h_eq_branching :
          U64w.toNat (op_a_value air row) < U64w.toNat (op_b_value air row) ↔
          air.cols.branching row 0 = 1 := by
        obtain ⟨ h_c49, h_c50, h_c53, h_c54, h_c55, h_c56 ⟩
          : constraint_49 air row ∧ constraint_50 air row ∧
            constraint_53 air row ∧ constraint_54 air row ∧
            constraint_55 air row ∧ constraint_56 air row := by
          rw [allHold_iff_allHold_simplified] at h_constraints
          simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
          clear *- h_constraints; aesop
        simp [constraint_and_interaction_simplification, h_is_bltu, h_selectors, sub_eq_zero,
              mul_eq_zero, one_mul] at h_c49 h_c50 h_c53 h_c54 h_c55 h_c56
        simp [h_selectors] at h_lt h_gt
        simp only [op_a_value, op_b_value]
        constructor
        . intro h_a_lt_b
          rw [if_pos h_a_lt_b] at h_lt
          have h_not_b_lt_a : ¬ (U64w.toNat (op_b_value air row) <
                                 U64w.toNat (op_a_value air row)) := by
            simp only [op_a_value, op_b_value] at *; omega
          rw [if_neg (by omega)] at h_gt
          rcases h_c50 with h_b | h_s
          . exact h_b
          . exfalso
            simp [h_gt] at h_s
            simp [h_s] at h_c53 h_c54 h_c55 h_c56
            have h_eq_toNat :
              U64w.toNat (op_a_value air row) = U64w.toNat (op_b_value air row) := by
              simp only [op_a_value, op_b_value]
              rw [U64w.toNat, U64w.toNat]
              grind
            simp only [op_a_value, op_b_value] at *; omega
        . intro h_b
          rcases h_c49 with h_b0 | h_s2
          . simp [h_b0] at h_b
          . simp [h_s2] at h_lt
            assumption
      extract_lets reg1 reg2 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_BLTU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_a_value air row))
        (r2_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
      ]
      . simp [
          OpcodeSpec.RV64.spec_BLTU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row, BitVec.ofNatLT_eq_ofNat,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rs1, h_reg_rs2,
        ]
        simp [op_b_value] at h_reg2
        subst reg1 reg2
        rw [operation_list_effect_state_writeReg_same (by simp [← h_reg2])]; simp
        rw [operation_list_effect_state_writeReg_same (by simp [h_reg1, branch_constraints])]
        by_cases h_lt_cond : U64w.toNat (op_a_value air row) <
                              U64w.toNat (op_b_value air row)
        . have h_branching := h_eq_branching.mp h_lt_cond
          have h_next_pc := h_npc_branching h_branching
          simp [h_lt_cond, h_next_pc, h_op_c_bv]
        . have h_not_branching : air.cols.not_branching row 0 = 1 := by
            rcases h_b_branching with h | h
            . obtain ⟨_, _, _, _, _, h_not_b_bool, h_sum, _⟩ := branch_constraints
              rcases h_not_b_bool with h_nb | h_nb
              . exfalso
                have : air.cols.branching row 0 + air.cols.not_branching row 0 = 0 := by
                  simp [h, h_nb]
                grind
              . exact h_nb
            . exfalso; exact h_lt_cond (h_eq_branching.mpr h)
          have h_next_pc := branch_constraints.2.2.2.2.2.2.2.2 h_not_branching
          simp [h_lt_cond, h_next_pc]
      . simp [OpcodeSpec.RV64.spec_BLTU]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [h_prev_eq, ← h_reg1]
        . subst reg2; simp [← h_reg2]
      . intro h_lt_cond; simp at h_lt_cond
        have h_branching := h_eq_branching.mp h_lt_cond
        have h_next_pc := h_npc_branching h_branching
        rw [BitVec.mod_4_zero_equiv_64]
        rw [show U64w.toBV (pc air row) + BitVec.signExtend 64 imm' =
              U64w.toBV (next_pc air row) from by rw [h_next_pc, h_op_c_bv]]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind

    /-- Equivalence for BGEU (opcode 23, unsigned greater-or-equal).
    `op_a.toNat ≥ op_b.toNat ↔ branching = 1` via c51/c52 + unsigned comparison. -/
    theorem equivalence_BGEU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 23)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BGEU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_constraints
      have h_npc_mod4 := next_pc_mod_four_eq_zero air (by grind) (by grind) (by grind)
                          row h_row h_is_real pico_assumptions
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs1, h_reg_rs2, _h_imm_mod_2 ⟩ :=
        btype_operand_setup air row h_row h_is_real (by grind) .BGEU
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
      have h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 +
          air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 +
          air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 +
          air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        simp [h_selectors]
      have branch_constraints := is_branching_active_constraints air row h_row h_is_real
                                  (by grind) h_branch_sum h_constraints
      have h_npc_branching := branching_next_pc_eq_pc_plus_op_c air row h_is_real (by grind)
      have h_lt := branch_instruction_a_lt_b air row h_is_real (by grind) h_branch_sum
      have h_gt := branch_instruction_a_gt_b air row h_is_real (by grind) h_branch_sum
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      obtain ⟨ h_pc, h_reg2, h_reg1 ⟩ :=
        btype_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .BGEU
          (by simp [Transpiler.opcode_of_bop]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rs1 h_reg_rs2
      have h_prev_eq : U64w.toBV (op_a_value air row) =
                      U64w.toBV #v[ air.cols.op_a_access.prev_value_0 row 0,
                                    air.cols.op_a_access.prev_value_1 row 0,
                                    air.cols.op_a_access.prev_value_2 row 0,
                                    air.cols.op_a_access.prev_value_3 row 0 ] := by
        obtain ⟨h_p0, h_p1, h_p2, h_p3, _⟩ := branch_constraints
        simp only [op_a_value]
        rw [h_p0, h_p1, h_p2, h_p3]
      have h_is_bgeu : air.cols.opcode_selector.is_bgeu row 0 = 1 := by simp [h_selectors]
      have h_b_branching :
          air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1 :=
        branch_constraints.2.2.2.2.1
      have h_eq_branching :
          (U64w.toNat (op_a_value air row)) ≥ (U64w.toNat (op_b_value air row)) ↔
          air.cols.branching row 0 = 1 := by
        obtain ⟨ h_c51, h_c52, h_c53, h_c54, h_c55, h_c56 ⟩
          : constraint_51 air row ∧ constraint_52 air row ∧
            constraint_53 air row ∧ constraint_54 air row ∧
            constraint_55 air row ∧ constraint_56 air row := by
          rw [allHold_iff_allHold_simplified] at h_constraints
          simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
          clear *- h_constraints; aesop
        simp [constraint_and_interaction_simplification, h_is_bgeu, h_selectors, sub_eq_zero,
              mul_eq_zero, one_mul] at h_c51 h_c52 h_c53 h_c54 h_c55 h_c56
        simp [h_selectors] at h_lt h_gt
        simp only [op_a_value, op_b_value]
        constructor
        . intro h_a_ge_b
          rcases h_c52 with h_b0 | h_s2
          . rcases h_b_branching with h | h
            . exfalso; simp [h] at h_b0
            . exact h
          . exfalso
            simp [h_s2] at h_lt
            simp at h_a_ge_b
            omega
        . intro h_b
          rcases h_c51 with h_b0 | h_s
          . simp [h_b0] at h_b
          . by_contra h_not_ge
            simp at h_not_ge
            rw [if_pos h_not_ge] at h_lt
            have h_not_b_lt_a : ¬ ((U64w.toBV (op_b_value air row)).toNat <
                                   (U64w.toBV (op_a_value air row)).toNat) := by
              simp only [op_a_value, op_b_value] at *; simp; omega
            rw [if_neg (by omega)] at h_gt
            simp [h_gt] at h_s
            simp [h_s] at h_c53 h_c54 h_c55 h_c56
            have h_eq_toNat :
              (U64w.toBV (op_a_value air row)).toNat = (U64w.toBV (op_b_value air row)).toNat := by
              simp only [op_a_value, op_b_value]
              rw [U64w.toBV_toNat, U64w.toBV_toNat, U64w.toNat, U64w.toNat]
              grind
            simp only [op_a_value, op_b_value] at *; simp at h_eq_toNat; omega
      extract_lets reg1 reg2 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_BGEU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_a_value air row))
        (r2_val := U64w.toBV (op_b_value air row))
        (misa := misa)
        (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)
      ]
      . simp [
          OpcodeSpec.RV64.spec_BGEU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row, BitVec.ofNatLT_eq_ofNat,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rs1, h_reg_rs2,
        ]
        simp [op_b_value] at h_reg2
        subst reg1 reg2
        rw [operation_list_effect_state_writeReg_same (by simp [← h_reg2])]; simp
        rw [operation_list_effect_state_writeReg_same (by simp [h_reg1, branch_constraints])]
        by_cases h_ge_cond : (U64w.toNat (op_a_value air row)) ≥
                              (U64w.toNat (op_b_value air row))
        . have h_branching := h_eq_branching.mp h_ge_cond
          have h_next_pc := h_npc_branching h_branching
          simp [h_ge_cond, h_next_pc, h_op_c_bv]
        . have h_not_branching : air.cols.not_branching row 0 = 1 := by
            rcases h_b_branching with h | h
            . obtain ⟨_, _, _, _, _, h_not_b_bool, h_sum, _⟩ := branch_constraints
              rcases h_not_b_bool with h_nb | h_nb
              . exfalso
                have : air.cols.branching row 0 + air.cols.not_branching row 0 = 0 := by
                  simp [h, h_nb]
                grind
              . exact h_nb
            . exfalso; exact h_ge_cond (h_eq_branching.mpr h)
          have h_next_pc := branch_constraints.2.2.2.2.2.2.2.2 h_not_branching
          rw [if_neg (by clear *- h_ge_cond; simp at h_ge_cond; omega)]
          simp [h_next_pc]
      . simp [OpcodeSpec.RV64.spec_BGEU]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega
        . subst reg1; simp [h_prev_eq, ← h_reg1]
        . subst reg2; simp [← h_reg2]
      . intro h_ge_cond; simp at h_ge_cond
        have h_branching := h_eq_branching.mp h_ge_cond
        have h_next_pc := h_npc_branching h_branching
        rw [BitVec.mod_4_zero_equiv_64]
        rw [show U64w.toBV (pc air row) + BitVec.signExtend 64 imm' =
              U64w.toBV (next_pc air row) from by rw [h_next_pc, h_op_c_bv]]
        have h_npc0_lt := (air.cols.next_pc_0 row 0).isLt
        have h_npc1_lt := (air.cols.next_pc_1 row 0).isLt
        have h_npc2_lt := (air.cols.next_pc_2 row 0).isLt
        simp [next_pc, U64w.toBV]
        repeat (rw [BitVec.getElem_append]; simp)
        simp [BitVec.getElem_eq_testBit_toNat]
        clear *- h_npc_mod4
        grind

  end BTYPE

  section STORES

    -- ========================================================================
    -- STORES — SB / SH / SW / SD instructions.
    -- Chip encoding (Transpiler.lean:520):
    --   * opcode ∈ {15, 16, 17, 47} for SB, SH, SW, SD respectively
    --   * imm_b = 0, imm_c = 1 (op_c holds the 12-bit immediate, sign-extended)
    --   * op_a stores rs2 (the data source register index), value column
    --     holds rs2's actual value (= prev_value, since stores don't write rd)
    --   * op_b stores rs1 (base address register index), value column holds
    --     rs1's value
    --   * exactly one of `is_sb`/`is_sh`/`is_sw`/`is_sd` is 1 (`store_sum = 1`).
    -- Helpers used:
    --   * `is_store_active_constraints` — `next_pc = pc + 4`, op_a unchanged.
    --   * `imm_c_eq_1_constraints` (c4-c7) — op_c stores the immediate
    --     (sign-extended via `Transpiler.imm_to_KB`).
    --   * `MemoryBus.Spec` — gives `addr < Pico_address_space_size_64` and
    --     alignment for SH/SW/SD.
    -- ========================================================================

    /-- Operand-setup lemma for the STORE class. Returns the 12-bit immediate,
    rs2 (data), rs1 (base), the chip's column equations, the imm_b=0/imm_c=1
    flags, the specific-store selectors, and the two reg bounds. The `width`
    parameter is one of 1, 2, 4, 8. -/
    lemma store_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (mw : Nat)
      (h_mw : mw = 1 ∨ mw = 2 ∨ mw = 4 ∨ mw = 8)
      (h_opcode : air.cols.instruction.opcode row 0 =
        (match mw with | 1 => 15 | 2 => 16 | 4 => 17 | 8 => 47 | _ => 0))
    :
      ∃ (imm : BitVec 12) (rs2 rs1 : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rs2 ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = (Transpiler.imm_to_KB imm true)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.imm_to_KB imm true)[1] ∧
        air.cols.instruction.op_c_2 row 0 = (Transpiler.imm_to_KB imm true)[2] ∧
        air.cols.instruction.op_c_3 row 0 = (Transpiler.imm_to_KB imm true)[3] ∧
        air.cols.instruction.op_a_is_x0 row 0 = 0 ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        air.cols.opcode_selector.imm_c row 0 = 1 ∧
        (air.cols.opcode_selector.is_alu row 0 = 0 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = 0 ∧
         air.cols.opcode_selector.is_lbu row 0 = 0 ∧
         air.cols.opcode_selector.is_lh row 0 = 0 ∧
         air.cols.opcode_selector.is_lhu row 0 = 0 ∧
         air.cols.opcode_selector.is_lw row 0 = 0 ∧
         air.cols.opcode_selector.is_lwu row 0 = 0 ∧
         air.cols.opcode_selector.is_ld row 0 = 0 ∧
         air.cols.opcode_selector.is_sb row 0 = (if mw = 1 then 1 else 0) ∧
         air.cols.opcode_selector.is_sh row 0 = (if mw = 2 then 1 else 0) ∧
         air.cols.opcode_selector.is_sw row 0 = (if mw = 4 then 1 else 0) ∧
         air.cols.opcode_selector.is_sd row 0 = (if mw = 8 then 1 else 0) ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32
    := by
      replace h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      rcases h_mw with h | h | h | h <;>
        ( subst h
          simp at h_opcode
          simp [h_opcode] at h_opcode_props
          obtain ⟨ imm, rs2, rs1, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ imm, rs2, rs1, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0] at h_eq_props
          obtain ⟨ h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rs1 h_reg_rs2
          refine ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3,
                   eq_a_is_x0,
                   eq_imm_b, eq_imm_c,
                   h_selectors,
                   h_reg_rs2, h_reg_rs1 ⟩ )

    /-- Equivalence for SB (opcode 15, `instruction.STORE (imm, rs2, rs1, 1)`).
    Probe equivalence for the STORE class. -/
    theorem equivalence_SB
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 15)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 1)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs2, h_reg_rs1 ⟩ :=
        store_operand_setup air row h_row h_is_real (by grind) 1
          (by left; rfl) (by simp; exact h_opcode)
      have h_store_sum :
        air.cols.opcode_selector.is_sb row 0 +
          air.cols.opcode_selector.is_sh row 0 +
          air.cols.opcode_selector.is_sw row 0 +
          air.cols.opcode_selector.is_sd row 0 = 1 := by
        simp [h_selectors]
      have store_constraints := is_store_active_constraints air row h_row h_is_real
                                  (by grind) h_store_sum h_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      -- Memory bus wf assumption.
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      -- Hypotheses: extract h_pc, h_rs1 (op_b read), h_rs2 (op_a read).
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c, eq_a_is_x0,
        h_reg_rs1, h_reg_rs2,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
      obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
      clear h_mem
      extract_lets rs2_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [show U64w.toBV (op_b_value air row) =
              U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                            air.cols.op_b_access.access.value_1 row 0,
                            air.cols.op_b_access.access.value_2 row 0,
                            air.cols.op_b_access.access.value_3 row 0 ] from rfl]
        rw [show BitVec.signExtend 64 imm' =
              U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                            air.cols.op_c_access.access.value_1 row 0,
                            air.cols.op_c_access.access.value_2 row 0,
                            air.cols.op_c_access.access.value_3 row 0 ] from by
              rw [← h_op_c_bv]]
        simp [BitVec.toNat_add]
        exact h_asm_mem.2
      rw [
        OpcodeSpec.RV64.execute_SB_equiv
        (r1 := rs1_let) (r2 := rs2_let) (imm := imm')
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_a_value air row))
        (state := state)
        (risc_v_assumptions := h_assumptions)
        (h_range := h_range)
      ]
      . -- Main goal: chip-side state == Sail spec_SB state.
        subst rs1_let rs2_let
        obtain ⟨ _, h_npc_eq, _, h_a0, h_a1, h_a2, h_a3 ⟩ := store_constraints
        have h_rs2' :
          read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0)))) state =
          EStateM.Result.ok (U64w.toBV
            #v[ air.cols.op_a_access.access.value_0 row 0,
                air.cols.op_a_access.access.value_1 row 0,
                air.cols.op_a_access.access.value_2 row 0,
                air.cols.op_a_access.access.value_3 row 0 ]) state := by
          simp only [h_a0, h_a1, h_a2, h_a3]; exact h_rs2
        simp [
          OpcodeSpec.RV64.spec_SB, CPU_bus_operations, bus_operations,
          deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors,
          eq_imm_b, eq_imm_c, eq_a_is_x0,
          h_reg_rs1, h_reg_rs2,
          BitVec.ofNatLT_eq_ofNat
        ]
        -- Filter out reads on RHS.
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        -- Drop the WriteReg op_b and op_a no-ops.
        rw [operation_list_effect_state_writeReg_same h_rs1]
        rw [operation_list_effect_state_writeReg_same h_rs2']
        have h_extract_eq : BitVec.extractLsb 7 0 (op_a_value air row).toBV = BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0)
        := by
          clear *-; simp [op_a_value, BitVec.extractLsb, U64w.toBV]
          repeat rw [BitVec.extractLsb'_append_eq_ite]
          simp [← BitVec.toNat_inj]
        simp [op_b_value, h_npc_eq, h_extract_eq]
        simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv]
        simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . -- Hypotheses: 3 reads (PC, rs1, rs2).
        rw [OpcodeSpec.RV64.spec_SB_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
        . subst rs1_let; simp [op_b_value]; exact h_rs1
        . subst rs2_let; simp [op_a_value, store_constraints]; exact h_rs2

    /-- Equivalence for SH (opcode 16, `instruction.STORE (imm, rs2, rs1, 2)`). -/
    theorem equivalence_SH
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 16)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 2)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs2, h_reg_rs1 ⟩ :=
        store_operand_setup air row h_row h_is_real (by grind) 2
          (by right; left; rfl) (by simp; exact h_opcode)
      have h_store_sum :
        air.cols.opcode_selector.is_sb row 0 +
          air.cols.opcode_selector.is_sh row 0 +
          air.cols.opcode_selector.is_sw row 0 +
          air.cols.opcode_selector.is_sd row 0 = 1 := by
        simp [h_selectors]
      have store_constraints := is_store_active_constraints air row h_row h_is_real
                                  (by grind) h_store_sum h_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c, eq_a_is_x0,
        h_reg_rs1, h_reg_rs2,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
      obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
      clear h_mem
      extract_lets rs2_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.1
      have h_align :
        (2 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2
      rw [
        OpcodeSpec.RV64.execute_SH_equiv
        (r1 := rs1_let) (r2 := rs2_let) (imm := imm')
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_a_value air row))
        (state := state)
        (risc_v_assumptions := h_assumptions)
        (h_range := h_range)
        (h_align := h_align)
      ]
      . -- Main goal: chip-side state == Sail spec_SH state.
        subst rs1_let rs2_let
        obtain ⟨ _, h_npc_eq, _, h_a0, h_a1, h_a2, h_a3 ⟩ := store_constraints
        have h_rs2' :
          read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0)))) state =
          EStateM.Result.ok (U64w.toBV
            #v[ air.cols.op_a_access.access.value_0 row 0,
                air.cols.op_a_access.access.value_1 row 0,
                air.cols.op_a_access.access.value_2 row 0,
                air.cols.op_a_access.access.value_3 row 0 ]) state := by
          simp only [h_a0, h_a1, h_a2, h_a3]; exact h_rs2
        simp [
          OpcodeSpec.RV64.spec_SH, CPU_bus_operations, bus_operations,
          deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors,
          eq_imm_b, eq_imm_c, eq_a_is_x0,
          h_reg_rs1, h_reg_rs2,
          BitVec.ofNatLT_eq_ofNat
        ]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        rw [operation_list_effect_state_writeReg_same h_rs1]
        rw [operation_list_effect_state_writeReg_same h_rs2']
        have h_extract_eq : BitVec.extractLsb 15 0 (op_a_value air row).toBV =
                            BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
        := by
          clear *-; simp [op_a_value, BitVec.extractLsb, U64w.toBV]
          repeat rw [BitVec.extractLsb'_append_eq_ite]
          simp
        simp [op_b_value, h_npc_eq, h_extract_eq]
        simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv]
        simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . rw [OpcodeSpec.RV64.spec_SH_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
        . subst rs1_let; simp [op_b_value]; exact h_rs1
        . subst rs2_let; simp [op_a_value, store_constraints]; exact h_rs2

    /-- Equivalence for SW (opcode 17, `instruction.STORE (imm, rs2, rs1, 4)`). -/
    theorem equivalence_SW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 17)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 4)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs2, h_reg_rs1 ⟩ :=
        store_operand_setup air row h_row h_is_real (by grind) 4
          (by right; right; left; rfl) (by simp; exact h_opcode)
      have h_store_sum :
        air.cols.opcode_selector.is_sb row 0 +
          air.cols.opcode_selector.is_sh row 0 +
          air.cols.opcode_selector.is_sw row 0 +
          air.cols.opcode_selector.is_sd row 0 = 1 := by
        simp [h_selectors]
      have store_constraints := is_store_active_constraints air row h_row h_is_real
                                  (by grind) h_store_sum h_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c, eq_a_is_x0,
        h_reg_rs1, h_reg_rs2,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
      obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
      clear h_mem
      extract_lets rs2_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.1
      have h_align :
        (4 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2
      rw [
        OpcodeSpec.RV64.execute_SW_equiv
        (r1 := rs1_let) (r2 := rs2_let) (imm := imm')
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_a_value air row))
        (state := state)
        (risc_v_assumptions := h_assumptions)
        (h_range := h_range)
        (h_align := h_align)
      ]
      . subst rs1_let rs2_let
        obtain ⟨ _, h_npc_eq, _, h_a0, h_a1, h_a2, h_a3 ⟩ := store_constraints
        have h_rs2' :
          read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0)))) state =
          EStateM.Result.ok (U64w.toBV
            #v[ air.cols.op_a_access.access.value_0 row 0,
                air.cols.op_a_access.access.value_1 row 0,
                air.cols.op_a_access.access.value_2 row 0,
                air.cols.op_a_access.access.value_3 row 0 ]) state := by
          simp only [h_a0, h_a1, h_a2, h_a3]; exact h_rs2
        simp [
          OpcodeSpec.RV64.spec_SW, CPU_bus_operations, bus_operations,
          deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors,
          eq_imm_b, eq_imm_c, eq_a_is_x0,
          h_reg_rs1, h_reg_rs2,
          BitVec.ofNatLT_eq_ofNat
        ]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        rw [operation_list_effect_state_writeReg_same h_rs1]
        rw [operation_list_effect_state_writeReg_same h_rs2']
        have h_extract_eq : BitVec.extractLsb 31 0 (op_a_value air row).toBV =
                            BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0) ++
                            BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
        := by
          clear *-; simp [op_a_value, BitVec.extractLsb, U64w.toBV]
          repeat rw [BitVec.extractLsb'_append_eq_ite]
          simp
        simp [op_b_value, h_npc_eq, h_extract_eq]
        simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv]
        simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . rw [OpcodeSpec.RV64.spec_SW_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
        . subst rs1_let; simp [op_b_value]; exact h_rs1
        . subst rs2_let; simp [op_a_value, store_constraints]; exact h_rs2

    /-- Equivalence for SD (opcode 47, `instruction.STORE (imm, rs2, rs1, 8)`). -/
    theorem equivalence_SD
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 47)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 8)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs2, rs1,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rs2, h_reg_rs1 ⟩ :=
        store_operand_setup air row h_row h_is_real (by grind) 8
          (by right; right; right; rfl) (by simp; exact h_opcode)
      have h_store_sum :
        air.cols.opcode_selector.is_sb row 0 +
          air.cols.opcode_selector.is_sh row 0 +
          air.cols.opcode_selector.is_sw row 0 +
          air.cols.opcode_selector.is_sd row 0 = 1 := by
        simp [h_selectors]
      have store_constraints := is_store_active_constraints air row h_row h_is_real
                                  (by grind) h_store_sum h_constraints
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c, eq_a_is_x0,
        h_reg_rs1, h_reg_rs2,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
      simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
      obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
      clear h_mem
      extract_lets rs2_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.1
      have h_align :
        (8 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2
      rw [
        OpcodeSpec.RV64.execute_SD_equiv
        (r1 := rs1_let) (r2 := rs2_let) (imm := imm')
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_a_value air row))
        (state := state)
        (risc_v_assumptions := h_assumptions)
        (h_range := h_range)
        (h_align := h_align)
      ]
      . subst rs1_let rs2_let
        obtain ⟨ _, h_npc_eq, _, h_a0, h_a1, h_a2, h_a3 ⟩ := store_constraints
        have h_rs2' :
          read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0)))) state =
          EStateM.Result.ok (U64w.toBV
            #v[ air.cols.op_a_access.access.value_0 row 0,
                air.cols.op_a_access.access.value_1 row 0,
                air.cols.op_a_access.access.value_2 row 0,
                air.cols.op_a_access.access.value_3 row 0 ]) state := by
          simp only [h_a0, h_a1, h_a2, h_a3]; exact h_rs2
        simp [
          OpcodeSpec.RV64.spec_SD, CPU_bus_operations, bus_operations,
          deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors,
          eq_imm_b, eq_imm_c, eq_a_is_x0,
          h_reg_rs1, h_reg_rs2,
          BitVec.ofNatLT_eq_ofNat
        ]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        rw [operation_list_effect_state_writeReg_same h_rs1]
        rw [operation_list_effect_state_writeReg_same h_rs2']
        simp [op_a_value, op_b_value, h_npc_eq]
        simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv]
        simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]
      . rw [OpcodeSpec.RV64.spec_SD_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
        . subst rs1_let; simp [op_b_value]; exact h_rs1
        . subst rs2_let; simp [op_a_value, store_constraints]; exact h_rs2

  end STORES

  section LOADS

    /-- Operand-setup lemma for the LOAD class. For loads, op_a holds rd
    (destination register). Returns the 12-bit immediate, rd (as op_a),
    rs1 (as op_b), the column equations, and selector facts. -/
    lemma load_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (is_unsigned : Bool)
      (mw : Nat)
      (h_mw : (is_unsigned = false ∧ mw = 1) ∨ (is_unsigned = true ∧ mw = 1) ∨
              (is_unsigned = false ∧ mw = 2) ∨ (is_unsigned = true ∧ mw = 2) ∨
              (is_unsigned = false ∧ mw = 4) ∨ (is_unsigned = true ∧ mw = 4) ∨
              (is_unsigned = false ∧ mw = 8))
      (h_opcode : air.cols.instruction.opcode row 0 =
        (match is_unsigned, mw with
         | false, 1 => 10 | true, 1 => 13
         | false, 2 => 11 | true, 2 => 14
         | false, 4 => 12 | true, 4 => 45
         | false, 8 => 46 | _, _ => 0))
    :
      ∃ (imm : BitVec 12) (rs1 rd : regidx),
        air.cols.instruction.op_a_0 row 0 = Transpiler.reg_to_KB rd ∧
        air.cols.instruction.op_a_1 row 0 = 0 ∧
        air.cols.instruction.op_a_2 row 0 = 0 ∧
        air.cols.instruction.op_a_3 row 0 = 0 ∧
        air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs1 ∧
        air.cols.instruction.op_b_1 row 0 = 0 ∧
        air.cols.instruction.op_b_2 row 0 = 0 ∧
        air.cols.instruction.op_b_3 row 0 = 0 ∧
        air.cols.instruction.op_c_0 row 0 = (Transpiler.imm_to_KB imm true)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.imm_to_KB imm true)[1] ∧
        air.cols.instruction.op_c_2 row 0 = (Transpiler.imm_to_KB imm true)[2] ∧
        air.cols.instruction.op_c_3 row 0 = (Transpiler.imm_to_KB imm true)[3] ∧
        air.cols.instruction.op_a_is_x0 row 0 = (if rd == regidx.Regidx 0 then 1 else 0) ∧
        air.cols.opcode_selector.imm_b row 0 = 0 ∧
        air.cols.opcode_selector.imm_c row 0 = 1 ∧
        (air.cols.opcode_selector.is_alu row 0 = 0 ∧
         air.cols.opcode_selector.is_ecall row 0 = 0 ∧
         air.cols.opcode_selector.is_lb row 0 = (if is_unsigned = false ∧ mw = 1 then 1 else 0) ∧
         air.cols.opcode_selector.is_lbu row 0 = (if is_unsigned = true ∧ mw = 1 then 1 else 0) ∧
         air.cols.opcode_selector.is_lh row 0 = (if is_unsigned = false ∧ mw = 2 then 1 else 0) ∧
         air.cols.opcode_selector.is_lhu row 0 = (if is_unsigned = true ∧ mw = 2 then 1 else 0) ∧
         air.cols.opcode_selector.is_lw row 0 = (if is_unsigned = false ∧ mw = 4 then 1 else 0) ∧
         air.cols.opcode_selector.is_lwu row 0 = (if is_unsigned = true ∧ mw = 4 then 1 else 0) ∧
         air.cols.opcode_selector.is_ld row 0 = (if is_unsigned = false ∧ mw = 8 then 1 else 0) ∧
         air.cols.opcode_selector.is_sb row 0 = 0 ∧
         air.cols.opcode_selector.is_sh row 0 = 0 ∧
         air.cols.opcode_selector.is_sw row 0 = 0 ∧
         air.cols.opcode_selector.is_sd row 0 = 0 ∧
         air.cols.opcode_selector.is_beq row 0 = 0 ∧
         air.cols.opcode_selector.is_bne row 0 = 0 ∧
         air.cols.opcode_selector.is_blt row 0 = 0 ∧
         air.cols.opcode_selector.is_bge row 0 = 0 ∧
         air.cols.opcode_selector.is_bltu row 0 = 0 ∧
         air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
         air.cols.opcode_selector.is_jalr row 0 = 0 ∧
         air.cols.opcode_selector.is_jal row 0 = 0 ∧
         air.cols.opcode_selector.is_auipc row 0 = 0 ∧
         air.cols.opcode_selector.is_unimpl row 0 = 0) ∧
        (air.cols.instruction.op_a_0 row 0).val < 32 ∧
        (air.cols.instruction.op_b_0 row 0).val < 32
    := by
      replace h_wf : bus_row_wf_asm (bus_row air row) := by grind
      simp [bus_row_wf_asm] at h_wf
      replace h_wf := h_wf.1
      simp [
        bus_row, deserialise_bus_row, raw_bus_row,
        ProgramBusEntry.operand_properties, h_is_real,
        -Vector.getElem_mk, -ProgramBusEntry.mk.injEq
      ] at h_wf
      obtain ⟨ instr, mult, data, props, h_eq, h_eq_entry, h_props ⟩ := h_wf
      have h_eq_mult : mult = 1 := by aesop
      simp [h_eq_mult] at h_eq h_eq_entry
      have h_opcode_props
        := @ProgramBusEntry.operand_properties_inversion
            instr
            ⟨ 1, data ⟩
            props
            (ProgramBusEntry.deserialise (program_bus_entry air row))
            (by simp [h_eq, h_is_real])
            (by simp [h_is_real]; aesop)
      rcases h_mw with ⟨ h_u, h ⟩ | ⟨ h_u, h ⟩ | ⟨ h_u, h ⟩ | ⟨ h_u, h ⟩ |
                     ⟨ h_u, h ⟩ | ⟨ h_u, h ⟩ | ⟨ h_u, h ⟩ <;>
        ( subst h h_u
          simp at h_opcode
          simp [h_opcode] at h_opcode_props
          obtain ⟨ imm, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ imm, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data] at h_eq_entry
          simp [h_props, Transpiler.is_register] at h_eq_props
          obtain ⟨ _eq_opcode,
                   eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0,
                   eq_imm_b, eq_imm_c, h_selectors ⟩ := h_eq_entry
          simp [← eq_a0, ← eq_b0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1
          refine ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                   eq_b0, eq_b1, eq_b2, eq_b3,
                   eq_c0, eq_c1, eq_c2, eq_c3,
                   eq_a_is_x0,
                   eq_imm_b, eq_imm_c,
                   h_selectors,
                   h_reg_rd, h_reg_rs1 ⟩ )

    /-- Equivalence for LB (opcode 10, `instruction.LOAD (imm, rs1, rd, false, 1)`). -/
    theorem equivalence_LB
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 10)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 1)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) false 1
          (by left; exact ⟨rfl, rfl⟩) (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      -- Case split on rd = x0 (= a_is_0 = 1 vs 0). regidx has DecidableEq via its BitVec field.
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . -- rd = x0 case: chip emits ReadMemAny, Sail spec_LB rd=0 branch.
        subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LB_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
        ]
        . -- Main equality for rd=x0 branch.
          have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LB, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . -- Hypotheses: rd=x0 case, third conjunct is mem.isSome.
          rw [OpcodeSpec.RV64.spec_LB_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          . simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simpa [op_b_value]
      . -- rd ≠ x0 case: chip emits ReadMem with byte, Sail spec_LB rd≠0 branch.
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LB_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0))
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
        ]
        . -- Main equality for rd≠x0 branch.
          have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_a_ext : U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
              BitVec.signExtend 64
                (BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0)) := by
            rw [h_asm_mem.2.2.2 h_a_is_0]
            simp [U64w.toBV, BitVec.setWidth_eq_append_extractLsb']
            rw! (config := { castMode := .all }) [min_eq_right (by simp)]
            repeat rw [BitVec.extractLsb'_append_eq_ite]
            simp [← BitVec.toNat_inj, BitVec.toNat_signExtend]
            simp [BitVec.getMsbD_eq_getLsbD, BitVec.msb_eq_getLsbD_last]
            simp [BitVec.getElem_eq_testBit_toNat]
            clear *-; grind
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LB, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, h_a_ext]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          clear *-; grind [reg_of_fin_neq_nextPC]
        . -- Hypotheses: rd≠x0 case, third conjunct is mem = some data0.
          rw [OpcodeSpec.RV64.spec_LB_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          . simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin, Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simpa [op_b_value]

    /-- Equivalence for LBU (opcode 13, `instruction.LOAD (imm, rs1, rd, true, 1)`). -/
    theorem equivalence_LBU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 13)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, true, 1)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) true 1
          (by right; left; exact ⟨rfl, rfl⟩) (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . -- rd = x0 case: chip emits ReadMemAny, Sail spec_LBU rd=0 branch.
        subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LBU_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
        ]
        . -- Main equality for rd=x0 branch.
          have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LBU, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . -- Hypotheses: rd=x0 case, third conjunct is mem.isSome.
          rw [OpcodeSpec.RV64.spec_LBU_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          . simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simpa [op_b_value]
      . -- rd ≠ x0 case: chip emits ReadMem with byte, Sail spec_LBU rd≠0 branch.
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LBU_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0))
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
        ]
        . -- Main equality for rd≠x0 branch.
          have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_a_ext : U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
              BitVec.setWidth 64
                (BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0)) := by
            rw [h_asm_mem.2.2.2 h_a_is_0]
            simp [U64w.toBV, BitVec.setWidth_eq_append_extractLsb']
            rw! (config := { castMode := .all }) [min_eq_left (by simp)]
            rw! (config := { castMode := .all }) [min_eq_right (by simp)]
            (repeat rw [BitVec.extractLsb'_append_eq_ite]); simp [← BitVec.toNat_inj]
            (repeat rw [BitVec.toNat_append]); simp
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LBU, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, h_a_ext]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          clear *-; grind [reg_of_fin_neq_nextPC]
        . -- Hypotheses: rd≠x0 case, third conjunct is mem = some data0.
          rw [OpcodeSpec.RV64.spec_LBU_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          . simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin, Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simpa [op_b_value]

    /-- Equivalence for LH (opcode 11, `instruction.LOAD (imm, rs1, rd, false, 2)`). -/
    theorem equivalence_LH
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 11)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 2)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) false 2
          (by right; right; left; exact ⟨rfl, rfl⟩) (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      have h_align :
        (2 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2.2.1
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . -- rd = x0 case: chip emits ReadMemAny, Sail spec_LH rd=0 branch.
        subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LH_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8) (data1 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . -- Main equality for rd=x0 branch.
          have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LH, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . -- Hypotheses: rd=x0 case (4 conjuncts: PC, rs1, mem[addr].isSome, mem[addr+1].isSome).
          rw [OpcodeSpec.RV64.spec_LH_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value]; grind
      . -- rd ≠ x0 case: chip emits ReadMem with half, Sail spec_LH rd≠0 branch.
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LH_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.extractLsb 7 0 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)))
          (data1 := BitVec.extractLsb 15 8 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)))
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . -- Main equality for rd≠x0 branch.
          have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_a_ext : U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
              BitVec.signExtend 64
                (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)) := by
            rw [h_asm_mem.2.2.2.2 h_a_is_0]
            simp [U64w.toBV, BitVec.setWidth_eq_append_extractLsb']
            rw! (config := { castMode := .all }) [min_eq_right (by simp)]
            repeat rw [BitVec.extractLsb'_append_eq_ite]
            simp
          have h_append_eq :
            BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0) =
              BitVec.extractLsb 15 8 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)) ++
              BitVec.extractLsb 7 0 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0))
            := by clear *-; simp [BitVec.extractLsb]; grind
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LH, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, h_a_ext]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          . rw [h_append_eq]; simp
          . clear *-; grind [reg_of_fin_neq_nextPC]
        . -- Hypotheses: rd≠x0 case (4 conjuncts).
          rw [OpcodeSpec.RV64.spec_LH_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin,
                  Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem, ← BitVec.toNat_inj]
            simp [BitVec.ofNat, width_of_mem_width]

    /-- Equivalence for LHU (opcode 14, `instruction.LOAD (imm, rs1, rd, true, 2)`). -/
    theorem equivalence_LHU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 14)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, true, 2)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) true 2
          (by right; right; right; left; exact ⟨rfl, rfl⟩) (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      have h_align :
        (2 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2.2.1
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LHU_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8) (data1 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LHU, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . rw [OpcodeSpec.RV64.spec_LHU_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem]
      . have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LHU_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.extractLsb 7 0 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)))
          (data1 := BitVec.extractLsb 15 8 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)))
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_a_ext : U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
              BitVec.setWidth 64
                (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)) := by
            rw [h_asm_mem.2.2.2.2 h_a_is_0]
            simp [U64w.toBV, BitVec.setWidth_eq_append_extractLsb']
            rw! (config := { castMode := .all }) [min_eq_left (by simp)]
            rw! (config := { castMode := .all }) [min_eq_right (by simp)]
            (repeat rw [BitVec.extractLsb'_append_eq_ite]); simp
          have h_append_eq :
            BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0) =
              BitVec.extractLsb 15 8 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)) ++
              BitVec.extractLsb 7 0 (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0))
            := by clear *-; simp [BitVec.extractLsb]; grind
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LHU, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, h_a_ext]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          . rw [h_append_eq]; simp
          . clear *-; grind [reg_of_fin_neq_nextPC]
        . rw [OpcodeSpec.RV64.spec_LHU_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin,
                  Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem, ← BitVec.toNat_inj]
            simp [BitVec.ofNat, width_of_mem_width]

    /-- Equivalence for LW (opcode 12, `instruction.LOAD (imm, rs1, rd, false, 4)`). -/
    theorem equivalence_LW
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 12)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 4)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) false 4
          (by right; right; right; right; left; exact ⟨rfl, rfl⟩) (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      have h_align :
        (4 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2.2.1
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LW_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8) (data1 := 0#8) (data2 := 0#8) (data3 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LW, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . rw [OpcodeSpec.RV64.spec_LW_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem]
      . have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        let v32 := (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)) ++
                   (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0))
        rw [
          OpcodeSpec.RV64.execute_LW_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.extractLsb 7 0 v32)
          (data1 := BitVec.extractLsb 15 8 v32)
          (data2 := BitVec.extractLsb 23 16 v32)
          (data3 := BitVec.extractLsb 31 24 v32)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_a_ext : U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
              BitVec.signExtend 64 v32 := by
            rw [h_asm_mem.2.2.2.2 h_a_is_0]
            simp [v32, U32w.toBV]
          have h_append_eq :
            v32 =
              BitVec.extractLsb 31 24 v32 ++ BitVec.extractLsb 23 16 v32 ++
              BitVec.extractLsb 15 8 v32 ++ BitVec.extractLsb 7 0 v32
          := by
            clear *-; simp [BitVec.extractLsb, v32]
            (repeat rw [BitVec.extractLsb'_append_eq_ite]); simp
            set x₁ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)
            set x₂ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
            rw [BitVec.extractLsb'_append_extractLsb', BitVec.append_assoc, BitVec.extractLsb'_append_extractLsb']
            simp
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LW, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, h_a_ext]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          . rw [← h_append_eq]
          . clear *-; grind [reg_of_fin_neq_nextPC]
        . rw [OpcodeSpec.RV64.spec_LW_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin,
                  Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem, v32]

    /-- Equivalence for LWU (opcode 45, `instruction.LOAD (imm, rs1, rd, true, 4)`). -/
    theorem equivalence_LWU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 45)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, true, 4)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) true 4
          (by right; right; right; right; right; left; exact ⟨rfl, rfl⟩)
          (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      have h_align :
        (4 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2.2.1
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LWU_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8) (data1 := 0#8) (data2 := 0#8) (data3 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LWU, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . rw [OpcodeSpec.RV64.spec_LWU_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem]
      . have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        let v32 := (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)) ++
                   (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0))
        rw [
          OpcodeSpec.RV64.execute_LWU_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.extractLsb 7 0 v32)
          (data1 := BitVec.extractLsb 15 8 v32)
          (data2 := BitVec.extractLsb 23 16 v32)
          (data3 := BitVec.extractLsb 31 24 v32)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_a_ext : U64w.toBV
              #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
              BitVec.setWidth 64 v32 := by
            rw [h_asm_mem.2.2.2.2 h_a_is_0]
            simp [v32, U32w.toBV, BitVec.setWidth_eq_append_extractLsb']
          have h_append_eq :
            v32 =
              BitVec.extractLsb 31 24 v32 ++ BitVec.extractLsb 23 16 v32 ++
              BitVec.extractLsb 15 8 v32 ++ BitVec.extractLsb 7 0 v32
          := by
            clear *-; simp [BitVec.extractLsb, v32]
            (repeat rw [BitVec.extractLsb'_append_eq_ite]); simp
            set x₁ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)
            set x₂ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
            rw [BitVec.extractLsb'_append_extractLsb', BitVec.append_assoc, BitVec.extractLsb'_append_extractLsb']
            simp
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LWU, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, h_a_ext]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          . rw [← h_append_eq]
          . clear *-; grind [reg_of_fin_neq_nextPC]
        . rw [OpcodeSpec.RV64.spec_LWU_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin,
                  Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem, v32]

    /-- Equivalence for LD (opcode 46, `instruction.LOAD (imm, rs1, rd, false, 8)`). -/
    theorem equivalence_LD
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 46)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 8)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) (by grind)
      have h_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_mem_wf : bus_row_wf_asm (bus_row air row) := by grind
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ imm', rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3,
               eq_c0, eq_c1, eq_c2, eq_c3, eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1 ⟩ :=
        load_operand_setup air row h_row h_is_real (by grind) false 8
          (by right; right; right; right; right; right; exact ⟨rfl, rfl⟩)
          (by simp; exact h_opcode)
      have h_imm_c_eqs := imm_c_eq_1_constraints air row eq_imm_c h_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 imm' := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn imm'
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      simp [bus_row_wf_asm] at h_mem_wf
      obtain ⟨ _, _, _, _, h_asm_mem ⟩ := h_mem_wf
      simp [bus_row, deserialise_bus_row, raw_bus_row, MemoryBus.Spec,
            h_is_real, h_opcode, h_selectors] at h_asm_mem
      have h_addr_bridge :
        U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] +
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] := by
        rw [← h_op_c_bv]; rfl
      have h_range :
        (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
        Pico_address_space_size_64 := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact h_asm_mem.2.2.1
      have h_align :
        (8 : ℤ) ∣ (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]; simp [BitVec.toNat_add]; exact_mod_cast h_asm_mem.2.2.2
      simp [
        CPU_bus_operations, bus_operations,
        deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors,
        eq_imm_b, eq_imm_c,
        h_reg_rd, h_reg_rs1,
        BitVec.ofNatLT_eq_ofNat
      ] at h_bus_hypotheses
      extract_lets rd_let rs1_let imm_let
      have h_imm_let : imm_let = imm' := h_imm_eq
      rw [h_imm_let]
      obtain ⟨ rd_bv ⟩ := rd
      by_cases h_rd0 : rd_bv = 0#5
      . subst h_rd0
        have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [eq_a_is_x0]; rfl
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        rw [
          OpcodeSpec.RV64.execute_LD_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := 0#8) (data1 := 0#8) (data2 := 0#8) (data3 := 0#8)
          (data4 := 0#8) (data5 := 0#8) (data6 := 0#8) (data7 := 0#8)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_op_a_zero : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [eq_a0]; simp [Transpiler.reg_to_KB, regidx_to_fin]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          subst rs1_let
          rw [h_rd_let_zero]
          simp [
            OpcodeSpec.RV64.spec_LD, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [operation_list_effect, operation_effect, write_xreg,
                Sail.writeReg, PreSail.writeReg, regidx_to_fin,
                load_constraints, h_op_a_zero]
        . rw [OpcodeSpec.RV64.spec_LD_hypotheses]
          have h_rd_let_zero : rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [eq_a0, Transpiler.reg_to_KB, regidx_to_fin]
          rw [h_rd_let_zero]
          simp only [beq_self_eq_true, if_true]
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem]
      . have h_a_is_0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [eq_a_is_x0]; simp [h_rd0]
        simp [h_a_is_0] at h_bus_hypotheses
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus_hypotheses
        simp [operation_list_effect_hypotheses_writeReg_same h_rs1] at h_rs2
        obtain ⟨ h_rs2, h_mem ⟩ := h_rs2
        let v64 := U64w.toBV
                    #v[ BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0),
                        BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0),
                        BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_2 row 0),
                        BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_3 row 0) ]
        rw [
          OpcodeSpec.RV64.execute_LD_equiv
          (r1 := rs1_let) (rd := rd_let) (imm := imm')
          (pc_val := U64w.toBV (pc air row))
          (r1_val := U64w.toBV (op_b_value air row))
          (data0 := BitVec.extractLsb 7 0 v64)
          (data1 := BitVec.extractLsb 15 8 v64)
          (data2 := BitVec.extractLsb 23 16 v64)
          (data3 := BitVec.extractLsb 31 24 v64)
          (data4 := BitVec.extractLsb 39 32 v64)
          (data5 := BitVec.extractLsb 47 40 v64)
          (data6 := BitVec.extractLsb 55 48 v64)
          (data7 := BitVec.extractLsb 63 56 v64)
          (state := state)
          (risc_v_assumptions := h_assumptions)
          (h_range := h_range)
          (h_align := h_align)
        ]
        . have h_load_sum :
            air.cols.opcode_selector.is_lb row 0 +
              air.cols.opcode_selector.is_lbu row 0 +
              air.cols.opcode_selector.is_lh row 0 +
              air.cols.opcode_selector.is_lhu row 0 +
              air.cols.opcode_selector.is_lw row 0 +
              air.cols.opcode_selector.is_lwu row 0 +
              air.cols.opcode_selector.is_ld row 0 = 1 := by
            simp [h_selectors]
          have load_constraints := is_load_active_constraints air row h_row h_is_real
                                    (by grind) h_load_sum h_constraints
          have h_append_eq :
            v64 =
              BitVec.extractLsb 63 56 v64 ++ BitVec.extractLsb 55 48 v64 ++
              BitVec.extractLsb 47 40 v64 ++ BitVec.extractLsb 39 32 v64 ++
              BitVec.extractLsb 31 24 v64 ++ BitVec.extractLsb 23 16 v64 ++
              BitVec.extractLsb 15 8 v64 ++ BitVec.extractLsb 7 0 v64
          := by
            clear *-; simp [BitVec.extractLsb, v64, U64w.toBV]
            (repeat rw [BitVec.extractLsb'_append_eq_ite]); simp
            set x₁ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_3 row 0)
            set x₂ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_2 row 0)
            set x₃ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)
            set x₄ := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
            conv =>
              lhs;
              rw [← BitVec.extractLsb'_append_extractLsb' (x := x₁) (len := 8)]
              rw [← BitVec.extractLsb'_append_extractLsb' (x := x₂) (len := 8)]
              rw [← BitVec.extractLsb'_append_extractLsb' (x := x₃) (len := 8)]
              rw [← BitVec.extractLsb'_append_extractLsb' (x := x₄) (len := 8)]
            (repeat rw [BitVec.append_assoc]); simp
          subst rs1_let
          simp [
            OpcodeSpec.RV64.spec_LD, CPU_bus_operations, bus_operations,
            deserialise_bus_row, raw_bus_row,
            h_is_real, h_opcode, h_selectors,
            eq_imm_b, eq_imm_c, h_a_is_0,
            h_reg_rd, h_reg_rs1,
            BitVec.ofNatLT_eq_ofNat
          ]
          have h_rd_not_zero : ¬ (rd_let == regidx.Regidx 0#5) = true := by
            subst rd_let; clear *- h_rd0 eq_a0 h_reg_rd; simp
            intro h_eq; apply h_rd0; clear h_rd0
            simp [← BitVec.toNat_inj] at h_eq
            simp [Fin.ext_iff, Transpiler.reg_to_KB, regidx_to_fin] at eq_a0
            simp [← BitVec.toNat_inj]; omega
          subst rd_let
          rw [if_neg h_rd_not_zero]; simp [← BitVec.toNat_inj] at h_rd_not_zero
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same h_rs1]
          simp [load_constraints, op_b_value, v64]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg]
          rw [ExtDHashMap.insert_comm]
          . rw [← h_append_eq]
          . clear *-; grind [reg_of_fin_neq_nextPC]
        . rw [OpcodeSpec.RV64.spec_LD_hypotheses]
          have h_rd_let_nonzero : ¬ rd_let = regidx.Regidx 0#5 := by
            subst rd_let
            simp [← BitVec.toNat_inj] at h_rd0 ⊢
            intro h_contra
            apply h_rd0
            rw [eq_a0] at h_contra
            simp [Transpiler.reg_to_KB, regidx_to_fin] at h_contra
            omega
          rw [if_neg (by simpa)]
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]; clear *- pc_npc_bounds; omega
          . subst rs1_let; simp [op_b_value]; exact h_rs1
          all_goals
            simp [← BitVec.toNat_inj] at h_rd0
            simp [operation_list_effect, operation_effect] at h_mem
            simp [write_xreg, eq_a0, Transpiler.reg_to_KB, regidx_to_fin,
                  Sail.writeReg, PreSail.writeReg] at h_mem
            simp [← BitVec.toNat_inj] at h_op_c_bv; simp [h_op_c_bv] at h_mem
            simp [op_b_value, h_mem, v64]

  end LOADS

end Equivalence
