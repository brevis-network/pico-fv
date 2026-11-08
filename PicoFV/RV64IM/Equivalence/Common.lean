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

  -- `bv_decide` realises these auxiliary declarations in each module that needs them, and two
  -- instruction-class files realising them separately cannot be imported together. Realising
  -- them once here, below every class file, avoids the clash.
  open Lean.Elab.Tactic.BVDecide.Frontend.Normalize in
  run_meta do
    for enum in [``Register, ``Reservability, ``misaligned_fault, ``uop, ``bop] do
      discard <| getEnumToBitVecFor enum
      discard <| getEqIffEnumToBitVecEqFor enum
      discard <| getEnumToBitVecLeFor enum

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

end Equivalence
