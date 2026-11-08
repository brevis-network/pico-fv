import PicoFV.RV64IM.Equivalence.Common

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

end Equivalence
