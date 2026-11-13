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

end Equivalence
