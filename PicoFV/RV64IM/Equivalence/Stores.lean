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

end Equivalence
