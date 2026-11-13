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
