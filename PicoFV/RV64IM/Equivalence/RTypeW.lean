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

end Equivalence
