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

end Equivalence
