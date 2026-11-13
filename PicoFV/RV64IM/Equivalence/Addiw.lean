import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false
-- The bus assumptions are part of every instruction theorem's statement, whether or not this
-- particular proof reads them.
set_option linter.unusedVariables false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  attribute [local simp]
    program_bus_entry

  section ADDIW

    -- ========================================================================
    -- ADDIW — the RV64-only sign-extending 32-bit add-immediate, opcode 40 with
    -- `imm_c = 1`. It shares opcode 40 with `RTYPEW.ADDW`, which the immediate
    -- flag tells it from (`ProgramBusEntry.decoded_from` at 40), and the chip-side
    -- shape with every I-type row: one register read, `imm_b = 0`, `imm_c = 1`
    -- and no class selector.
    -- ========================================================================

    /-- Equivalence for ADDIW (opcode 40, `instruction.ADDIW`). `imm` is read back from the
        chip's `op_c` columns, the low 12 bits of the sign-extended 64-bit form. The close
        needs a `(b.setWidth 32) + (c.setWidth 32) = (b + c).setWidth 32` bridge between the
        chip's ALU output and `spec_ADDIW`'s `setWidth 32 (r1 + signExtend 64 imm)` form,
        discharged inside the folded `h_spec'`. -/
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 40 ∧
                  air.cols.opcode_selector.imm_b row 0 = 0 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.ADDIW (imm, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf : bus_row_wf_asm (bus_row air row) := h_all_wf row h_row
      have h_constraints : CpuChip.Extraction.allHold air row := h_all_constraints row h_row
      -- The row is an ALU row: no class selector, no halt, `next_pc = pc + 4`.
      have h_alu := alu_row_facts air row h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions (by rw [h_opcode.1]; rfl)
      -- The Program message, and the instruction it was decoded from.
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, h_al, h_lt, h_eq, h_eq_entry, h_props ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      simp [ProgramBusEntry.decoded_from, h_opcode.1, h_opcode.2.2] at h_decoded
      obtain ⟨ imm', rs1', rd', h_eq_instr ⟩ := h_decoded
      -- The message's fields are the ones the decoder writes for that instruction.
      subst h_eq_instr
      simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
      obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
      subst h_eq_data
      rw [deserialise_program_bus_entry] at h_eq_entry
      simp [ProgramBusEntry.deserialise] at h_eq_entry
      obtain ⟨ h_pc0, h_pc1, -, eq_a, eq_b0, eq_b1, eq_bs, eq_c0, eq_c1, eq_cs, eq_a_is_x0,
               -, -, h_s_ecall, h_s_mem, h_s_store, h_s_beq, h_s_bne, h_s_blt, h_s_bge,
               h_s_bltu, h_s_bgeu, h_s_jalr, h_s_jal, h_pc_carry ⟩ := h_eq_entry
      -- The decoder's side conditions: both registers are real register indices.
      simp [h_props, Transpiler.is_register] at h_eq_props
      obtain ⟨ h_reg_rd, h_reg_rs1 ⟩ := h_eq_props
      rw [← eq_a] at h_reg_rd
      rw [← eq_b0] at h_reg_rs1
      simp [Fin.lt_def] at h_reg_rd h_reg_rs1
      -- `op_c` is the sign-extended immediate.
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_constraints
      have h_op_c_bv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        simp only [op_c_value, h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1,
                   h_imm_c_eqs.2.2.2, eq_c0, eq_c1, eq_cs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        rw [h_op_c_bv]; bv_decide
      -- The row's messages, as operations on the Sail state.
      have h_bus := h_bus_hypotheses
      simp [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, deserialise_bus_row,
            raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode.1, h_opcode.2.1, h_opcode.2.2, h_s_mem,
            h_reg_rd, h_reg_rs1] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      -- The ALU dispatch is sent exactly when the destination is not `x0`
      -- (constraint 17, `is_alu_not_x0 = is_alu * (1 - op_a_0)`).
      have h_c17 : constraint_17 air row := by
        have h := h_constraints
        rw [allHold_iff_allHold_simplified] at h
        simp only [allHold_simplified, row_constraint_list, List.Forall] at h
        clear *- h; aesop
      simp [constraint_and_interaction_simplification, h_is_real, h_s_beq, h_s_bne, h_s_blt,
            h_s_bge, h_s_bltu, h_s_bgeu, h_s_ecall, h_s_mem, h_s_jal, h_s_jalr,
            sub_eq_zero] at h_c17
      have h_pc_bounds := pc_facts air row h_is_real h_wf
      extract_lets rd rs1 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [OpcodeSpec.RV64.execute_ADDIW_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_b_value air row))]
      · simp [OpcodeSpec.RV64.spec_ADDIW, CPU_bus_operations,
              RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
              MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode.1, h_opcode.2.1, h_opcode.2.2, h_s_mem,
              h_reg_rd, h_reg_rs1, rd, rs1, BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv =>
          rhs
          rw [operation_list_effect_state_writeReg_same
                (by simpa [BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_readReg]
        rw [h_alu.2.2.2.2]
        by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
        · -- The destination is `x0`: neither write changes the state, and the chip sends no
          -- ALU message (`is_alu_not_x0 = 0`), so there is nothing else to compare.
          rw [operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0]),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0])]
        · have h_wf_alu := h_wf
          simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real,
                h_opcode.1] at h_wf_alu
          have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
            rw [eq_a_is_x0]
            have h_ne : ¬ (rd' == regidx.Regidx 0#5) = true := by
              intro h
              simp at h
              subst h
              exact h_rd0 (by rw [eq_a]; rfl)
            simp [h_ne]
          have h_spec := h_wf_alu.2.1 (by rw [h_c17, h_a_is_x0]; ring)
          simp [RV64IM_Interactions.ALUBus.Spec] at h_spec
          obtain ⟨ -, h_spec_eq ⟩ := h_spec
          -- Fold the chip's `signExtend 64 (b32 + c32)` into `spec_ADDIW`'s
          -- `signExtend 64 (setWidth 32 (b + signExtend 64 imm'))`, using
          -- `b32 + c32 = (b + c).setWidth 32` for `c = signExtend 64 imm'`.
          have h_val :
              BitVec.signExtend 64 (BitVec.setWidth 32
                ((op_b_value air row).toBV + BitVec.signExtend 64 imm'))
              = U64w.toBV
                  #v[ BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0),
                      BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0),
                      BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_2 row 0),
                      BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_3 row 0) ] := by
            rw [h_spec_eq, h_imm_c_eqs.1, h_imm_c_eqs.2.1, eq_c0, eq_c1,
                Transpiler.V3.immw_operand_toBV_sgn imm']
            simp [execute_RTYPEW_pure, op_b_value]
            congr 1
            simp [← BitVec.toNat_inj, U32w.toNat, U64w.toNat, BitVec.toNat_signExtend,
                  BitVec.msb_eq_decide]
            split_ifs with h_msb <;> omega
          rw [h_val]
      · simp [OpcodeSpec.RV64.spec_ADDIW, operation_list_effect, operation_effect, rd, rs1]
        refine ⟨ ?_, ?_ ⟩
        · rw [h_pc_read]
          congr 1
          simp [pc, ← BitVec.toNat_inj, U64w.toNat]
          omega
        · simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b

  end ADDIW

end Equivalence
