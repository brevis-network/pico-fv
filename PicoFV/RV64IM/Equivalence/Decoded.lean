import PicoFV.RV64IM.Equivalence.Stores

set_option maxHeartbeats 4_000_000
-- As in `Common.lean`: the linter is slow on this proof's large context.
set_option linter.constructorNameAsVariable false

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section DECODED

    /-- `SD` in decoded form: for every `SD` instruction and address `addr` whose decoding
        (`Transpiler.V3.transpile_op`) is the row's Program message, Sail's step on that
        instruction equals the row's effect. The decoding replaces `equivalence_SD`'s opcode
        and `is_real` hypotheses: it implies them, and with the Program table's promise they
        imply it (`SD_decode_satisfiable`). It fixes `addr` only modulo `2 ^ 32`, through the
        row's two 16-bit pc pieces. -/
    theorem equivalence_SD_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 12} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.STORE (imm, rs2, rs1, 8)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.STORE (imm, rs2, rs1, 8)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ opc, h_opc, h_data ⟩ := transpile_op_store_row h_decode
      obtain rfl : opc = 47 := by
        rcases h_opc with ⟨ h, - ⟩ | ⟨ h, - ⟩ | ⟨ h, - ⟩ | ⟨ -, h ⟩ <;>
          first | exact absurd h (by decide) | exact h
      have h_cols := congrArg ProgramBusEntry.deserialise h_data
      rw [deserialise_program_bus_entry, ProgramBusEntry.deserialise_vec] at h_cols
      simp only [ProgramBusEntry.mk.injEq] at h_cols
      obtain ⟨ h_is_real, -, -, h_opcode, -, h_op_a, h_op_b_0, -, -, h_c0, h_c1, h_cs, -, -,
               h_imm_c, - ⟩ := h_cols
      have h := equivalence_SD air row h_row h_is_real h_all_axioms h_all_ext h_all_wf
        h_all_wf_asrt h_all_constraints pico_assumptions h_opcode h_bus_hypotheses
        risc_v_assumptions
      have h_c := imm_c_eq_1_constraints air row h_imm_c (h_all_constraints row h_row)
      have h_imm : (U64w.toBV (op_c_value air row)).setWidth 12 = imm := by
        simp only [op_c_value, h_c.1, h_c.2.1, h_c.2.2.1, h_c.2.2.2, h_c0, h_c1, h_cs]
        rw [Transpiler.V3.imm_operand_toBV_sgn imm (by norm_num) (by norm_num)]
        exact setWidth_signExtend_self imm (by norm_num)
      have h_reg (r : regidx) : regidx.Regidx (Transpiler.reg_to_KB r).val = r := by
        obtain ⟨ r ⟩ := r
        simp [Transpiler.reg_to_KB, regidx_to_fin]
      simpa only [h_op_a, h_op_b_0, h_reg, h_imm] using h

    /-- The converse of the decoding hypothesis: on a real row with opcode 47, the Program
        table's promise gives an `SD` instruction and an address whose decoding is the row's
        Program message. So `equivalence_SD_decoded` applies to every row `equivalence_SD`
        applies to. -/
    theorem SD_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = 47)
    :
      ∃ (imm : BitVec 12) (rs2 rs1 : regidx) (addr : ℕ) (props : Prop),
        Transpiler.V3.transpile_op (.STORE (imm, rs2, rs1, 8)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, data, props, -, -, h_trans, h_deser, - ⟩ :=
        program_bus_operand_properties air row h_is_real h_wf
      have h_dec := ProgramBusEntry.operand_properties_inversion h_trans h_deser
      rw [deserialise_program_bus_entry] at h_dec
      simp only [h_opcode] at h_dec
      obtain ⟨ imm, rs2, rs1, rfl ⟩ := h_dec
      have h_data : program_bus_entry air row = data :=
        (ProgramBusEntryInstance.inv_ser_deser (program_bus_entry air row)).symm.trans
          ((congrArg ProgramBusEntryInstance.serialise h_deser).trans
            (ProgramBusEntryInstance.inv_ser_deser data))
      have h_mult :
          (ProgramBusEntry.deserialise (program_bus_entry air row)).multiplicity = 1 := by
        rw [deserialise_program_bus_entry]; exact h_is_real
      rw [h_mult] at h_trans
      exact ⟨ imm, rs2, rs1, addr, props, by rw [h_data]; exact h_trans.symm ⟩

  end DECODED

end Equivalence
