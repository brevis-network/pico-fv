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

end Equivalence
