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

  section UTYPE

    -- ========================================================================
    -- UTYPE — `instruction.UTYPE (imm, rd, uop)` with `imm : BitVec 20` and
    -- `uop ∈ { .LUI, .AUIPC }`. Sail semantics for both:
    --   LUI    rd_val = signExtend 64 (imm ++ 0#12)
    --   AUIPC  rd_val = pc       + signExtend 64 (imm ++ 0#12)
    -- Chip encoding: both use `imm_b = 1` AND `imm_c = 1` (so neither op_b
    -- nor op_c is a register read). The chip's columns are:
    --   LUI   : opcode = 0,  is_alu = 1,  is_auipc = 0,
    --           op_b = 0 (literal), op_c = imm_KB (signExtend 64 (imm ++ 0#12))
    --   AUIPC : opcode = 27, is_alu = 0,  is_auipc = 1,
    --           op_b = op_c = imm_KB
    -- LUI is computed via the standard ALU bus arm 0 (`a = b + c = 0 + imm`).
    -- AUIPC is computed via a dedicated ALU bus row whose `b` is `pc` and
    -- `c` is `op_b` (see `auipc_op_a_eq_pc_plus_op_b`).
    -- ========================================================================

    /-- Equivalence for LUI (opcode 0, `instruction.UTYPE (imm, rd, .LUI)`).
    Inversion at opcode 0 is a 3-way disjunction (RTYPE.ADD / ITYPE.ADDI /
    UTYPE.LUI); `imm_b = 1, imm_c = 1` selects LUI. The 20-bit `imm` is
    recovered from the chip's `op_c` columns as `((op_c >>> 12).setWidth 20)`
    — chip stores `signExtend 64 (imm ++ 0#12)`. -/
    theorem equivalence_LUI
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
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let imm : BitVec 20 := (U64w.toBV (op_c_value air row) >>> 12).setWidth 20
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      -- Operand extraction (inline; 2-existential ⟨imm, rd⟩).
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
      simp [h_opcode.1, h_opcode.2.1, h_opcode.2.2] at h_opcode_props
      obtain ⟨ imm', rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, Transpiler.opcode_of_uop, -Vector.eq_mk] at h_eq
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
      have h_reg_rd := h_eq_props
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      -- Bridge: op_c stores `signExtend 64 (imm' ++ 0#12)` via `imm_c = 1`.
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_opcode.2.2 h_all_constraints
      have h_op_c_bv :
        U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                      air.cols.op_c_access.access.value_1 row 0,
                      air.cols.op_c_access.access.value_2 row 0,
                      air.cols.op_c_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 (imm' ++ 0#12) := by
        simp only [h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1, h_imm_c_eqs.2.2.2,
                   eq_c0, eq_c1, eq_c2, eq_c3]
        exact Transpiler.imm_to_KB_BV_sgn (imm' ++ 0#12)
      have h_imm_eq : ((U64w.toBV (op_c_value air row)) >>> 12).setWidth 20 = imm' := by
        simp only [op_c_value]; rw [h_op_c_bv]; bv_decide
      -- Bridge: op_b is literally 0 (no register read, no immediate either —
      -- LUI uses `imm_b = 1` with `instruction.op_b_*` all hardcoded to 0).
      have h_imm_b_eqs := imm_b_eq_1_constraints air row h_opcode.2.1 h_all_constraints
      have h_op_b_zero :
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] = (0 : BitVec 64) := by
        simp only [h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1, h_imm_b_eqs.2.2.2,
                   eq_b0, eq_b1, eq_b2, eq_b3]
        rw [← BitVec.toNat_inj]; simp [U64w.toNat]
      -- Bus extraction (only pc + op_a write; no op_b/op_c reads under imm_b=imm_c=1).
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
          h_reg_rd
        ] at h_bus_hypotheses
        obtain ⟨ h_pc, h_reg0, _ ⟩ := h_bus_hypotheses
        simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
        exact ⟨ h_pc, h_reg0 ⟩
      obtain ⟨ h_pc, h_reg0 ⟩ := h_bus
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_LUI_equiv
        (pc_val := U64w.toBV (pc air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_LUI,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd
        ]
        subst reg0
        rw [operation_list_effect_state_swap_writePC_writeReg]
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure,
              and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        -- Fold h_spec into the Sail-spec form: `0 + signExtend 64 (imm' ++ 0#12) = signExtend …`.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = BitVec.signExtend 64 (imm' ++ 0#12) := by
          rw [h_spec, Transpiler.imm_to_KB_BV_sgn]
          simp [U64w.toBV]
        simp [← h_spec', BitVec.ofNatLT_eq_ofNat]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [OpcodeSpec.RV64.spec_LUI, operation_list_effect, operation_effect]
        simp [Sail.writeReg, PreSail.writeReg]
        simp [h_pc, pc, ← BitVec.toNat_inj, U64w.toNat]
        clear *- pc_npc_bounds; omega

    /-- Equivalence for AUIPC (opcode 27, `instruction.UTYPE (imm, rd, .AUIPC)`).
    Inversion is single-arm. Chip computes `op_a = pc + op_b` via the dedicated
    AUIPC ALU bus row (see `auipc_op_a_eq_pc_plus_op_b`); `imm_b = 1` forces
    `op_b = signExtend 64 (imm ++ 0#12)`. -/
    theorem equivalence_AUIPC
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
      (h_opcode : air.cols.instruction.opcode row 0 = 27 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (h_is_auipc : air.cols.opcode_selector.is_auipc row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let imm : BitVec 20 := (U64w.toBV (op_b_value air row) >>> 12).setWidth 20
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints :=
        is_auipc_active_constraints air row h_row h_is_real (by grind) h_is_auipc
          (by grind)
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
      simp [h_opcode.1] at h_opcode_props
      obtain ⟨ imm', rd, h_eq_instr ⟩ := h_opcode_props
      simp [h_eq_instr] at h_eq
      simp [Transpiler.transpile_op, Transpiler.opcode_of_uop, -Vector.eq_mk] at h_eq
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
      have h_reg_rd := h_eq_props
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      -- Bridge: op_b stores `signExtend 64 (imm' ++ 0#12)` via `imm_b = 1`.
      have h_imm_b_eqs := imm_b_eq_1_constraints air row h_opcode.2.1 h_all_constraints
      have h_op_b_bv :
        U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                      air.cols.op_b_access.access.value_1 row 0,
                      air.cols.op_b_access.access.value_2 row 0,
                      air.cols.op_b_access.access.value_3 row 0 ] =
        BitVec.signExtend 64 (imm' ++ 0#12) := by
        simp only [h_imm_b_eqs.1, h_imm_b_eqs.2.1, h_imm_b_eqs.2.2.1, h_imm_b_eqs.2.2.2,
                   eq_b0, eq_b1, eq_b2, eq_b3]
        exact Transpiler.imm_to_KB_BV_sgn (imm' ++ 0#12)
      have h_imm_eq : ((U64w.toBV (op_b_value air row)) >>> 12).setWidth 20 = imm' := by
        simp only [op_b_value]; rw [h_op_b_bv]; bv_decide
      -- The dedicated AUIPC ALU bridge: `op_a = pc + op_b`.
      have h_auipc := auipc_op_a_eq_pc_plus_op_b air row h_is_real (by grind) h_is_auipc
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
        h_reg_rd
      ] at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg0
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 imm
      have h_imm_let : imm = imm' := h_imm_eq
      rw [h_imm_let]
      rw [
        OpcodeSpec.RV64.execute_AUIPC_equiv
        (pc_val := U64w.toBV (pc air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_AUIPC,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, h_opcode.2.1, h_opcode.2.2,
          h_reg_rd
        ]
        subst reg0
        rw [operation_list_effect_state_swap_writePC_writeReg]
        -- Fold `op_a = pc + op_b = pc + signExtend 64 (imm' ++ 0#12)` into h_spec'.
        have h_spec' :
            U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
            = U64w.toBV (pc air row) + BitVec.signExtend 64 (imm' ++ 0#12) := by
          rw [h_auipc, h_op_b_bv]
        simp [← h_spec', BitVec.ofNatLT_eq_ofNat]
        rw [seq_constraints.2.1]
      . simp [OpcodeSpec.RV64.spec_AUIPC, operation_list_effect, operation_effect]
        simp [Sail.writeReg, PreSail.writeReg]
        simp [h_pc, pc, ← BitVec.toNat_inj, U64w.toNat]
        clear *- pc_npc_bounds; omega

  end UTYPE

end Equivalence
