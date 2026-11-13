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

  section DIV_FAMILY

    -- ========================================================================
    -- DIV-family variant tag. The DIV family spans 8 chip opcodes:
    --   DIV   = 34   — 64-bit signed division
    --   DIVU  = 35   — 64-bit unsigned division
    --   REM   = 36   — 64-bit signed remainder
    --   REMU  = 37   — 64-bit unsigned remainder
    --   DIVW  = 49   — 32-bit signed division (RV64-only)
    --   DIVUW = 50   — 32-bit unsigned division (RV64-only)
    --   REMW  = 51   — 32-bit signed remainder (RV64-only)
    --   REMUW = 52   — 32-bit unsigned remainder (RV64-only)
    -- All eight share the MUL-family bus layout (3 register operands,
    -- imm_b = 0, imm_c = 0, is_alu = 1), and unlike the MUL family their
    -- ALUBus.Spec arms do *not* prepend `operand_range ∧ …`, so the
    -- h_wf_alu destructure matches the ADD/SUB shape (no `_h_operands`).
    -- Every variant's inversion is 3-existential (no MUL-Low-style edge
    -- case), so `cases var <;> (…)` with a single common body suffices.
    -- ========================================================================

    inductive DivVariant where
      | DIV | DIVU | REM | REMU | DIVW | DIVUW | REMW | REMUW
      deriving DecidableEq, Repr

    def opcode_of_DivVariant : DivVariant → FKB
      | .DIV   => 34
      | .DIVU  => 35
      | .REM   => 36
      | .REMU  => 37
      | .DIVW  => 49
      | .DIVUW => 50
      | .REMW  => 51
      | .REMUW => 52

    /-- Operand-setup lemma for the DIV family. Mirrors `mul_operand_setup`. -/
    lemma div_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (var : DivVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_DivVariant var)
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
        air.cols.opcode_selector.imm_c row 0 = 0 ∧
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
      -- All 8 variants are 3-existential and share an identical post-`obtain`
      -- body — closing over them with `cases var <;> (…)`.
      cases var <;>
        ( simp [opcode_of_DivVariant] at h_opcode
          simp [h_opcode] at h_opcode_props
          obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ rs2, rs1, rd, ?_ ⟩
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
          simp [← eq_a0, ← eq_b0, ← eq_c0] at h_eq_props
          obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := h_eq_props
          simp [Fin.lt_def] at h_reg_rd h_reg_rs1 h_reg_rs2
          exact ⟨ eq_a0, eq_a1, eq_a2, eq_a3,
                  eq_b0, eq_b1, eq_b2, eq_b3,
                  eq_c0, eq_c1, eq_c2, eq_c3,
                  eq_a_is_x0,
                  eq_imm_b, eq_imm_c,
                  h_selectors,
                  h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ )

    /-- Bus-side setup lemma for the DIV family. Identical in shape to
    `mul_bus_setup`. -/
    lemma div_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (var : DivVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_DivVariant var)
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
      grind [op_b_value, op_c_value]

    /-- Equivalence for DIV (opcode 34, signed 64-bit division,
    `instruction.DIV (…, false)` in Sail). Probe equivalence for the DIV
    family — same close as `equivalence_MULH` but without the extra
    `_h_operands` slot in the destructure (DIV/REM/DIVW/REMW ALUBus.Spec
    arms don't carry `operand_range ∧ …`). -/
    theorem equivalence_DIV
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
      (h_opcode : air.cols.instruction.opcode row 0 = 34)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIV
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIV
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIV_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIV,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for DIVU (opcode 35, unsigned 64-bit division). -/
    theorem equivalence_DIVU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 35)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIV (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIVU
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIVU
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIVU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIVU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REM (opcode 36, signed 64-bit remainder). -/
    theorem equivalence_REM
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
      (h_opcode : air.cols.instruction.opcode row 0 = 36)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REM
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REM
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REM_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REM,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REMU (opcode 37, unsigned 64-bit remainder). -/
    theorem equivalence_REMU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 37)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REM (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REMU
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REMU
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REMU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REMU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for DIVW (opcode 49, signed 32-bit division, RV64-only). -/
    theorem equivalence_DIVW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 49)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIVW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIVW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIVW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIVW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for DIVUW (opcode 50, unsigned 32-bit division, RV64-only). -/
    theorem equivalence_DIVUW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 50)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.DIVW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .DIVUW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .DIVUW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_DIVUW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_DIVUW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REMW (opcode 51, signed 32-bit remainder, RV64-only). -/
    theorem equivalence_REMW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 51)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, false)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REMW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REMW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REMW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REMW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for REMUW (opcode 52, unsigned 32-bit remainder, RV64-only). -/
    theorem equivalence_REMUW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 52)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.REMW (rs2, rs1, rd, true)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := div_operand_setup air row h_row h_is_real (by grind) .REMUW
             (by simp [opcode_of_DivVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        div_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .REMUW
          (by simp [opcode_of_DivVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_REMUW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_REMUW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end DIV_FAMILY

end Equivalence
