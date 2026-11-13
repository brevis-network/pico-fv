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

  section RTYPE

    -- ========================================================================
    -- R-type ALU operand setup. Packages the Program-bus inversion + chip-side
    -- column-equation extraction common to every RTYPE ALU opcode (ADD, SUB,
    -- AND, OR, XOR, SLL, SRL, SRA, SLT, SLTU). Caller supplies `op : rop` +
    -- `h_opcode : opcode = opcode_of_rop op` + `h_imm_c : imm_c = 0`; lemma
    -- returns ∃ rs2 rs1 rd, the 16 column equations (op_a/b/c limbs, x0 flag,
    -- imm_b), the 23-selector pattern (`is_alu = 1` and all others 0), and the
    -- u5 register-id bounds on op_a/b/c_0.
    -- ========================================================================

    /-- Operand-setup lemma for the RTYPE ALU class. Mirrors the
    Program-bus inversion + column-equation extraction in
    `equivalence_ADD` (lines 138-173 of this file); usable verbatim by
    every per-opcode RTYPE equivalence theorem. -/
    lemma rtype_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (op : rop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_rop op)
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
      cases op <;>
        ( simp [Transpiler.opcode_of_rop] at h_opcode
          simp [h_opcode, h_imm_c] at h_opcode_props
          obtain ⟨ rs2, rs1, rd, h_eq_instr ⟩ := h_opcode_props
          refine ⟨ rs2, rs1, rd, ?_ ⟩
          simp [h_eq_instr] at h_eq
          simp [Transpiler.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, h_eq_props ⟩ := h_eq
          simp [h_eq_data, Transpiler.opcode_of_rop] at h_eq_entry
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
                  eq_a_is_x0, eq_imm_b,
                  h_selectors,
                  h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ )

    -- ========================================================================
    -- R-type ALU bus setup. Packages the post-operand-setup chunk that
    -- extracts the ALU-bus consumer assumption + the four Sail register/PC
    -- read assumptions from `h_bus_hypotheses`. Output (in order):
    --   1. `h_wf_alu` — the ALU-bus `wf_assume` conjunction (used to extract
    --      `a = execute_RTYPE_pure b c op` from the chip's ALU lookup).
    --   2. `h_pc` — the Sail PC read; PC value is in raw limb-sum BV form.
    --   3. `h_reg1` — the rs1 (op_b) register read; value as `U64w.toBV` of
    --      `op_b_value` (4-limb form).
    --   4. `h_reg2` — the rs2 (op_c) register read; value as `U64w.toBV` of
    --      `op_c_value` (4-limb form).
    --   5. `h_reg0` — the rd (op_a previous) register read; value as
    --      `U64w.toBV` of the 4-limb `prev_value_*` form.
    -- All five hypotheses are stated in the forms that drop straight into
    -- the per-opcode equivalence proof (post-rtype_operand_setup, used in
    -- Phases 4-6 of the original equivalence_ADD proof).
    -- ========================================================================

    /-- Bus-side setup lemma for the RTYPE ALU class. Mirrors the post-setup
    chunk of `equivalence_ADD` (lines 287-294 in the original proof). The
    23-selector pattern, register-id bounds, opcode equality and imm_b/imm_c
    flags should be supplied as obtained from `rtype_operand_setup`. -/
    lemma rtype_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (op : rop)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_rop op)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (eq_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
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
      simp [bus_row_wf_asm] at h_all_wf
      obtain ⟨ _, h_wf_alu, _, _, _ ⟩ := h_all_wf
      refine ⟨ h_wf_alu, ?_ ⟩
      simp [
        CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
        h_is_real, h_opcode, h_selectors, eq_imm_b, h_imm_c,
        h_reg_rd, h_reg_rs1, h_reg_rs2
      ] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_pc, h_reg1, h_reg2, h_reg0, _ ⟩ := h_bus_hypotheses
      simp [BitVec.ofNatLT_eq_ofNat] at h_reg1 h_reg2 h_reg0
      show _ ∧ _ ∧ _ ∧ _
      refine ⟨ ?_, ?_, ?_, ?_ ⟩
      . exact h_pc
      . simp only [op_b_value]; exact h_reg1
      . simp only [op_c_value]; exact h_reg2
      . exact h_reg0

    -- ==========================================================================
    -- Per-opcode RTYPE equivalence theorems.
    -- ==========================================================================

    /-- Equivalence for ADD (opcode 0, R-type ALU `.ADD`).
    Pattern: under the chip's row constraints + bus assumptions + program
    well-formedness + a state pre-condition (`h_bus_hypotheses`), the chip's
    emitted bus operations, applied to a Sail `state`, produce the same
    post-state as one Sail step of `instruction.RTYPE (rs2, rs1, rd, .ADD)`. -/
    theorem equivalence_ADD
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
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses to the current row + pull
      -- common chip-side facts (sequential active constraints, pc/next_pc u16 bounds).
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      -- Phase 2: RTYPE operand extraction via the class-level setup lemma.
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .ADD (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      -- Phase 3: package the ALU-bus + PC/reg read assumptions via rtype_bus_setup.
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .ADD
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      -- Phase 4: bridge Sail RTYPE → spec_ADD via execute_ADD_equiv.
      rw [
        OpcodeSpec.RV64.execute_ADD_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      -- Phase 5: state equality.
      . simp [
          OpcodeSpec.RV64.spec_ADD,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      -- Phase 6: discharge execute_ADD_equiv hypothesis side-goal.
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SUB (opcode 1, R-type ALU `.SUB`). -/
    theorem equivalence_SUB
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
      (h_opcode : air.cols.instruction.opcode row 0 = 1 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SUB)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SUB (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SUB
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SUB_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SUB,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for XOR (opcode 2, R-type ALU `.XOR`). -/
    theorem equivalence_XOR
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
      (h_opcode : air.cols.instruction.opcode row 0 = 2 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.XOR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .XOR (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .XOR
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_XOR_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_XOR,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for OR (opcode 3, R-type ALU `.OR`). -/
    theorem equivalence_OR
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
      (h_opcode : air.cols.instruction.opcode row 0 = 3 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.OR)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .OR (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .OR
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_OR_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_OR,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for AND (opcode 4, R-type ALU `.AND`). -/
    theorem equivalence_AND
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
      (h_opcode : air.cols.instruction.opcode row 0 = 4 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.AND)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .AND (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .AND
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_AND_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_AND,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLL (opcode 5, R-type ALU `.SLL`). -/
    theorem equivalence_SLL
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
      (h_opcode : air.cols.instruction.opcode row 0 = 5 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SLL (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLL
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLL_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRL (opcode 6, R-type ALU `.SRL`). -/
    theorem equivalence_SRL
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
      (h_opcode : air.cols.instruction.opcode row 0 = 6 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRL)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SRL (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SRL
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SRL_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SRA (opcode 7, R-type ALU `.SRA`). -/
    theorem equivalence_SRA
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
      (h_opcode : air.cols.instruction.opcode row 0 = 7 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SRA)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SRA (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SRA
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SRA_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SRA,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLT (opcode 8, R-type ALU `.SLT`). -/
    theorem equivalence_SLT
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
      (h_opcode : air.cols.instruction.opcode row 0 = 8 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SLT (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLT
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLT_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLT,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for SLTU (opcode 9, R-type ALU `.SLTU`). -/
    theorem equivalence_SLTU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 9 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      obtain ⟨ rs2, rs1, rd,
              eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
              eq_a_is_x0, eq_imm_b,
              h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ :=
        rtype_operand_setup air row h_is_real (by grind) .SLTU (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        rtype_bus_setup (state := state) air row h_is_real (by grind) (by grind) .SLTU
          (by simp [Transpiler.opcode_of_rop]; exact h_opcode.1) h_opcode.2 eq_imm_b h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_SLTU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_SLTU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode.1, h_selectors, eq_imm_b, h_opcode.2,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, execute_RTYPE_pure, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints; specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end RTYPE

end Equivalence
