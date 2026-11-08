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

  section MUL_FAMILY

    -- ========================================================================
    -- MUL-family variant tag. The MUL family spans 5 chip opcodes:
    --   MUL    = 30   — low 64 bits, signedness-agnostic (5-existential inversion)
    --   MULH   = 31   — high 64 bits, signed × signed
    --   MULHU  = 32   — high 64 bits, unsigned × unsigned
    --   MULHSU = 33   — high 64 bits, signed × unsigned
    --   MULW   = 48   — 32-bit × 32-bit → 32-bit sign-extended to 64
    -- All five share the same Program-bus column layout (3 register operands,
    -- imm_b = 0, imm_c = 0, is_alu = 1), so the operand/bus setups can be
    -- factored exactly as for `rtype_operand_setup` / `rtype_bus_setup`.
    -- ========================================================================

    inductive MulVariant where
      | MUL | MULH | MULHU | MULHSU | MULW
      deriving DecidableEq, Repr

    def opcode_of_MulVariant : MulVariant → FKB
      | .MUL    => 30
      | .MULH   => 31
      | .MULHU  => 32
      | .MULHSU => 33
      | .MULW   => 48

    -- ========================================================================
    -- MUL-family operand setup. Mirrors `rtype_operand_setup` but for the
    -- five MUL/MULW chip opcodes. Caller supplies `var : MulVariant` +
    -- `h_opcode : opcode = opcode_of_MulVariant var`. The chip-side imm_b /
    -- imm_c flags are returned (eq_imm_b, eq_imm_c) — for the MUL family
    -- the transpiler emits both as 0, so callers can pattern-match them out.
    -- For `.MUL` (opcode 30) the underlying inversion is 5-existential
    -- (∃ rs2 rs1 rd sl sr, …); we drop the irrelevant sl/sr and return a
    -- 3-existential, matching the shape of the other 4 variants. The
    -- caller's `equivalence_MUL` will then universally quantify the
    -- signedness fields at the theorem statement (mirroring
    -- `execute_MUL_equiv` in `mul.lean:88`).
    -- ========================================================================

    /-- Operand-setup lemma for the MUL family (5 opcodes: MUL/MULH/MULHU/
    MULHSU/MULW). Mirrors `rtype_operand_setup`. -/
    lemma mul_operand_setup
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (var : MulVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_MulVariant var)
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
        air.cols.instruction.op_a_is_x0 row 0 = (if (rd == regidx.Regidx 0#5) = true then 1 else 0) ∧
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
      -- ------------------------------------------------------------------
      -- Dispatch on the variant. .MUL is 5-existential; the rest are
      -- 3-existential. The post-`obtain` body is otherwise identical.
      -- ------------------------------------------------------------------
      cases var
      -- .MUL (opcode 30): 5-existential — drop sl / sr.
      . simp [opcode_of_MulVariant] at h_opcode
        simp [h_opcode] at h_opcode_props
        obtain ⟨ rs2, rs1, rd, sl, sr, h_eq_instr ⟩ := h_opcode_props
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
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULH (opcode 31): 3-existential, fixed (.High, .Signed, .Signed).
      . simp [opcode_of_MulVariant] at h_opcode
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
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULHU (opcode 32).
      . simp [opcode_of_MulVariant] at h_opcode
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
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULHSU (opcode 33).
      . simp [opcode_of_MulVariant] at h_opcode
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
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
      -- .MULW (opcode 48).
      . simp [opcode_of_MulVariant] at h_opcode
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
                h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩

    -- ========================================================================
    -- MUL-family bus setup. Identical in shape to `rtype_bus_setup` — the
    -- chip's State-bus emission for MUL/MULW is the same as for RTYPE
    -- (imm_b = imm_c = 0 means op_a/op_b/op_c are all register reads). The
    -- ALU-bus shape only differs by opcode value (handled by `h_opcode`).
    -- ========================================================================

    /-- Bus-side setup lemma for the MUL family. -/
    lemma mul_bus_setup
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (var : MulVariant)
      (h_opcode : air.cols.instruction.opcode row 0 = opcode_of_MulVariant var)
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

    /-- Equivalence for MULH (opcode 31, `instruction.MUL` with
    `result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed`).
    Probe equivalence for the MUL family: validates that the chip's
    `execute_MUL_pure b c .MULH` matches the Sail spec's
    `execute_MUL_pure r1_val r2_val .MULH` without any bridge work
    (no immediate, no shift extraction). Note the `h_wf_alu` destructure
    has the extra `_h_operands` slot because every MUL/MULW arm of
    `ALUBus.Spec` carries `operand_range ∧ …` (same as XOR/OR/AND). -/
    theorem equivalence_MULH
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
      (h_opcode : air.cols.instruction.opcode row 0 = 31)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Signed })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      -- Phase 1: specialise universal hypotheses to the current row + pull common facts.
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULH
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULH
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      -- Phase 2: bridge Sail MUL → spec_MULH via execute_MULH_equiv.
      rw [
        OpcodeSpec.RV64.execute_MULH_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      -- Phase 3: state equality.
      . simp [
          OpcodeSpec.RV64.spec_MULH,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        -- ALU arms 30..33 / 48 all wrap their spec as `operand_range ∧ …`,
        -- so the destructure picks up an extra `_h_operands` slot (same as
        -- the XOR/OR/AND RTYPE pattern).
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      -- Phase 4: discharge execute_MULH_equiv hypothesis side-goal.
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MUL (opcode 30, `instruction.MUL` with
    `result_part := .Low`). The Sail spec for MUL is parametric in the
    signedness fields (the low 64 bits of the product do not depend on
    sign), so the theorem universally quantifies `srs1 srs2 : Signedness`
    just like `OpcodeSpec.RV64.execute_MUL_equiv`. Internally the
    `mul_operand_setup .MUL` invocation handles the 5-existential
    inversion (it drops the irrelevant `sl / sr` returned by
    `operand_properties_inversion`). -/
    theorem equivalence_MUL
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
      (h_opcode : air.cols.instruction.opcode row 0 = 30)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
      (srs1 srs2 : Signedness)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.Low,
            signed_rs1   := srs1,
            signed_rs2   := srs2 })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MUL
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MUL
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MUL_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MUL,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MULHU (opcode 32, `instruction.MUL` with
    `result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned`). -/
    theorem equivalence_MULHU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 32)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Unsigned,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULHU
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULHU
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MULHU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MULHU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MULHSU (opcode 33, `instruction.MUL` with
    `result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned`). -/
    theorem equivalence_MULHSU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 33)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MUL
        (rs2, rs1, rd,
          { result_part  := VectorHalf.High,
            signed_rs1   := Signedness.Signed,
            signed_rs2   := Signedness.Unsigned })) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULHSU
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULHSU
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MULHSU_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MULHSU,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

    /-- Equivalence for MULW (opcode 48, `instruction.MULW`). Distinct
    constructor (`.MULW` vs `.MUL`) and the spec applies `setWidth 32`
    to the operands before multiplying — matching the chip's ALU bus
    arm 48 (`a = execute_MULW_pure (b.setWidth 32) (c.setWidth 32)`). -/
    theorem equivalence_MULW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 48)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      execute_instruction (instruction.MULW (rs2, rs1, rd)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have seq_constraints := is_sequential_active_constraints air row h_row h_is_real (by grind)
      obtain ⟨ rs2, rs1, rd,
               eq_a0, eq_a1, eq_a2, eq_a3, eq_b0, eq_b1, eq_b2, eq_b3, eq_c0, eq_c1, eq_c2, eq_c3,
               eq_a_is_x0, eq_imm_b, eq_imm_c,
               h_selectors, h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩
        := mul_operand_setup air row h_row h_is_real (by grind) .MULW
             (by simp [opcode_of_MulVariant]; exact h_opcode)
      obtain ⟨ h_wf_alu, h_pc, h_reg1, h_reg2, h_reg0 ⟩ :=
        mul_bus_setup (state := state) air row h_row h_is_real (by grind) (by grind) .MULW
          (by simp [opcode_of_MulVariant]; exact h_opcode)
          eq_imm_b eq_imm_c h_selectors h_reg_rd h_reg_rs1 h_reg_rs2
      replace h_all_axioms : bus_row_axioms (bus_row air row) := by grind
      replace h_all_ext : bus_row_ext_asm (bus_row air row) := by grind
      replace h_all_wf : bus_row_wf_asm (bus_row air row) := by grind
      replace h_all_wf_asrt : bus_row_wf_asrt (bus_row air row) := by grind
      replace h_all_constraints : CpuChip.Extraction.allHold air row := by grind
      have pc_npc_bounds := pc_next_pc_u16_bounds air row h_is_real (by grind) h_all_constraints
      extract_lets reg0 reg1 reg2
      rw [
        OpcodeSpec.RV64.execute_MULW_equiv
        (pc_val := U64w.toBV (pc air row))
        (r1_val := U64w.toBV (op_b_value air row))
        (r2_val := U64w.toBV (op_c_value air row))
      ]
      . simp [
          OpcodeSpec.RV64.spec_MULW,
          CPU_bus_operations, bus_operations, deserialise_bus_row, raw_bus_row,
          h_is_real, h_opcode, h_selectors, eq_imm_b, eq_imm_c,
          h_reg_rd, h_reg_rs1, h_reg_rs2
        ]
        subst reg0 reg1 reg2
        rw [operation_list_effect_state_swap_writePC_writeReg]
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_b_value])]; simp
        conv => rhs; rw [operation_list_effect_state_writeReg_same (by grind [op_c_value])]; simp
        simp [bus_row, deserialise_bus_row, raw_bus_row, ALUBus.Spec, and_assoc, *] at h_wf_alu
        obtain ⟨ _ub_a0, _ub_a1, _ub_a2, _ub_a3, _h_operands, h_spec, _rest ⟩ := h_wf_alu
        simp [← h_spec, BitVec.ofNatLT_eq_ofNat, op_b_value, op_c_value]
        simp [h_selectors] at seq_constraints
        specialize seq_constraints (by simp at h_all_constraints; assumption)
        rw [seq_constraints.2.1]
      . simp [op_b_value, op_c_value] at *
        split_ands <;> [ simp; skip; aesop; aesop ]
        . simp [pc, h_pc, ← BitVec.toNat_inj, U64w.toNat]
          clear *- pc_npc_bounds; omega

  end MUL_FAMILY

end Equivalence
