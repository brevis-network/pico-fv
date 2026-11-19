import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 2_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section BTYPE

    -- ========================================================================
    -- BTYPE — the six branch opcodes: BEQ = 18, BNE = 19, BLT = 20,
    -- BGE = 21, BLTU = 22, BGEU = 23. None is shared
    -- (`ProgramBusEntry.decoded_from`), so the decoder fixes both immediate
    -- flags and the row's class selector, and no statement takes them; the 2.x
    -- statements did not take them either, so for these six the recorded text
    -- changes only in the contract names and in reading `rs1` from `op_a`.
    --
    -- A branch row reads `rs1` into `op_a` and `rs2` into `op_b` and writes
    -- both back unchanged (`op_a_kept`), so it writes no register. Its `op_c`
    -- is the 13-bit offset (`imm_c = 1`). The comparison runs on the ALU bus:
    -- `branch_compare_spec` gives the two bits `a_lt_b` and `a_gt_b` as the
    -- strict comparisons of the two operands, signed for `BLT` and `BGE`
    -- (opcode 264) and unsigned for the other four (265); the chip recovers
    -- equality as `1 - a_lt_b - a_gt_b`. The row's own taken predicate is
    -- `branch_taken`, and the next pc is `pc + offset` when it is 1
    -- (`branch_taken_next_pc`) and `pc + 4` when it is 0
    -- (`branch_not_taken_next_pc`). Sail's success condition is that the
    -- target is 4-aligned on the taken branch alone, which
    -- `next_pc_mod_four_eq_zero` carries.
    -- ========================================================================

    /-- A branch row's flags and selectors, as its opcode fixes them
        (`selector_exclusivity`): both `imm_b = 0` and `imm_c = 1` come from the decoder, and
        the class-selector vector is the opcode's row of `class_selectors_of_opcode`, which a
        caller with a literal opcode reads off by `simp`. -/
    private lemma branch_row_selectors
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {op : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = op)
      (h_b : imm_b_of_opcode op.val = some 0)
      (h_c : imm_c_of_opcode op.val = some 1)
    :
      air.cols.opcode_selector.imm_b row 0 = 0 ∧
      air.cols.opcode_selector.imm_c row 0 = 1 ∧
      #v[ air.cols.opcode_selector.is_ecall row 0
        , air.cols.opcode_selector.is_memory row 0
        , air.cols.opcode_selector.is_store row 0
        , air.cols.opcode_selector.is_beq row 0
        , air.cols.opcode_selector.is_bne row 0
        , air.cols.opcode_selector.is_blt row 0
        , air.cols.opcode_selector.is_bge row 0
        , air.cols.opcode_selector.is_bltu row 0
        , air.cols.opcode_selector.is_bgeu row 0
        , air.cols.opcode_selector.is_jalr row 0
        , air.cols.opcode_selector.is_jal row 0 ] =
        class_selectors_of_opcode op.val
    := by
      obtain ⟨ h_sel, h_imm_b, h_imm_c ⟩ :=
        selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
      rw [h_opcode] at h_sel h_imm_b h_imm_c
      exact ⟨ h_imm_b 0 h_b, h_imm_c 1 h_c, h_sel ⟩

    /-- A branch row's offset: the Program message says the row's `op_c` columns encode a
        13-bit immediate `imm'`, and `op_c` is then its 64-bit sign extension (constraints 4 to
        7, through `imm_c_eq_1_constraints`). The branch class is taken as a `bop` so the six
        opcodes share one proof. -/
    private lemma branch_offset
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (bo : bop)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_bop bo)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ imm' : BitVec 13,
        air.cols.instruction.op_c_0 row 0 = (Transpiler.V3.imm_operand imm' true)[0] ∧
        air.cols.instruction.op_c_1 row 0 = (Transpiler.V3.imm_operand imm' true)[1] ∧
        air.cols.instruction.op_c_sign row 0 = (Transpiler.V3.imm_operand imm' true)[2] ∧
        U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm'
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      cases bo <;>
      · simp [ProgramBusEntry.decoded_from, Transpiler.opcode_of_bop, h_opcode] at h_decoded
        obtain ⟨ imm', rs2', rs1', h_eq_instr ⟩ := h_decoded
        subst h_eq_instr
        simp [Transpiler.V3.transpile_op, Transpiler.opcode_of_bop, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, - ⟩ := h_eq
        subst h_eq_data
        rw [deserialise_program_bus_entry] at h_eq_entry
        simp [ProgramBusEntry.deserialise] at h_eq_entry
        have eq_c0 : air.cols.instruction.op_c_0 row 0 =
            (Transpiler.V3.imm_operand imm' true)[0] := by simp [h_eq_entry]
        have eq_c1 : air.cols.instruction.op_c_1 row 0 =
            (Transpiler.V3.imm_operand imm' true)[1] := by simp [h_eq_entry]
        have eq_cs : air.cols.instruction.op_c_sign row 0 =
            (Transpiler.V3.imm_operand imm' true)[2] := by simp [h_eq_entry]
        refine ⟨ imm', eq_c0, eq_c1, eq_cs, ?_ ⟩
        have h_imm_c_eqs := imm_c_eq_1_constraints air row h_imm_c h_constraints
        simp only [op_c_value, h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1,
                   h_imm_c_eqs.2.2.2, eq_c0, eq_c1, eq_cs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)

    /-- The operations a branch row's messages stand for, in order: the pc read, a read and
        write back of `rs2`, a read and write back of `rs1`, and the next pc. `op_c` is the
        offset, so it sends no message, and neither register changes. -/
    private lemma CPU_bus_operations_eq_of_branch
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_memory : air.cols.opcode_selector.is_memory row 0 = 0)
      (h_width : mem_width_of_opcode (air.cols.instruction.opcode row 0) = none)
    :
      CPU_bus_operations air row =
        [ .ReadPC (U64w.toBV (pc air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_prev_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC (U64w.toBV (next_pc air row)) ]
    := by
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      simp [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, deserialise_bus_row,
            raw_bus_row, MemoryBusEntry.deserialise, h_width,
            h_is_real, h_imm_b, h_imm_c, h_memory, h_reg_rd, h_reg_rs1 h_imm_b,
            BitVec.ofNatLT_eq_ofNat, toBV_pc_eq_ofNat air row h_is_real h_wf,
            op_a_prev_value, op_a_value, op_b_value]

    /-- A branch row's next pc, as Sail's increment: `pc + offset` when the branch is taken
        and `pc + 4` when it is not. `taken` is the row's own predicate, decided by the
        comparison bits; `branch_taken_next_pc` and `branch_not_taken_next_pc` give the two
        cases, and the 13-bit offset bound is what makes constraint 19 an exact 64-bit
        addition. -/
    private lemma branch_next_pc
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_ecall : air.cols.opcode_selector.is_ecall row 0 = 0)
      (h_jal : air.cols.opcode_selector.is_jal row 0 = 0)
      (h_jalr : air.cols.opcode_selector.is_jalr row 0 = 0)
      (h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1)
      {imm' : BitVec 13}
      (eq_c0 : air.cols.instruction.op_c_0 row 0 = (Transpiler.V3.imm_operand imm' true)[0])
      (eq_c1 : air.cols.instruction.op_c_1 row 0 = (Transpiler.V3.imm_operand imm' true)[1])
      (eq_cs : air.cols.instruction.op_c_sign row 0 = (Transpiler.V3.imm_operand imm' true)[2])
      (h_op_c : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm')
      (taken : Bool)
      (h_taken : branch_taken air row = if taken then 1 else 0)
    :
      U64w.toBV (next_pc air row) =
        U64w.toBV (pc air row) + (if taken then BitVec.signExtend 64 imm' else 4#64)
    := by
      have h_bounds := imm_operand_offset_bounds (w := 13) (by norm_num) (by norm_num) imm'
      cases taken with
      | true =>
        simp only [if_true]
        rw [← h_op_c]
        exact branch_taken_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_branch_sum (by simpa using h_taken)
          (by rw [eq_c0, eq_c1, eq_cs]; exact h_bounds.1)
          (by rw [eq_c0, eq_c1, eq_cs]; exact h_bounds.2)
      | false =>
        simp only [Bool.false_eq_true, if_false]
        exact branch_not_taken_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions (by simpa using h_taken) h_jal h_jalr
          (is_halt_eq_zero_of_no_ecall air row h_ecall (h_all_constraints row h_row))

    /-- Equivalence for BEQ (opcode 18, `bop.BEQ`). -/
    theorem equivalence_BEQ
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 18)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BEQ)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row .BEQ h_is_real h_wf h_constraints h_opcode h_imm_c
      have h_branch_sum :
          air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
            air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
            air.cols.opcode_selector.is_bltu row 0 +
            air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]; norm_num
      -- The comparison bits, unsigned (opcode 265).
      have h_cmp := (branch_compare_spec air row h_is_real h_wf h_branch_sum).2
        (by rw [h_blt, h_bge]; norm_num)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_cmp
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).ult (U64w.toBV (op_b_value air row)) = true
            then 1 else 0 := h_cmp.2.1
      have h_gt_bit : air.cols.a_gt_b row 0 =
          if (U64w.toBV (op_b_value air row)).ult (U64w.toBV (op_a_value air row)) = true
            then 1 else 0 := h_cmp.2.2
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      have h_a_value : U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      -- The row's predicate: taken exactly when the two values are equal.
      have h_taken : branch_taken air row =
          if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row) then 1 else 0 := by
        by_cases h_vals : U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
        · have h_lt0 : air.cols.a_lt_b row 0 = 0 := by
            rw [h_lt_bit, if_neg (by simp [BitVec.ult, h_vals])]
          have h_gt0 : air.cols.a_gt_b row 0 = 0 := by
            rw [h_gt_bit, if_neg (by simp [BitVec.ult, h_vals])]
          rw [if_pos h_vals]
          simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_lt0, h_gt0]
        · rw [if_neg h_vals]
          have h_ne : U64w.toNat (op_a_value air row) ≠ U64w.toNat (op_b_value air row) := by
            intro h
            exact h_vals (BitVec.eq_of_toNat_eq (by simpa using h))
          rcases Nat.lt_or_ge (U64w.toNat (op_a_value air row))
            (U64w.toNat (op_b_value air row)) with h | h
          · have h_lt1 : air.cols.a_lt_b row 0 = 1 := by
              rw [h_lt_bit, if_pos (by simp [BitVec.ult]; omega)]
            have h_gt0 : air.cols.a_gt_b row 0 = 0 := by
              rw [h_gt_bit, if_neg (by simp [BitVec.ult]; omega)]
            simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_lt1, h_gt0]
          · have h_lt0 : air.cols.a_lt_b row 0 = 0 := by
              rw [h_lt_bit, if_neg (by simp [BitVec.ult]; omega)]
            have h_gt1 : air.cols.a_gt_b row 0 = 1 := by
              rw [h_gt_bit, if_pos (by simp [BitVec.ult]; omega)]
            simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_lt0, h_gt1]
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) +
            (if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
              then BitVec.signExtend 64 imm' else 4#64) := by
        simpa using branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
          (decide (U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)))
          (by simpa using h_taken)
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_branch air row h_is_real h_wf h_imm_b h_imm_c h_memory
            (by simp [mem_width_of_opcode, h_opcode])] at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [OpcodeSpec.RV64.execute_BEQ_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · simp [OpcodeSpec.RV64.spec_BEQ, rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [OpcodeSpec.RV64.spec_BEQ_hypotheses]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_vals
        rw [show BitVec.signExtend 64 imm' =
              (if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
                then BitVec.signExtend 64 imm' else 4#64) from by rw [if_pos h_vals]]
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

    /-- Equivalence for BNE (opcode 19, `bop.BNE`). -/
    theorem equivalence_BNE
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 19)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BNE)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row .BNE h_is_real h_wf h_constraints h_opcode h_imm_c
      have h_branch_sum :
          air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
            air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
            air.cols.opcode_selector.is_bltu row 0 +
            air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]; norm_num
      -- The comparison bits, unsigned (opcode 265).
      have h_cmp := (branch_compare_spec air row h_is_real h_wf h_branch_sum).2
        (by rw [h_blt, h_bge]; norm_num)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_cmp
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).ult (U64w.toBV (op_b_value air row)) = true
            then 1 else 0 := h_cmp.2.1
      have h_gt_bit : air.cols.a_gt_b row 0 =
          if (U64w.toBV (op_b_value air row)).ult (U64w.toBV (op_a_value air row)) = true
            then 1 else 0 := h_cmp.2.2
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      have h_a_value : U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      have h_taken : branch_taken air row =
          if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row) then 0 else 1 := by
        by_cases h_vals : U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
        · have h_lt0 : air.cols.a_lt_b row 0 = 0 := by
            rw [h_lt_bit, if_neg (by simp [BitVec.ult, h_vals])]
          have h_gt0 : air.cols.a_gt_b row 0 = 0 := by
            rw [h_gt_bit, if_neg (by simp [BitVec.ult, h_vals])]
          rw [if_pos h_vals]
          simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_lt0, h_gt0]
        · rw [if_neg h_vals]
          have h_ne : U64w.toNat (op_a_value air row) ≠ U64w.toNat (op_b_value air row) := by
            intro h
            exact h_vals (BitVec.eq_of_toNat_eq (by simpa using h))
          rcases Nat.lt_or_ge (U64w.toNat (op_a_value air row))
            (U64w.toNat (op_b_value air row)) with h | h
          · have h_lt1 : air.cols.a_lt_b row 0 = 1 := by
              rw [h_lt_bit, if_pos (by simp [BitVec.ult]; omega)]
            have h_gt0 : air.cols.a_gt_b row 0 = 0 := by
              rw [h_gt_bit, if_neg (by simp [BitVec.ult]; omega)]
            simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_lt1, h_gt0]
          · have h_lt0 : air.cols.a_lt_b row 0 = 0 := by
              rw [h_lt_bit, if_neg (by simp [BitVec.ult]; omega)]
            have h_gt1 : air.cols.a_gt_b row 0 = 1 := by
              rw [h_gt_bit, if_pos (by simp [BitVec.ult]; omega)]
            simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_lt0, h_gt1]
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + (if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row) then 4#64 else BitVec.signExtend 64 imm') := by
        simpa using branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
          (decide (¬ (U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)))) (by simpa using h_taken)
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_branch air row h_is_real h_wf h_imm_b h_imm_c h_memory
            (by simp [mem_width_of_opcode, h_opcode])] at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [OpcodeSpec.RV64.execute_BNE_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · simp [OpcodeSpec.RV64.spec_BNE, rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [OpcodeSpec.RV64.spec_BNE_hypotheses]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_vals
        rw [show BitVec.signExtend 64 imm' =
              (if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row) then 4#64 else BitVec.signExtend 64 imm') from by rw [if_neg h_vals]]
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

    /-- Equivalence for BLT (opcode 20, `bop.BLT`). -/
    theorem equivalence_BLT
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 20)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row .BLT h_is_real h_wf h_constraints h_opcode h_imm_c
      have h_branch_sum :
          air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
            air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
            air.cols.opcode_selector.is_bltu row 0 +
            air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]; norm_num
      -- The comparison bits, signed (opcode 264).
      have h_cmp := (branch_compare_spec air row h_is_real h_wf h_branch_sum).1
        (by rw [h_blt, h_bge]; norm_num)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_cmp
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).slt (U64w.toBV (op_b_value air row)) = true
            then 1 else 0 := h_cmp.2.1
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      have h_a_value : U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      have h_taken : branch_taken air row =
          if U64w.toInt (op_a_value air row) < U64w.toInt (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        rw [h_lt_bit]
        simp [BitVec.slt]
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + (if U64w.toInt (op_a_value air row) < U64w.toInt (op_b_value air row) then BitVec.signExtend 64 imm' else 4#64) := by
        simpa using branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
          (decide (U64w.toInt (op_a_value air row) < U64w.toInt (op_b_value air row))) (by simpa using h_taken)
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_branch air row h_is_real h_wf h_imm_b h_imm_c h_memory
            (by simp [mem_width_of_opcode, h_opcode])] at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [OpcodeSpec.RV64.execute_BLT_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · simp [OpcodeSpec.RV64.spec_BLT, rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [OpcodeSpec.RV64.spec_BLT_hypotheses]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_vals
        rw [show BitVec.signExtend 64 imm' =
              (if U64w.toInt (op_a_value air row) < U64w.toInt (op_b_value air row)
                then BitVec.signExtend 64 imm' else 4#64) from by
            rw [if_pos (by simpa using h_vals)]]
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

    /-- Equivalence for BGE (opcode 21, `bop.BGE`). -/
    theorem equivalence_BGE
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 21)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BGE)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row .BGE h_is_real h_wf h_constraints h_opcode h_imm_c
      have h_branch_sum :
          air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
            air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
            air.cols.opcode_selector.is_bltu row 0 +
            air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]; norm_num
      -- The comparison bits, signed (opcode 264).
      have h_cmp := (branch_compare_spec air row h_is_real h_wf h_branch_sum).1
        (by rw [h_blt, h_bge]; norm_num)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_cmp
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).slt (U64w.toBV (op_b_value air row)) = true
            then 1 else 0 := h_cmp.2.1
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      have h_a_value : U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      have h_taken : branch_taken air row =
          if U64w.toInt (op_a_value air row) ≥ U64w.toInt (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = 1 - air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        by_cases h_ge : U64w.toInt (op_a_value air row) ≥ U64w.toInt (op_b_value air row)
        · rw [if_pos h_ge, h_lt_bit,
              if_neg (by simp only [BitVec.slt, decide_eq_true_eq, not_lt]; simpa using h_ge)]
          norm_num
        · rw [if_neg h_ge, h_lt_bit,
              if_pos (by simp only [BitVec.slt, decide_eq_true_eq]
                         simpa using Int.not_le.mp h_ge)]
          norm_num
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + (if U64w.toInt (op_a_value air row) ≥ U64w.toInt (op_b_value air row) then BitVec.signExtend 64 imm' else 4#64) := by
        simpa using branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
          (decide (U64w.toInt (op_a_value air row) ≥ U64w.toInt (op_b_value air row))) (by simpa using h_taken)
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_branch air row h_is_real h_wf h_imm_b h_imm_c h_memory
            (by simp [mem_width_of_opcode, h_opcode])] at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [OpcodeSpec.RV64.execute_BGE_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · simp [OpcodeSpec.RV64.spec_BGE, rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [OpcodeSpec.RV64.spec_BGE_hypotheses]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_vals
        rw [show BitVec.signExtend 64 imm' =
              (if U64w.toInt (op_a_value air row) ≥ U64w.toInt (op_b_value air row)
                then BitVec.signExtend 64 imm' else 4#64) from by
            rw [if_pos (by simpa using h_vals)]]
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

    /-- Equivalence for BLTU (opcode 22, `bop.BLTU`). -/
    theorem equivalence_BLTU
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 22)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row .BLTU h_is_real h_wf h_constraints h_opcode h_imm_c
      have h_branch_sum :
          air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
            air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
            air.cols.opcode_selector.is_bltu row 0 +
            air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]; norm_num
      -- The comparison bits, unsigned (opcode 265).
      have h_cmp := (branch_compare_spec air row h_is_real h_wf h_branch_sum).2
        (by rw [h_blt, h_bge]; norm_num)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_cmp
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).ult (U64w.toBV (op_b_value air row)) = true
            then 1 else 0 := h_cmp.2.1
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      have h_a_value : U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      have h_taken : branch_taken air row =
          if U64w.toNat (op_a_value air row) < U64w.toNat (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        rw [h_lt_bit]
        simp [BitVec.ult]
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + (if U64w.toNat (op_a_value air row) < U64w.toNat (op_b_value air row) then BitVec.signExtend 64 imm' else 4#64) := by
        simpa using branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
          (decide (U64w.toNat (op_a_value air row) < U64w.toNat (op_b_value air row))) (by simpa using h_taken)
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_branch air row h_is_real h_wf h_imm_b h_imm_c h_memory
            (by simp [mem_width_of_opcode, h_opcode])] at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [OpcodeSpec.RV64.execute_BLTU_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · simp [OpcodeSpec.RV64.spec_BLTU, rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [OpcodeSpec.RV64.spec_BLTU_hypotheses]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_vals
        rw [show BitVec.signExtend 64 imm' =
              (if U64w.toNat (op_a_value air row) < U64w.toNat (op_b_value air row)
                then BitVec.signExtend 64 imm' else 4#64) from by
            rw [if_pos (by simpa using h_vals)]]
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

    /-- Equivalence for BGEU (opcode 23, `bop.BGEU`). -/
    theorem equivalence_BGEU
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
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 23)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BGEU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row .BGEU h_is_real h_wf h_constraints h_opcode h_imm_c
      have h_branch_sum :
          air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
            air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
            air.cols.opcode_selector.is_bltu row 0 +
            air.cols.opcode_selector.is_bgeu row 0 = 1 := by
        rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]; norm_num
      -- The comparison bits, unsigned (opcode 265).
      have h_cmp := (branch_compare_spec air row h_is_real h_wf h_branch_sum).2
        (by rw [h_blt, h_bge]; norm_num)
      simp [RV64IM_Interactions.ALUBus.Spec] at h_cmp
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).ult (U64w.toBV (op_b_value air row)) = true
            then 1 else 0 := h_cmp.2.1
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      have h_a_value : U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      have h_taken : branch_taken air row =
          if U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = 1 - air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        by_cases h_ge : U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row)
        · rw [if_pos h_ge, h_lt_bit, if_neg (by simp [BitVec.ult]; omega)]
          norm_num
        · rw [if_neg h_ge, h_lt_bit, if_pos (by simp [BitVec.ult]; omega)]
          norm_num
      have h_next : U64w.toBV (next_pc air row) =
          U64w.toBV (pc air row) + (if U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row) then BitVec.signExtend 64 imm' else 4#64) := by
        simpa using branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
          pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
          (decide (U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row))) (by simpa using h_taken)
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_branch air row h_is_real h_wf h_imm_b h_imm_c h_memory
            (by simp [mem_width_of_opcode, h_opcode])] at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [OpcodeSpec.RV64.execute_BGEU_equiv
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · simp [OpcodeSpec.RV64.spec_BGEU, rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [OpcodeSpec.RV64.spec_BGEU_hypotheses]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_vals
        rw [show BitVec.signExtend 64 imm' =
              (if U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row)
                then BitVec.signExtend 64 imm' else 4#64) from by
            rw [if_pos (by simpa using h_vals)]]
        rw [← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

  end BTYPE

end Equivalence
