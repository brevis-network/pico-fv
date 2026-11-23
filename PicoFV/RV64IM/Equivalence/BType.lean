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
    -- flags and the row's class selector, and no statement takes them.
    --
    -- A branch row reads `rs1` into `op_a` and `rs2` into `op_b` and writes
    -- both back unchanged (`op_a_kept`, constraint 13), so it writes no
    -- register. Its `op_c` is the 13-bit offset (`imm_c = 1`). The comparison
    -- runs on the ALU bus: `branch_compare_spec` gives the two bits `a_lt_b`
    -- and `a_gt_b` as the strict comparisons of the two operands, signed for
    -- `BLT` and `BGE` (opcode 264) and unsigned for the other four (265); the
    -- chip recovers equality as `1 - a_lt_b - a_gt_b`. The row's own taken
    -- predicate is `branch_taken`, and the next pc is `pc + offset` when it is
    -- 1 (`branch_taken_next_pc`, constraint 19) and `pc + 4` when it is 0
    -- (`branch_not_taken_next_pc`, constraint 37). Sail's success condition is
    -- that the target is 4-aligned on the taken branch alone, which
    -- `next_pc_mod_four_eq_zero` carries.
    --
    -- Pico source at the pinned v3.2.0, under `vm/src/chips/chips/riscv_cpu/`:
    --   * `op_a` keeps its previous value on a branch or store row:
    --     `register/constraints.rs:117-123`;
    --   * every branch row has `imm_c = 1`, and the taken target
    --     `next_pc = pc + offset`: `branch/constraints.rs:74-86`;
    --   * the comparison message on the ALU bus, opcode `SLT` or `SLTU` plus
    --     `LT_CMP_OPCODE_TAG`: `branch/constraints.rs:103-117`;
    --   * the taken predicate: `branch_taken_expr`, `constraints.rs:356-363`;
    --   * `next_pc = pc + 4` on a real row that is not a taken branch, a jump
    --     or a halt: `constraints.rs:318-326`.
    --
    -- The six column-form theorems (`equivalence_BEQ_row` to
    -- `equivalence_BGEU_row`) differ only in the comparison. Each derives the
    -- row's taken bit from the comparison bits and hands it, with its Sail
    -- lemmas, to `branch_equivalence`, which does the rest. The checked
    -- theorems, in decoded form, follow them.
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

    /-- The part of a branch theorem that does not depend on the comparison. A branch's Sail
        operations are a pc read, reads of `rs1` and `rs2`, and the write of
        `pc + (if cond then offset else 4)`, where `cond` is the branch's comparison of the two
        values (`h_spec`); `h_exec` is the opcode's `execute_*_equiv`. Given the row's
        selectors and its taken bit as `cond` of the `op_a` and `op_b` values (`h_taken`), the
        row's operations have the same effect: the branch writes no register, since `op_a`
        keeps the value it read (`op_a_kept`), and the next pc is the Sail increment
        (`branch_next_pc`), 4-aligned when the branch is taken (`next_pc_mod_four_eq_zero`). -/
    private lemma branch_equivalence
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (bo : bop)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_bop bo)
      (h_ecall : air.cols.opcode_selector.is_ecall row 0 = 0)
      (h_store : air.cols.opcode_selector.is_store row 0 = 0)
      (h_jalr : air.cols.opcode_selector.is_jalr row 0 = 0)
      (h_jal : air.cols.opcode_selector.is_jal row 0 = 0)
      (h_branch_sum :
        air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
          air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
          air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1)
      (spec :
        regidx → regidx → BitVec 13 → BitVec 64 → BitVec 64 → BitVec 64 → List Operation)
      (cond : BitVec 64 → BitVec 64 → Prop) [∀ a b, Decidable (cond a b)]
      (h_spec : ∀ r1 r2 imm pc_val r1_val r2_val, spec r1 r2 imm pc_val r1_val r2_val =
        [ .ReadPC pc_val, .ReadReg r1 r1_val, .ReadReg r2 r2_val,
          .WritePC (pc_val + if cond r1_val r2_val then BitVec.signExtend 64 imm else 4#64) ])
      (h_exec : ∀ {r1 r2 : regidx} {imm : BitVec 13} {pc_val r1_val r2_val : BitVec 64}
          {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
          {misa : BitVec 64},
        (operation_list_effect (spec r1 r2 imm pc_val r1_val r2_val) state).hypotheses →
        Sail.readReg Register.misa state = EStateM.Result.ok misa state →
        (cond r1_val r2_val → (pc_val + BitVec.signExtend 64 imm) % 4 = 0) →
        execute_instruction (instruction.BTYPE (imm, r2, r1, bo)) state =
          (operation_list_effect (spec r1 r2 imm pc_val r1_val r2_val) state).state)
      (h_taken : branch_taken air row =
        if cond (U64w.toBV (op_a_value air row)) (U64w.toBV (op_b_value air row)) then 1 else 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs1 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bo)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      obtain ⟨ h_imm_b, h_imm_c, - ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode
          (by cases bo <;> rfl) (by cases bo <;> rfl)
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs, h_op_c ⟩ :=
        branch_offset air row bo h_is_real h_wf h_constraints h_opcode h_imm_c
      -- `op_a` keeps the value it read, so the branch writes no register.
      have h_kept := op_a_kept air row h_constraints (by rw [h_branch_sum, h_store]; norm_num)
      have h_a_value :
          U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) := by
        simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1, h_kept.2.2.2]
      have h_next := branch_next_pc air row h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_ecall h_jal h_jalr h_branch_sum eq_c0 eq_c1 eq_cs h_op_c
        (decide (cond (U64w.toBV (op_a_value air row)) (U64w.toBV (op_b_value air row))))
        (by simp only [decide_eq_true_eq]; exact h_taken)
      simp only [decide_eq_true_eq] at h_next
      have h_align := next_pc_mod_four_eq_zero air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
      -- The row's messages, as operations on the Sail state.
      rw [CPU_bus_operations_eq_of_imm_c_eq_one air row h_is_real h_wf h_imm_b h_imm_c
            (by cases bo <;> simp [mem_width_of_opcode, h_opcode, Transpiler.opcode_of_bop])]
        at h_bus_hypotheses ⊢
      extract_lets rs1 rs2 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      simp at h_bus_hypotheses
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      rw [h_exec (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)]
      · rw [h_spec]
        simp [rs1, rs2]
        rw [operation_list_effect_state_writeReg_same h_read_b,
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same (by rw [h_a_value]; exact h_read_a),
            ← h_next]
      · rw [h_spec]
        simp [operation_list_effect, List.foldl, operation_effect, and_assoc]
        exact ⟨ h_pc_read, by rw [h_a_value]; simpa [rs1] using h_read_a,
                by simpa [rs2] using h_read_b ⟩
      · clear * - risc_v_assumptions
        simp [RISC_V_assumptions] at risc_v_assumptions
        tauto
      · intro h_c
        rw [show BitVec.signExtend 64 imm' =
              (if cond (U64w.toBV (op_a_value air row)) (U64w.toBV (op_b_value air row))
                then BitVec.signExtend 64 imm' else 4#64) from (if_pos h_c).symm,
            ← h_next]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod]
        simp [U64w.toBV_toNat, h_align.2]

    /-- `equivalence_BEQ` in column form: for a row of opcode 18, Sail's step on the `BEQ`
        whose registers and offset are read off the row's columns equals the row's effect. -/
    theorem equivalence_BEQ_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      obtain ⟨ -, -, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, -, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
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
      exact branch_equivalence air row .BEQ h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_opcode h_ecall h_store h_jalr h_jal h_branch_sum
        OpcodeSpec.RV64.spec_BEQ (fun a b => a = b)
        (fun _ _ _ _ _ _ => by simp [OpcodeSpec.RV64.spec_BEQ])
        OpcodeSpec.RV64.execute_BEQ_equiv h_taken
        h_bus_hypotheses risc_v_assumptions

    /-- `equivalence_BNE` in column form: for a row of opcode 19, Sail's step on the `BNE`
        whose registers and offset are read off the row's columns equals the row's effect. -/
    theorem equivalence_BNE_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      obtain ⟨ -, -, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, -, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
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
      exact branch_equivalence air row .BNE h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_opcode h_ecall h_store h_jalr h_jal h_branch_sum
        OpcodeSpec.RV64.spec_BNE (fun a b => ¬ a = b)
        (fun _ _ _ _ _ _ => by simp [OpcodeSpec.RV64.spec_BNE])
        OpcodeSpec.RV64.execute_BNE_equiv (by rw [ite_not]; exact h_taken)
        h_bus_hypotheses risc_v_assumptions

    /-- `equivalence_BLT` in column form: for a row of opcode 20, Sail's step on the `BLT`
        whose registers and offset are read off the row's columns equals the row's effect. -/
    theorem equivalence_BLT_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      obtain ⟨ -, -, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, -, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
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
      have h_taken : branch_taken air row =
          if U64w.toInt (op_a_value air row) < U64w.toInt (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        rw [h_lt_bit]
        simp [BitVec.slt]
      exact branch_equivalence air row .BLT h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_opcode h_ecall h_store h_jalr h_jal h_branch_sum
        OpcodeSpec.RV64.spec_BLT (fun a b => a.toInt < b.toInt)
        (fun _ _ _ _ _ _ => by simp [OpcodeSpec.RV64.spec_BLT])
        OpcodeSpec.RV64.execute_BLT_equiv (by simpa using h_taken)
        h_bus_hypotheses risc_v_assumptions

    /-- `equivalence_BGE` in column form: for a row of opcode 21, Sail's step on the `BGE`
        whose registers and offset are read off the row's columns equals the row's effect. -/
    theorem equivalence_BGE_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      obtain ⟨ -, -, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, -, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
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
      exact branch_equivalence air row .BGE h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_opcode h_ecall h_store h_jalr h_jal h_branch_sum
        OpcodeSpec.RV64.spec_BGE (fun a b => a.toInt ≥ b.toInt)
        (fun _ _ _ _ _ _ => by simp [OpcodeSpec.RV64.spec_BGE])
        OpcodeSpec.RV64.execute_BGE_equiv (by simpa using h_taken)
        h_bus_hypotheses risc_v_assumptions

    /-- `equivalence_BLTU` in column form: for a row of opcode 22, Sail's step on the `BLTU`
        whose registers and offset are read off the row's columns equals the row's effect. -/
    theorem equivalence_BLTU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      obtain ⟨ -, -, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, -, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
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
      have h_taken : branch_taken air row =
          if U64w.toNat (op_a_value air row) < U64w.toNat (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        rw [h_lt_bit]
        simp [BitVec.ult]
      exact branch_equivalence air row .BLTU h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_opcode h_ecall h_store h_jalr h_jal h_branch_sum
        OpcodeSpec.RV64.spec_BLTU (fun a b => a.toNat < b.toNat)
        (fun _ _ _ _ _ _ => by simp [OpcodeSpec.RV64.spec_BLTU])
        OpcodeSpec.RV64.execute_BLTU_equiv (by simpa using h_taken)
        h_bus_hypotheses risc_v_assumptions

    /-- `equivalence_BGEU` in column form: for a row of opcode 23, Sail's step on the `BGEU`
        whose registers and offset are read off the row's columns equals the row's effect. -/
    theorem equivalence_BGEU_row
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
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
      obtain ⟨ -, -, h_s ⟩ :=
        branch_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, -, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
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
      have h_taken : branch_taken air row =
          if U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row) then 1 else 0 := by
        rw [show branch_taken air row = 1 - air.cols.a_lt_b row 0 by
              simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]]
        by_cases h_ge : U64w.toNat (op_a_value air row) ≥ U64w.toNat (op_b_value air row)
        · rw [if_pos h_ge, h_lt_bit, if_neg (by simp [BitVec.ult]; omega)]
          norm_num
        · rw [if_neg h_ge, h_lt_bit, if_pos (by simp [BitVec.ult]; omega)]
          norm_num
      exact branch_equivalence air row .BGEU h_row h_is_real h_all_wf h_all_constraints
        pico_assumptions h_opcode h_ecall h_store h_jalr h_jal h_branch_sum
        OpcodeSpec.RV64.spec_BGEU (fun a b => a.toNat ≥ b.toNat)
        (fun _ _ _ _ _ _ => by simp [OpcodeSpec.RV64.spec_BGEU])
        OpcodeSpec.RV64.execute_BGEU_equiv (by simpa using h_taken)
        h_bus_hypotheses risc_v_assumptions

    -- ========================================================================
    -- The checked branch theorems, in decoded form: each takes the branch and
    -- an address whose decoding (`Transpiler.V3.transpile_op`, at
    -- multiplicity 1) is the row's Program message, and is proved from its
    -- column form.
    --
    -- The proofs pass hypotheses as `@h`. On the store and load sections,
    -- passing them as `@h` elaborated about 2.3 times faster than passing them
    -- bare. It does not avoid every unfolding: checking `@h_bus_hypotheses`
    -- against its expected type still unfolds `operation_list_effect`.
    -- ========================================================================

    /-- What a branch's decoding says about the row: it is real, its opcode is the branch's
        (`Transpiler.opcode_of_bop`), its `op_a` and `op_b` columns name `rs1` and `rs2`, and
        the low 13 bits of its `op_c` value are the offset. -/
    private lemma btype_decoded
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_constraints : CpuChip.Extraction.allHold air row)
      {imm : BitVec 13} {rs2 rs1 : regidx} {bo : bop} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, bo)) 1 addr =
        some (program_bus_entry air row, props))
    :
      air.cols.is_real row 0 = 1 ∧
      air.cols.instruction.opcode row 0 = Transpiler.opcode_of_bop bo ∧
      regidx.Regidx (air.cols.instruction.op_a row 0).val = rs1 ∧
      regidx.Regidx (air.cols.instruction.op_b_0 row 0).val = rs2 ∧
      (U64w.toBV (op_c_value air row)).setWidth 13 = imm
    := by
      simp only [Transpiler.V3.transpile_op, Option.some.injEq, Prod.mk.injEq] at h_decode
      have h_data := h_decode.1.symm
      have h_op_a : air.cols.instruction.op_a row 0 = Transpiler.reg_to_KB rs1 :=
        decoded_field h_data ProgramBusEntry.op_a
      have h_op_b : air.cols.instruction.op_b_0 row 0 = Transpiler.reg_to_KB rs2 :=
        decoded_field h_data ProgramBusEntry.b_0
      have h_op_c := op_c_value_eq_signExtend_of_imm_operand air row imm (by norm_num)
        (by norm_num) (decoded_field h_data ProgramBusEntry.imm_c) h_constraints
        (decoded_field h_data ProgramBusEntry.c_0) (decoded_field h_data ProgramBusEntry.c_1)
        (decoded_field h_data ProgramBusEntry.c_sign)
      exact ⟨ decoded_field h_data ProgramBusEntry.multiplicity,
        decoded_field h_data ProgramBusEntry.opcode,
        by rw [h_op_a]; exact regidx_reg_to_KB rs1, by rw [h_op_b]; exact regidx_reg_to_KB rs2,
        by rw [h_op_c]; exact setWidth_signExtend_self imm (by norm_num) ⟩

    /-- Equivalence for BEQ (opcode 18, `bop.BEQ`): for every `BEQ` instruction and address
        `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_BEQ
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 13} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, .BEQ)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BEQ)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        btype_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_BEQ_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- Equivalence for BNE (opcode 19, `bop.BNE`): for every `BNE` instruction and address
        `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_BNE
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 13} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, .BNE)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BNE)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        btype_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_BNE_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- Equivalence for BLT (opcode 20, `bop.BLT`): for every `BLT` instruction and address
        `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_BLT
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 13} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, .BLT)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BLT)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        btype_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_BLT_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- Equivalence for BGE (opcode 21, `bop.BGE`): for every `BGE` instruction and address
        `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_BGE
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 13} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, .BGE)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BGE)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        btype_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_BGE_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- Equivalence for BLTU (opcode 22, `bop.BLTU`): for every `BLTU` instruction and address
        `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_BLTU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 13} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, .BLTU)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BLTU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        btype_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_BLTU_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- Equivalence for BGEU (opcode 23, `bop.BGEU`): for every `BGEU` instruction and address
        `addr` whose decoding (`Transpiler.V3.transpile_op`, at multiplicity 1) is the row's
        Program message, Sail's step on that instruction equals the row's effect. The decoding
        fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. -/
    theorem equivalence_BGEU
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      {imm : BitVec 13} {rs2 rs1 : regidx} {addr : ℕ} {props : Prop}
      (h_decode : Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, .BGEU)) 1 addr =
        some (program_bus_entry air row, props))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BGEU)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      obtain ⟨ h_is_real, h_opcode, rfl, rfl, rfl ⟩ :=
        btype_decoded air row (h_all_constraints row h_row) h_decode
      exact equivalence_BGEU_row air row @h_row @h_is_real @h_all_wf
        @h_all_constraints @pico_assumptions @h_opcode @h_bus_hypotheses @risc_v_assumptions

    /-- The branch theorems' decoding hypothesis holds on every real row of a branch opcode:
        there the Program table's promise (in `bus_row_wf_asm`) gives a branch of the opcode's
        comparison and a 4-aligned address below `Transpiler.V3.code_address_bound` whose
        decoding is the row's Program message. -/
    theorem btype_decode_satisfiable
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (bo : bop)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = Transpiler.opcode_of_bop bo)
    :
      ∃ (imm : BitVec 13) (rs2 rs1 : regidx) (addr : ℕ) (props : Prop),
        addr % 4 = 0 ∧ addr < Transpiler.V3.code_address_bound ∧
        Transpiler.V3.transpile_op (.BTYPE (imm, rs2, rs1, bo)) 1 addr =
          some (program_bus_entry air row, props)
    := by
      obtain ⟨ instr, addr, props, h_al, h_lt, h_dec, h_from ⟩ :=
        program_bus_decoded air row @h_is_real @h_wf
      rw [h_opcode] at h_from
      cases bo <;>
      · obtain ⟨ imm, rs2, rs1, rfl ⟩ := h_from
        exact ⟨ imm, rs2, rs1, addr, props, h_al, h_lt, h_dec ⟩

  end BTYPE

end Equivalence
