import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.RVSail.Opcodes.Opcodes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSectionVars false

/-! # Trial proofs against the Pico v3.1.1 CPU chip (prototype, not for merging)

    Three instruction theorems (ADD, BEQ, JALR) over the 58-column chip, the 3.x contracts
    (`RVSail/BusesV3.lean`) and the 3.x whole-trace assumption below. They check that the
    contracts and the assumption are strong enough before the real work starts. -/

namespace Equivalence.TrialV3

  open Plonky3
  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open Interaction

  section Plumbing

    variable [Field ExtF]

    /-- The row's messages, sorted by contract. -/
    def bus_row (air : Valid_CpuChip FKB ExtF) (row : ℕ) : BusRow :=
      deserialise_bus_row (raw_bus_row air row)

    /-- The instruction-fetch message of a row (multiplicity `is_real`). -/
    def program_bus_entry (air : Valid_CpuChip FKB ExtF) (row : ℕ) : FKB × Vector FKB 26 :=
      ( air.cols.is_real row 0,
        #v[ air.cols.pc_0 row 0, air.cols.pc_1 row 0,
            air.cols.instruction.opcode row 0, air.cols.instruction.opcode row 0,
            air.cols.instruction.op_a_0 row 0,
            air.cols.instruction.op_b_0 row 0, air.cols.instruction.op_b_1 row 0,
            air.cols.instruction.op_b_sign row 0,
            air.cols.instruction.op_c_0 row 0, air.cols.instruction.op_c_1 row 0,
            air.cols.instruction.op_c_sign row 0,
            air.cols.instruction.op_a_is_x0 row 0,
            air.cols.opcode_selector.imm_b row 0, air.cols.opcode_selector.imm_c row 0,
            air.cols.opcode_selector.is_ecall row 0, air.cols.opcode_selector.is_memory row 0,
            air.cols.opcode_selector.is_store row 0,
            air.cols.opcode_selector.is_beq row 0, air.cols.opcode_selector.is_bne row 0,
            air.cols.opcode_selector.is_blt row 0, air.cols.opcode_selector.is_bge row 0,
            air.cols.opcode_selector.is_bltu row 0, air.cols.opcode_selector.is_bgeu row 0,
            air.cols.opcode_selector.is_jalr row 0, air.cols.opcode_selector.is_jal row 0,
            air.cols.pc_carry row 0 ] )

    lemma bus_row_Program (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
        (bus_row air row).Program = [ProgramBusEntry.deserialise (program_bus_entry air row)] := by
      simp [bus_row, deserialise_bus_row, raw_bus_row, program_bus_entry]

    /-- A row's pc as a number: two 16-bit pieces. -/
    def pc_val (air : Valid_CpuChip FKB ExtF) (row : ℕ) : ℕ :=
      (air.cols.pc_0 row 0).val + 65536 * (air.cols.pc_1 row 0).val

    /-- A row's `next_pc` as a number. -/
    def next_pc_val (air : Valid_CpuChip FKB ExtF) (row : ℕ) : ℕ :=
      (air.cols.next_pc_0 row 0).val + 65536 * (air.cols.next_pc_1 row 0).val

    def op_a_value (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0,
          air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0 ]

    def op_b_value (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_b_access.access.value_0 row 0, air.cols.op_b_access.access.value_1 row 0,
          air.cols.op_b_access.access.value_2 row 0, air.cols.op_b_access.access.value_3 row 0 ]

    def op_c_value (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_c_access.access.value_0 row 0, air.cols.op_c_access.access.value_1 row 0,
          air.cols.op_c_access.access.value_2 row 0, air.cols.op_c_access.access.value_3 row 0 ]

    /-- The row's operations: its messages', then the write of `next_pc`. -/
    def CPU_bus_operations (air : Valid_CpuChip FKB ExtF) (row : ℕ) : List Operation :=
      bus_operations (bus_row air row) ++
      [ .WritePC (BitVec.ofNat 64 (next_pc_val air row)) ]

    /-- The 3.x whole-trace assumption about the public final pc (`next_pc`, public values
        43 and 44; the chip pins 45 to zero itself): it is 4-aligned, its two pieces are
        16-bit, and it is below the guest address bound. Pico's recursion makes it either the
        next chunk's first pc, which is a Program-table pc, or zero. -/
    def pico_CpuChip_control_flow_assumptions (air : Valid_CpuChip FKB ExtF) : Prop :=
      (air.public_values 43).val % 4 = 0 ∧
      (air.public_values 43).val < 65536 ∧
      (air.public_values 44).val < 65536 ∧
      (air.public_values 43).val + 65536 * (air.public_values 44).val < 0x7800_0000

  end Plumbing

  section Rotation

    variable [Field ExtF]

    lemma pc_0_rotation (air : Valid_CpuChip FKB ExtF) (row rotation : ℕ) :
        air.cols.pc_0 row rotation = air.cols.pc_0 ((row + rotation) % (air.last_row + 1)) 0 := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.pc_0 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 2 row rotation
      have valid_col : ∀ row rotation, air.col_2 row rotation := by aesop
      unfold Raw_CpuChip.col_2 at valid_col
      iterate 2 rw [valid_col] at valid_circuit
      clear valid_col
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_2 row rotation := by aesop
      unfold Raw_CpuCols.col_2 at valid_cols
      clear *- valid_circuit valid_cols
      grind

    lemma pc_1_rotation (air : Valid_CpuChip FKB ExtF) (row rotation : ℕ) :
        air.cols.pc_1 row rotation = air.cols.pc_1 ((row + rotation) % (air.last_row + 1)) 0 := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.pc_1 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 3 row rotation
      have valid_col : ∀ row rotation, air.col_3 row rotation := by aesop
      unfold Raw_CpuChip.col_3 at valid_col
      iterate 2 rw [valid_col] at valid_circuit
      clear valid_col
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_3 row rotation := by aesop
      unfold Raw_CpuCols.col_3 at valid_cols
      clear *- valid_circuit valid_cols
      grind

    lemma is_real_rotation (air : Valid_CpuChip FKB ExtF) (row rotation : ℕ) :
        air.cols.is_real row rotation = air.cols.is_real ((row + rotation) % (air.last_row + 1)) 0 := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.is_real Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 53 row rotation
      have valid_col : ∀ row rotation, air.col_53 row rotation := by aesop
      unfold Raw_CpuChip.col_53 at valid_col
      iterate 2 rw [valid_col] at valid_circuit
      clear valid_col
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_53 row rotation := by aesop
      unfold Raw_CpuCols.col_53 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  end Rotation

  section ProgramFacts

    variable [Field ExtF]

    /-- On a real row the Program contract holds for the row's own fetch message. -/
    lemma program_wf
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_wf : bus_row_wf_asm (bus_row air row)) :
        ∃ instr pc data props,
          pc % 4 = 0 ∧ pc < Transpiler.V3.code_address_bound ∧
          Transpiler.V3.transpile_op instr 1 pc = .some (data, props) ∧
          ProgramBusEntry.deserialise (program_bus_entry air row) = ProgramBusEntry.deserialise data ∧
          props := by
      simp only [bus_row_wf_asm, bus_row_Program] at h_wf
      simp [program_bus_entry, h_is_real] at h_wf
      have h_prog := h_wf.1
      simp only [ProgramBusEntry.operand_properties] at h_prog
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, h_props ⟩ := h_prog
      refine ⟨ instr, pc, data, props, h_al, h_lt, h_tr.symm, ?_, h_props ⟩
      simpa [program_bus_entry, h_is_real] using h_eq

    /-- The pc facts the Program table delivers: on a real row the pc is a 4-aligned guest
        address below `0x7800_0000`, held as two 16-bit pieces, and `pc_carry` is
        `[pc[0] >= 0xFFFC]`. -/
    lemma pc_facts
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_wf : bus_row_wf_asm (bus_row air row)) :
        (air.cols.pc_0 row 0).val < 65536 ∧
        (air.cols.pc_1 row 0).val < 65536 ∧
        (air.cols.pc_0 row 0).val % 4 = 0 ∧
        pc_val air row < 0x7800_0000 ∧
        air.cols.pc_carry row 0 = (if 0xFFFC ≤ (air.cols.pc_0 row 0).val then 1 else 0) := by
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, _ ⟩ :=
        program_wf air row h_is_real h_wf
      have h_fields :
          air.cols.pc_0 row 0 = data.2[0] ∧ air.cols.pc_1 row 0 = data.2[1] ∧
          air.cols.pc_carry row 0 = data.2[25] := by
        simp [program_bus_entry, ProgramBusEntry.deserialise] at h_eq
        grind
      have h_data :
          data.2[0] = Transpiler.V3.pc_lo pc ∧ data.2[1] = Transpiler.V3.pc_hi pc ∧
          data.2[25] = Transpiler.V3.pc_carry pc := by
        cases instr <;> simp [Transpiler.V3.transpile_op] at h_tr <;>
          (try split at h_tr) <;> (try simp at h_tr) <;>
          (try (obtain ⟨ h_tr, _ ⟩ := h_tr; subst h_tr; simp))
      obtain ⟨ e0, e1, e25 ⟩ := h_fields
      obtain ⟨ d0, d1, d25 ⟩ := h_data
      simp only [Transpiler.V3.code_address_bound] at h_lt
      simp only [pc_val, e0, e1, e25, d0, d1, d25, Transpiler.V3.pc_lo, Transpiler.V3.pc_hi,
                 Transpiler.V3.pc_carry]
      refine ⟨ by omega, by omega, by omega, by omega, ?_ ⟩
      simp


    /-- The constraints of a row, one by one. -/
    lemma row_constraints
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h : CpuChip.Extraction.allHold air row) :
        List.Forall (·) (row_constraint_list air row) :=
      ((allHold_iff_allHold_simplified air row).mp h).2

    /-- What `next_pc` is on a real row: the next row's pc, which the Program table pins, or,
        on the last real row, the public final pc, which the whole-trace assumption pins.
        Either way it has two 16-bit pieces, is 4-aligned and is below `0x7800_0000`. -/
    lemma next_pc_facts
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_row : row ≤ air.last_row)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
        (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
        (h_pv : pico_CpuChip_control_flow_assumptions air) :
        (air.cols.next_pc_0 row 0).val < 65536 ∧
        (air.cols.next_pc_1 row 0).val < 65536 ∧
        (air.cols.next_pc_0 row 0).val % 4 = 0 ∧
        next_pc_val air row < 0x7800_0000 := by
      have hc := row_constraints air row (h_all_constraints row h_row)
      simp only [row_constraint_list, List.forall_cons, List.Forall] at hc
      obtain ⟨ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
               _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
               _, c41, c42, _, _, _, c46, c47, _, _, c50, c51, _ ⟩ := hc
      simp only [pico_CpuChip_control_flow_assumptions] at h_pv
      -- On the last real row, `next_pc` is the public final pc.
      have h_from_pv : air.cols.is_last row 0 = 1 →
          (air.cols.next_pc_0 row 0).val < 65536 ∧
          (air.cols.next_pc_1 row 0).val < 65536 ∧
          (air.cols.next_pc_0 row 0).val % 4 = 0 ∧
          next_pc_val air row < 0x7800_0000 := by
        intro h_last
        simp only [constraint_41, constraint_42, h_last, one_mul, sub_eq_zero] at c41 c42
        simp only [next_pc_val, ← c41, ← c42]
        omega
      by_cases h_end : row = air.last_row
      · apply h_from_pv
        simp only [constraint_51, Circuit.isLastRow, Circuit.last_row] at c51
        simp [h_end, sub_eq_zero] at c51
        rw [← h_end] at c51
        rw [c51, h_is_real]
      · have h_trans : Circuit.isTransitionRow air row = 1 := by
          simp [Circuit.isTransitionRow, Circuit.last_row]; exact h_end
        have h_next : row + 1 ≤ air.last_row := by omega
        have h_mod : (row + 1) % (air.last_row + 1) = row + 1 := Nat.mod_eq_of_lt (by omega)
        have h_nr : air.cols.is_real row 1 = air.cols.is_real (row + 1) 0 := by
          rw [is_real_rotation, h_mod]
        have hn := row_constraints air (row + 1) (h_all_constraints (row + 1) h_next)
        simp only [row_constraint_list, List.forall_cons, List.Forall] at hn
        have c12n := hn.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [constraint_12] at c12n
        rcases mul_eq_zero.mp c12n with h0 | h1
        · -- The next row is padding: this is the last real row.
          apply h_from_pv
          simp only [constraint_50, h_trans, one_mul, sub_eq_zero, h_nr, h0, h_is_real,
                     sub_zero] at c50
          exact c50
        · -- The next row is real: `next_pc` is its pc.
          have h_real' : air.cols.is_real (row + 1) 0 = 1 := by
            rw [sub_eq_zero] at h1; exact h1
          simp only [constraint_46, constraint_47, h_trans, h_nr, h_real', one_mul,
                     sub_eq_zero] at c46 c47
          rw [pc_0_rotation, h_mod] at c46
          rw [pc_1_rotation, h_mod] at c47
          have hp := pc_facts air (row + 1) h_real' (h_all_wf (row + 1) h_next)
          simp only [pc_val] at hp
          simp only [next_pc_val, ← c46, ← c47]
          omega

  end ProgramFacts

  section Decoder

    /-- The Program table's operand form of a sign-extended immediate of at most 32 bits: the two
        low 16-bit pieces of the 64-bit value, and a sign bit that is 0 for a value below `2^31`
        and 1 for a value in the top `2^31` of the 64-bit range. -/
    lemma imm_operand_sext {w : ℕ} (imm : BitVec w) (hw0 : 0 < w) (hw : w ≤ 32) :
        let o := Transpiler.V3.imm_operand imm true
        let sx := (BitVec.signExtend 64 imm).toNat
        o[0].val = sx % 65536 ∧ o[1].val = sx / 65536 % 65536 ∧
        ((o[2] = 0 ∧ sx < 2^31) ∨ (o[2] = 1 ∧ 2^64 - 2^31 ≤ sx ∧ sx < 2^64)) := by
      intro o sx
      have h_w : 2^w ≤ 2^32 := Nat.pow_le_pow_right (by norm_num) hw
      have h_lt : imm.toNat < 2^w := imm.isLt
      have h_half : 2^w = 2 * 2^(w-1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have h_sx : sx = imm.toNat + if imm.msb then 2^64 - 2^w else 0 := by
        simp only [sx, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
        rw [Nat.mod_eq_of_lt (by omega)]
      have h_msb : imm.msb = decide (2^(w-1) ≤ imm.toNat) := BitVec.msb_eq_decide imm
      have h_sx_lt : sx < 2^64 := (BitVec.signExtend 64 imm).isLt
      have h_msb64 : (BitVec.signExtend 64 imm).msb = decide (2^63 ≤ sx) := BitVec.msb_eq_decide _
      simp only [o, Transpiler.V3.imm_operand, Transpiler.imm_to_KB, BitVec.extend, U64w.fromNat]
      simp only [ite_true, h_msb64]
      simp
      refine ⟨ rfl, rfl, ?_ ⟩
      by_cases hm : imm.msb
      · simp [hm] at h_sx h_msb
        right
        refine ⟨ ?_, by omega, h_sx_lt ⟩
        omega
      · simp [hm] at h_sx h_msb
        left
        refine ⟨ ?_, by omega ⟩
        omega

    /-- A row with opcode 0 and no immediate operand is R-type ADD. -/
    lemma add_inversion
        (h_tr : Transpiler.V3.transpile_op instr 1 pc = .some (data, props))
        (h_op : data.2[2] = 0) (h_ic : data.2[13] = 0) :
        ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .ADD) := by
      cases instr <;> simp [Transpiler.V3.transpile_op] at h_tr <;>
        (try split at h_tr) <;> (try simp at h_tr) <;>
        (try (obtain ⟨ h_tr, _ ⟩ := h_tr; subst h_tr; simp at h_op h_ic))
      all_goals (try (exfalso; tauto))
      all_goals
        rename_i x _ _
        obtain ⟨ rs2, rs1, rd, op ⟩ := x
        cases op <;> simp [Transpiler.opcode_of_rop, Transpiler.opcode_of_ropw] at h_op ⊢

    /-- A row with opcode 18 is BEQ. -/
    lemma beq_inversion
        (h_tr : Transpiler.V3.transpile_op instr 1 pc = .some (data, props))
        (h_op : data.2[2] = 18) :
        ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BEQ) := by
      cases instr <;> simp [Transpiler.V3.transpile_op] at h_tr <;>
        (try split at h_tr) <;> (try simp at h_tr) <;>
        (try (obtain ⟨ h_tr, _ ⟩ := h_tr; subst h_tr; simp at h_op))
      all_goals (try (rename_i x _ _; obtain ⟨ a, b, c, op ⟩ := x; cases op <;>
        simp [Transpiler.opcode_of_rop, Transpiler.opcode_of_ropw, Transpiler.opcode_of_iop,
              Transpiler.opcode_of_sop, Transpiler.opcode_of_sopw, Transpiler.opcode_of_bop] at h_op ⊢))
      all_goals (exfalso; split at h_op <;> simp at h_op)


    /-- A row with opcode 25 is JALR. -/
    lemma jalr_inversion
        (h_tr : Transpiler.V3.transpile_op instr 1 pc = .some (data, props))
        (h_op : data.2[2] = 25) :
        ∃ imm rs1 rd, instr = .JALR (imm, rs1, rd) := by
      cases instr <;> simp [Transpiler.V3.transpile_op] at h_tr <;>
        (try split at h_tr) <;> (try simp at h_tr) <;>
        (try (obtain ⟨ h_tr, _ ⟩ := h_tr; subst h_tr; simp at h_op))
      all_goals (try (rename_i x _ _; obtain ⟨ a, b, c, op ⟩ := x; cases op <;>
        simp [Transpiler.opcode_of_rop, Transpiler.opcode_of_ropw, Transpiler.opcode_of_iop,
              Transpiler.opcode_of_sop, Transpiler.opcode_of_sopw, Transpiler.opcode_of_bop] at h_op ⊢))
      all_goals (exfalso; split at h_op <;> simp at h_op)

  end Decoder

  section Arithmetic

    /-- The branch target equation `next_pc = pc + c0 + c1 * 2^16 - sign * 2^32`
        (`branch/constraints.rs:66-86`), read over the integers: with both pcs below
        `0x7800_0000` and a 13-bit offset, the field equation has exactly one solution, the
        64-bit sum. A negative target would need `next_pc >= p - 4096`, above every pc. -/
    lemma branch_target_arith (n0 n1 p0 p1 sx imm s : ℕ)
        (hn : n0 + 65536 * n1 < 2013265920) (hp : p0 + 65536 * p1 < 2013265920)
        (himm : imm < 8192)
        (hs : (s = 0 ∧ sx = imm ∧ imm < 4096) ∨ (s = 1 ∧ sx = imm + (2^64 - 2^13) ∧ 4096 ≤ imm))
        (h : (n0 + 65536 * n1 + s * 33554430) % 2130706433 =
             (p0 + 65536 * p1 + sx % 65536 + sx / 65536 % 65536 * 65536) % 2130706433) :
        n0 + 65536 * n1 = (p0 + 65536 * p1 + sx) % 2^64 := by
      rcases hs with ⟨ rfl, rfl, h3 ⟩ | ⟨ rfl, rfl, h3 ⟩
      · omega
      · have e1 : (imm + (2^64 - 2^13)) % 65536 = imm + 57344 := by omega
        have e2 : (imm + (2^64 - 2^13)) / 65536 % 65536 = 65535 := by omega
        rw [e1, e2] at h
        omega

    /-- `k = x * 2^-16` (`2130673921` is the inverse of `65536` mod p) is 0 or 1 exactly when
        `x` is 0 or `2^16`. -/
    lemma carry_cases (x : FKB) (h : (x * 2130673921) * ((x * 2130673921) - 1) = 0) :
        (x = 0 ∧ x * 2130673921 = 0) ∨ (x = 65536 ∧ x * 2130673921 = 1) := by
      rcases mul_eq_zero.mp h with h | h
      · left
        have hinv : (2130673921 : FKB) ≠ 0 := by decide
        exact ⟨ (mul_eq_zero.mp h).resolve_right hinv, h ⟩
      · right
        have h1 : x * 2130673921 = 1 := sub_eq_zero.mp h
        refine ⟨ ?_, h1 ⟩
        have hk : (2130673921 : FKB) * 65536 = 1 := by decide
        calc x = x * ((2130673921 : FKB) * 65536) := by rw [hk, mul_one]
          _ = (x * 2130673921) * 65536 := by rw [mul_assoc]
          _ = 65536 := by rw [h1, one_mul]

    /-- The JALR addition (`jump/constraints.rs:113-126`, extracted constraints 27 to 30): four
        boolean carries make `b + c = next_pc[0] + lsb + 2^16 next_pc[1]` exact mod `2^64`, given
        16-bit operand limbs and `next_pc[0] + lsb < 2^16`. -/
    lemma jalr_sum (b0 b1 b2 b3 c0 c1 c2 c3 n0 n1 l : FKB)
        (hb : b0.val < 65536 ∧ b1.val < 65536 ∧ b2.val < 65536 ∧ b3.val < 65536)
        (hc : c0.val < 65536 ∧ c1.val < 65536 ∧ c2.val < 65536 ∧ c3.val < 65536)
        (hn : n0.val + 1 < 65536 ∧ n1.val < 65536) (hl : l = 0 ∨ l = 1)
        (h27 : (((((0 + b0) + c0) - n0) - l) * 2130673921) *
               (((((0 + b0) + c0) - n0) - l) * 2130673921 - 1) = 0)
        (h28 : (((((0 + b1) + c1) + (((((0 + b0) + c0) - n0) - l) * 2130673921)) - n1) * 2130673921) *
               ((((((0 + b1) + c1) + (((((0 + b0) + c0) - n0) - l) * 2130673921)) - n1) * 2130673921) - 1) = 0)
        (h29 : ((((0 + b2) + c2) + (((((0 + b1) + c1) + (((((0 + b0) + c0) - n0) - l) * 2130673921)) - n1) * 2130673921)) * 2130673921) *
               (((((0 + b2) + c2) + (((((0 + b1) + c1) + (((((0 + b0) + c0) - n0) - l) * 2130673921)) - n1) * 2130673921)) * 2130673921) - 1) = 0)
        (h30 : ((((0 + b3) + c3) + ((((0 + b2) + c2) + (((((0 + b1) + c1) + (((((0 + b0) + c0) - n0) - l) * 2130673921)) - n1) * 2130673921)) * 2130673921)) * 2130673921) *
               (((((0 + b3) + c3) + ((((0 + b2) + c2) + (((((0 + b1) + c1) + (((((0 + b0) + c0) - n0) - l) * 2130673921)) - n1) * 2130673921)) * 2130673921)) * 2130673921) - 1) = 0) :
        (b0.val + 65536 * b1.val + 4294967296 * b2.val + 281474976710656 * b3.val +
         (c0.val + 65536 * c1.val + 4294967296 * c2.val + 281474976710656 * c3.val)) % 2^64 =
          n0.val + l.val + 65536 * n1.val := by
      obtain ⟨ hb0, hb1, hb2, hb3 ⟩ := hb
      obtain ⟨ hc0, hc1, hc2, hc3 ⟩ := hc
      obtain ⟨ hn0, hn1 ⟩ := hn
      have hlv : l.val ≤ 1 := by rcases hl with rfl | rfl <;> decide
      have v0 : (0 : FKB).val = 0 := rfl
      have v1 : (1 : FKB).val = 1 := rfl
      have v6 : (65536 : FKB).val = 65536 := rfl
      -- Each bracket is an integer in (-2^16, 2^17): a boolean carry pins it to 0 or 2^16.
      rcases carry_cases _ h27 with ⟨ x1, k1 ⟩ | ⟨ x1, k1 ⟩ <;> rw [k1] at h28 h29 h30 <;>
      rcases carry_cases _ h28 with ⟨ x2, k2 ⟩ | ⟨ x2, k2 ⟩ <;> rw [k2] at h29 h30 <;>
      rcases carry_cases _ h29 with ⟨ x3, k3 ⟩ | ⟨ x3, k3 ⟩ <;> rw [k3] at h30 <;>
      rcases carry_cases _ h30 with ⟨ x4, _ ⟩ | ⟨ x4, _ ⟩ <;>
      · simp only [zero_add, sub_sub, sub_eq_iff_eq_add] at x1 x2 x3 x4
        have e1 := congrArg Fin.val x1
        have e2 := congrArg Fin.val x2
        have e3 := congrArg Fin.val x3
        have e4 := congrArg Fin.val x4
        simp only [Fin.val_add, v0, v1, v6] at e1 e2 e3 e4
        clear * - e1 e2 e3 e4 hb0 hb1 hb2 hb3 hc0 hc1 hc2 hc3 hn0 hn1 hlv
        omega

    /-- Clearing bit 0 of `N + l`, with `N` even and `l` a bit, gives `N`. -/
    lemma clear_low_bit (S N l : ℕ) (hS : S = N + l) (hN : N % 2 = 0) (hl : l ≤ 1) (hlt : S < 2^64) :
        (0xFFFFFFFFFFFFFFFE#64) &&& BitVec.ofNat 64 S = BitVec.ofNat 64 N := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : S < 2^64), Nat.mod_eq_of_lt (by omega : N < 2^64),
          Nat.mod_eq_of_lt (by norm_num : (18446744073709551614 : ℕ) < 2^64)]
      rcases i with _ | j
      · simp only [Nat.testBit_zero]; simp; omega
      · rw [show j + 1 = Nat.succ j from rfl, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        have h2 : S / 2 = N / 2 := by omega
        have hm : (18446744073709551614 : ℕ) / 2 = 2^63 - 1 := by norm_num
        rw [h2, hm, Nat.testBit_two_pow_sub_one]
        simp; omega

    /-- Bit 1 of `N + l`, with `N` a multiple of 4 and `l` a bit, is 0. -/
    lemma bit_one_zero (S N l : ℕ) (hS : S = N + l) (hN : N % 4 = 0) (hl : l ≤ 1) (hlt : S < 2^64) :
        (BitVec.ofNat 64 S)[1] = false := by
      simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hlt, show (1 : ℕ) = Nat.succ 0 from rfl, Nat.testBit_succ, Nat.testBit_zero]
      simp; omega

    /-- The return address of a jump row is `pc + 4` (`Pc::add_limb_with_carry`, extracted
        constraints 20 to 23), given the Program table's `pc_carry = [pc[0] >= 0xFFFC]` and a
        4-aligned pc below `0x7800_0000`. -/
    lemma jump_return_address (p0 p1 a0 a1 a2 a3 carry : FKB)
        (hp0 : p0.val < 65536) (hp4 : p0.val % 4 = 0) (hpv : p0.val + 65536 * p1.val < 2013265920)
        (hcarry : carry = if 65532 ≤ p0.val then 1 else 0)
        (c20 : carry * 65536 = p0 + 4 - a0) (c21 : a1 = p1 + carry) (c22 : a2 = 0) (c23 : a3 = 0) :
        U64w.toBV #v[(a0 : BitVec 16), (a1 : BitVec 16), (a2 : BitVec 16), (a3 : BitVec 16)] =
          BitVec.ofNat 64 (p0.val + 65536 * p1.val) + 4#64 := by
      have c20' := eq_sub_iff_add_eq.mp c20
      have v4 : (4 : FKB).val = 4 := rfl
      have v6 : (65536 : FKB).val = 65536 := rfl
      have hcv : carry.val = if 65532 ≤ p0.val then 1 else 0 := by rw [hcarry]; split <;> rfl
      have e1 := congrArg Fin.val c20'
      have e2 := congrArg Fin.val c21
      have e3 : a2.val = 0 := by rw [c22]; rfl
      have e4 : a3.val = 0 := by rw [c23]; rfl
      simp only [Fin.val_add, Fin.val_mul, v4, v6] at e1 e2
      apply BitVec.eq_of_toNat_eq
      simp [U64w.toNat, BitVec.toNat_add, e3, e4]
      clear c20 c20' c21 c22 c23 hcarry
      have := a0.isLt
      have := a1.isLt
      have hp1 : p1.val < 30720 := by omega
      split at hcv
      · rw [hcv] at e1 e2
        have ha0 : a0.val = 0 := by omega
        have ha1 : a1.val = p1.val + 1 := by omega
        rw [ha0, ha1]; omega
      · rw [hcv] at e1 e2
        have ha0 : a0.val = p0.val + 4 := by omega
        have ha1 : a1.val = p1.val := by omega
        rw [ha0, ha1]; omega

  end Arithmetic

  section Stand_in

    /-- Stand-in, on this prototype only, for the ALU contract's opcode 265 (`SLTU` + 256), which a
        separate change adds: the result's first two pieces are `[b <u c]` and `[c <u b]`. -/
    def cmp_unsigned_spec (e : RV64IM_Interactions.ALUBusEntry FKB) : Prop :=
      e.ALU_opcode = 265 →
        e.a_0 = (if (U64w.toBV #v[e.b_0, e.b_1, e.b_2, e.b_3]).ult (U64w.toBV #v[e.c_0, e.c_1, e.c_2, e.c_3]) then 1 else 0) ∧
        e.a_1 = (if (U64w.toBV #v[e.c_0, e.c_1, e.c_2, e.c_3]).ult (U64w.toBV #v[e.b_0, e.b_1, e.b_2, e.b_3]) then 1 else 0)

  end Stand_in

  section Trials

    variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}

    /-- ADD, register form: the row's operations change the Sail state as one step of
        `ADD rd, rs1, rs2` does. -/
    theorem equivalence_ADD [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_row : row ≤ air.last_row)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
        (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
        (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
        (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧ air.cols.opcode_selector.imm_c row 0 = 0)
        (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses) :
        let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
        let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
        let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
        execute_instruction (instruction.RTYPE (rs2, rs1, rd, rop.ADD)) state =
          (operation_list_effect (CPU_bus_operations air row) state).state := by
      have h_wf := h_all_wf row h_row
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, h_props ⟩ := program_wf air row h_is_real h_wf
      simp [program_bus_entry, ProgramBusEntry.deserialise] at h_eq
      obtain ⟨ _, e_pc0, e_pc1, e_op, _, e_a, e_b0, e_b1, e_bs, e_c0, e_c1, e_cs, e_ax0,
               e_ib, e_ic, e_ecall, e_mem, e_st, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu,
               e_jalr, e_jal, e_carry ⟩ := h_eq
      obtain ⟨ rs2, rs1, rd, rfl ⟩ := add_inversion h_tr (by rw [← e_op, h_opcode.1]) (by rw [← e_ic, h_opcode.2])
      simp [Transpiler.V3.transpile_op] at h_tr
      obtain ⟨ rfl, _ ⟩ := h_tr
      simp at e_pc0 e_pc1 e_a e_b0 e_b1 e_bs e_c0 e_c1 e_cs e_ax0 e_ib e_ecall e_mem e_st e_beq e_bne e_blt e_bge e_bltu e_bgeu e_jalr e_jal e_carry
      clear e_op e_ic
      have h_rd : (air.cols.instruction.op_a_0 row 0).val < 32 := by
        simp [e_a, Transpiler.reg_to_KB]
      have h_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32 := by
        simp [e_b0, Transpiler.reg_to_KB]
      have h_rs2 : (air.cols.instruction.op_c_0 row 0).val < 32 := by
        simp [e_c0, Transpiler.reg_to_KB]
      have hc := row_constraints air row (h_all_constraints row h_row)
      simp only [row_constraint_list, List.forall_cons, List.Forall] at hc
      obtain ⟨ _, _, _, _, _, _, _, _, c8, c9, c10, c11, _, _, _, _, _, c17, _, _,
               _, _, _, _, _, _, _, _, _, _, _, c31, _, _, _, _, _, c37, _ ⟩ := hc
      simp [constraint_31, e_ecall] at c31
      simp [constraint_17, h_is_real, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_ecall, e_mem, e_jal, e_jalr] at c17
      simp [constraint_37, h_is_real, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jal, e_jalr, c31, sub_eq_zero] at c37
      have h_pc := pc_facts air row h_is_real h_wf
      have h_npc := next_pc_facts air row h_row h_is_real h_all_wf h_all_constraints pico_assumptions
      simp only [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row, RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_bus_hypotheses
      simp [h_is_real, e_ib, h_opcode.2, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1, h_rs2, mem_width_of_opcode, h_opcode.1] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_rpc, h_reg1, h_reg2, h_reg0, _ ⟩ := h_bus_hypotheses
      -- next_pc = pc + 4 as numbers: both sides are below the field size.
      have h_next : next_pc_val air row = pc_val air row + 4 := by
        have h := congrArg Fin.val c37
        simp only [Fin.val_add, Fin.val_mul] at h
        simp only [next_pc_val, pc_val] at h_npc h_pc ⊢
        norm_num at h
        omega
      -- The ALU contract: on a row with rd ≠ x0, the ALU dispatch has multiplicity 1.
      have h_alu : air.cols.instruction.op_a_is_x0 row 0 = 0 →
          U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row) + U64w.toBV (op_c_value air row) := by
        intro h_x0
        simp [h_x0, sub_eq_zero] at c17
        simp only [bus_row_wf_asm, bus_row, RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_wf
        simp [h_is_real, c17, h_opcode.1, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu,
              RV64IM_Interactions.ALUBus.Spec, execute_RTYPE_pure] at h_wf
        simp only [op_a_value, op_b_value, op_c_value]
        exact h_wf.2.1.2
      simp only [BitVec.ofNatLT_eq_ofNat] at h_rpc h_reg1 h_reg2 h_reg0
      intro rd' rs1' rs2'
      rw [OpcodeSpec.RV64.execute_ADD_equiv
            (pc_val := BitVec.ofNat 64 (pc_val air row))
            (r1_val := U64w.toBV (op_b_value air row))
            (r2_val := U64w.toBV (op_c_value air row))]
      · simp only [OpcodeSpec.RV64.spec_ADD, CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                   RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row]
        simp [h_is_real, e_ib, h_opcode.2, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1, h_rs2,
              mem_width_of_opcode, h_opcode.1]
        simp only [BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_writeReg_same h_reg1]
        simp only [operation_list_effect_state_readReg]
        rw [operation_list_effect_state_writeReg_same h_reg2]
        simp only [operation_list_effect_state_readReg]
        rw [operation_list_effect_state_swap_writePC_writeReg]
        have h_npc_bv : BitVec.ofNat 64 (next_pc_val air row) = BitVec.ofNat 64 (pc_val air row) + 4#64 := by
          rw [h_next, BitVec.ofNat_add]
        rw [h_npc_bv]
        by_cases h_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0
        · have h_sum := h_alu h_x0
          simp only [op_a_value, op_b_value, op_c_value] at h_sum
          simp only [op_b_value, op_c_value, rd', ← h_sum]
          rfl
        · have h_a0 : (air.cols.instruction.op_a_0 row 0).val = 0 := by
            rw [e_ax0] at h_x0
            simp at h_x0
            simp [e_a, h_x0, Transpiler.reg_to_KB, regidx_to_fin]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin, rd', h_a0]
      · simp only [OpcodeSpec.RV64.spec_ADD_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · simpa [pc_val] using h_rpc
        · simpa [op_b_value, rs1'] using h_reg1
        · simpa [op_c_value, rs2'] using h_reg2


    /-- BEQ: the row's operations change the Sail state as one step of `BEQ rs1, rs2, imm` does.
        `h_cmp` stands in for the ALU contract's opcode 265, which a separate change adds. -/
    theorem equivalence_BEQ [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_row : row ≤ air.last_row)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
        (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
        (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
        (h_cmp : List.Forall (fun e => e.multiplicity = 1 → cmp_unsigned_spec e) (bus_row air row).ALU)
        (h_opcode : air.cols.instruction.opcode row 0 = 18)
        (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
        (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg) :
        let rs1 : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
        let rs2 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
        let imm : BitVec 13 := (U64w.toBV (op_c_value air row)).setWidth 13
        execute_instruction (instruction.BTYPE (imm, rs2, rs1, bop.BEQ)) state =
          (operation_list_effect (CPU_bus_operations air row) state).state := by
      have h_wf := h_all_wf row h_row
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, h_props ⟩ := program_wf air row h_is_real h_wf
      simp [program_bus_entry, ProgramBusEntry.deserialise] at h_eq
      obtain ⟨ _, e_pc0, e_pc1, e_op, _, e_a, e_b0, e_b1, e_bs, e_c0, e_c1, e_cs, e_ax0,
               e_ib, e_ic, e_ecall, e_mem, e_st, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu,
               e_jalr, e_jal, e_carry ⟩ := h_eq
      obtain ⟨ imm', rs2, rs1, rfl ⟩ := beq_inversion h_tr (by rw [← e_op, h_opcode])
      simp [Transpiler.V3.transpile_op] at h_tr
      obtain ⟨ rfl, _ ⟩ := h_tr
      simp at e_a e_b0 e_b1 e_bs e_c0 e_c1 e_cs e_ax0 e_ib e_ic e_ecall e_mem e_st e_beq e_bne e_blt e_bge e_bltu e_bgeu e_jalr e_jal
      clear e_op
      have h_imm := imm_operand_sext imm' (by norm_num) (by norm_num)
      have h_rs1 : (air.cols.instruction.op_a_0 row 0).val < 32 := by simp [e_a, Transpiler.reg_to_KB]
      have h_rs2 : (air.cols.instruction.op_b_0 row 0).val < 32 := by simp [e_b0, Transpiler.reg_to_KB]
      have hc := row_constraints air row (h_all_constraints row h_row)
      simp only [row_constraint_list, List.forall_cons, List.Forall] at hc
      obtain ⟨ _, _, _, _, c4, c5, c6, c7, _, _, _, _, _, c13, c14, c15, c16, _, _, c19,
               _, _, _, _, _, _, _, _, _, _, _, c31, _, _, _, _, _, c37, _ ⟩ := hc
      simp [constraint_4, constraint_5, constraint_6, constraint_7, e_ic, sub_eq_zero] at c4 c5 c6 c7
      simp [constraint_13, constraint_14, constraint_15, constraint_16, e_beq, e_bne, e_blt, e_bge,
            e_bltu, e_bgeu, e_st, sub_eq_zero] at c13 c14 c15 c16
      simp [constraint_31, e_ecall] at c31
      simp only [bus_row, RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_cmp
      simp [h_is_real, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, cmp_unsigned_spec] at h_cmp
      have h_pc := pc_facts air row h_is_real h_wf
      have h_npc := next_pc_facts air row h_row h_is_real h_all_wf h_all_constraints pico_assumptions
      simp only [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                 RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_bus_hypotheses
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rs1, h_rs2,
            mem_width_of_opcode, h_opcode] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_rpc, h_reg2, h_reg1, _ ⟩ := h_bus_hypotheses
      simp only [BitVec.ofNatLT_eq_ofNat] at h_rpc h_reg1 h_reg2
      -- The immediate: two pieces and a sign bit of the 13-bit offset, sign-extended.
      obtain ⟨ h_o0, h_o1, h_os ⟩ := h_imm
      have h_imm_lt : imm'.toNat < 8192 := imm'.isLt
      have h_sx : (BitVec.signExtend 64 imm').toNat = imm'.toNat + if imm'.msb then 2^64 - 2^13 else 0 := by
        simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]
      have h_msb : imm'.msb = decide (2^12 ≤ imm'.toNat) := BitVec.msb_eq_decide imm'
      have h_cv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        apply BitVec.eq_of_toNat_eq
        simp only [U64w.toBV_toNat, U64w.toNat, op_c_value, c4, c5, c6, c7, e_c0, e_c1, e_cs]
        rcases h_os with ⟨ hs, hlt ⟩ | ⟨ hs, hge, hlt ⟩ <;> simp [hs] <;> omega
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 13 = imm' := by
        rw [h_cv]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, h_sx]
        split <;> omega
      -- The two register values compared, and the comparison bits.
      have h_lt_bit : air.cols.a_lt_b row 0 =
          if (U64w.toBV (op_a_value air row)).ult (U64w.toBV (op_b_value air row)) then 1 else 0 := by
        simpa [op_a_value, op_b_value] using h_cmp.2.1
      have h_gt_bit : air.cols.a_gt_b row 0 =
          if (U64w.toBV (op_b_value air row)).ult (U64w.toBV (op_a_value air row)) then 1 else 0 := by
        simpa [op_a_value, op_b_value] using h_cmp.2.2
      clear h_cmp
      simp [constraint_19, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, c4, c5] at c19
      simp [constraint_37, h_is_real, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jal, e_jalr, c31] at c37
      -- The next pc as a number.
      have h_next : next_pc_val air row =
          if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
          then (pc_val air row + (BitVec.signExtend 64 imm').toNat) % 2^64
          else pc_val air row + 4 := by
        split
        · rename_i hAB
          have h_t : (1 : FKB) - air.cols.a_lt_b row 0 - air.cols.a_gt_b row 0 = 1 := by
            simp [h_lt_bit, h_gt_bit, hAB, BitVec.ult]
          simp only [h_t, one_ne_zero, false_or, sub_eq_zero] at c19
          rw [eq_sub_iff_add_eq] at c19
          have h := congrArg Fin.val c19
          simp only [Fin.val_add, Fin.val_mul] at h
          norm_num at h
          simp only [pc_val, next_pc_val] at h_pc h_npc ⊢
          rw [e_c0, e_c1, e_cs, h_o0, h_o1] at h
          apply branch_target_arith _ _ _ _ _ imm'.toNat ((Transpiler.V3.imm_operand imm' true)[2]).val
            (by omega) (by omega) h_imm_lt _ h
          rcases h_os with ⟨ hs, hlt ⟩ | ⟨ hs, hge, hlt ⟩ <;> rw [hs] <;>
            by_cases hm : imm'.msb <;> simp [hm] at h_sx h_msb <;> omega
        · rename_i hAB
          have h_t : (1 : FKB) - air.cols.a_lt_b row 0 - air.cols.a_gt_b row 0 = 0 := by
            have h_ne : (op_a_value air row).toNat ≠ (op_b_value air row).toNat := by
              intro h; apply hAB; apply BitVec.eq_of_toNat_eq; simpa using h
            rw [h_lt_bit, h_gt_bit]
            simp only [BitVec.ult, U64w.toBV_toNat]
            by_cases h1 : (op_a_value air row).toNat < (op_b_value air row).toNat
            · have h2 : ¬ (op_b_value air row).toNat < (op_a_value air row).toNat := by omega
              simp [h1, h2]
            · have h2 : (op_b_value air row).toNat < (op_a_value air row).toNat := by omega
              simp [h1, h2]
          simp only [h_t, sub_zero, one_ne_zero, false_or, sub_eq_zero] at c37
          have h := congrArg Fin.val c37
          simp only [Fin.val_add, Fin.val_mul] at h
          norm_num at h
          simp only [pc_val, next_pc_val] at h_pc h_npc ⊢
          omega
      -- Register `a` is unchanged on a branch row (`register/constraints.rs:117-123`).
      have h_reg1' : read_xreg (regidx_to_fin (regidx.Regidx (BitVec.ofNat 5 ↑(air.cols.instruction.op_a_0 row 0)))) state =
          EStateM.Result.ok (U64w.toBV (op_a_value air row)) state := by
        simpa [op_a_value, c13, c14, c15, c16] using h_reg1
      have h_npv := h_next
      simp only [pc_val, next_pc_val] at h_pc h_npc h_npv
      intro rs1' rs2' immv
      have h_immv : immv = imm' := h_imm_eq
      rw [h_immv]
      rw [OpcodeSpec.RV64.execute_BEQ_equiv
            (pc_val := BitVec.ofNat 64 (pc_val air row))
            (r1_val := U64w.toBV (op_a_value air row))
            (r2_val := U64w.toBV (op_b_value air row))
            (misa := misa)
            (h_misa := by clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto)]
      · simp only [OpcodeSpec.RV64.spec_BEQ, CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                   RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row]
        simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rs1, h_rs2,
              mem_width_of_opcode, h_opcode]
        simp only [BitVec.ofNatLT_eq_ofNat]
        rw [operation_list_effect_state_writeReg_same h_reg2]
        simp only [operation_list_effect_state_readReg]
        rw [operation_list_effect_state_writeReg_same (by simpa [op_a_value] using h_reg1')]
        have h_pc_eq : BitVec.ofNat 64 (pc_val air row) +
            (if U64w.toBV (op_a_value air row) = U64w.toBV (op_b_value air row)
             then BitVec.signExtend 64 imm' else 4#64) =
            BitVec.ofNat 64 (next_pc_val air row) := by
          rw [h_next]
          split
          · apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
            simp only [pc_val] at h_pc ⊢
            omega
          · rw [BitVec.ofNat_add]
        rw [h_pc_eq]
      · simp only [OpcodeSpec.RV64.spec_BEQ_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · simpa [pc_val] using h_rpc
        · simpa [rs1'] using h_reg1'
        · simpa [op_b_value, rs2'] using h_reg2
      · intro hAB
        simp only [hAB, ite_true] at h_npv
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_add]
        simp only [pc_val] at h_pc ⊢
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        have h0 : (0 : BitVec 64).toNat = 0 := rfl
        rw [h4, h0]
        omega

    /-- JALR: the row's operations change the Sail state as one step of `JALR rd, rs1, imm` does. -/
    theorem equivalence_JALR [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ)
        (h_row : row ≤ air.last_row)
        (h_is_real : air.cols.is_real row 0 = 1)
        (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
        (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
        (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
        (h_opcode : air.cols.instruction.opcode row 0 = 25)
        (h_bus_hypotheses : (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
        (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg) :
        let rd  : regidx := .Regidx (air.cols.instruction.op_a_0 row 0).val
        let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
        let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
        execute_instruction (instruction.JALR (imm, rs1, rd)) state =
          (operation_list_effect (CPU_bus_operations air row) state).state := by
      have h_wf := h_all_wf row h_row
      obtain ⟨ instr, pc, data, props, h_al, h_lt, h_tr, h_eq, h_props ⟩ := program_wf air row h_is_real h_wf
      simp [program_bus_entry, ProgramBusEntry.deserialise] at h_eq
      obtain ⟨ _, e_pc0, e_pc1, e_op, _, e_a, e_b0, e_b1, e_bs, e_c0, e_c1, e_cs, e_ax0,
               e_ib, e_ic, e_ecall, e_mem, e_st, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu,
               e_jalr, e_jal, e_carry ⟩ := h_eq
      obtain ⟨ imm', rs1, rd, rfl ⟩ := jalr_inversion h_tr (by rw [← e_op, h_opcode])
      simp [Transpiler.V3.transpile_op] at h_tr
      obtain ⟨ rfl, _ ⟩ := h_tr
      simp at e_a e_b0 e_b1 e_bs e_c0 e_c1 e_cs e_ax0 e_ib e_ic e_ecall e_mem e_st e_beq e_bne e_blt e_bge e_bltu e_bgeu e_jalr e_jal
      clear e_op
      have h_imm := imm_operand_sext imm' (by norm_num) (by norm_num)
      have h_rd : (air.cols.instruction.op_a_0 row 0).val < 32 := by simp [e_a, Transpiler.reg_to_KB]
      have h_rs1 : (air.cols.instruction.op_b_0 row 0).val < 32 := by simp [e_b0, Transpiler.reg_to_KB]
      have hc := row_constraints air row (h_all_constraints row h_row)
      simp only [row_constraint_list, List.forall_cons, List.Forall] at hc
      obtain ⟨ _, _, _, _, c4, c5, c6, c7, c8, c9, c10, c11, _, _, _, _, _, _, _, _,
               c20, c21, c22, c23, _, _, c26, c27, c28, c29, c30, _ ⟩ := hc
      simp [constraint_4, constraint_5, constraint_6, constraint_7, e_ic, sub_eq_zero] at c4 c5 c6 c7
      simp only [constraint_27, constraint_28, constraint_29, constraint_30, e_jalr, one_mul] at c27 c28 c29 c30
      simp [constraint_26] at c26
      have h_pc := pc_facts air row h_is_real h_wf
      have h_npc := next_pc_facts air row h_row h_is_real h_all_wf h_all_constraints pico_assumptions
      -- The value read from rs1 has four 16-bit pieces (the register-access contract).
      have h_b_range :
          (air.cols.op_b_access.access.value_0 row 0).val < 65536 ∧
          (air.cols.op_b_access.access.value_1 row 0).val < 65536 ∧
          (air.cols.op_b_access.access.value_2 row 0).val < 65536 ∧
          (air.cols.op_b_access.access.value_3 row 0).val < 65536 := by
        simp only [bus_row_wf_asm, bus_row, RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_wf
        simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu] at h_wf
        exact h_wf.2.2.2.2.2.2.1
      -- The immediate and its 64-bit value.
      obtain ⟨ h_o0, h_o1, h_os ⟩ := h_imm
      have h_imm_lt : imm'.toNat < 4096 := imm'.isLt
      have h_sx : (BitVec.signExtend 64 imm').toNat = imm'.toNat + if imm'.msb then 2^64 - 2^12 else 0 := by
        simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth]; rw [Nat.mod_eq_of_lt (by omega)]
      have h_msb : imm'.msb = decide (2^11 ≤ imm'.toNat) := BitVec.msb_eq_decide imm'
      have h_cv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        apply BitVec.eq_of_toNat_eq
        simp only [U64w.toBV_toNat, U64w.toNat, op_c_value, c4, c5, c6, c7, e_c0, e_c1, e_cs]
        rcases h_os with ⟨ hs, hlt ⟩ | ⟨ hs, hge, hlt ⟩ <;> simp [hs] <;> omega
      have h_imm_eq : (U64w.toBV (op_c_value air row)).setWidth 12 = imm' := by
        rw [h_cv]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, h_sx]
        split <;> omega
      have h_c_range :
          (air.cols.op_c_access.access.value_0 row 0).val < 65536 ∧
          (air.cols.op_c_access.access.value_1 row 0).val < 65536 ∧
          (air.cols.op_c_access.access.value_2 row 0).val < 65536 ∧
          (air.cols.op_c_access.access.value_3 row 0).val < 65536 := by
        rw [c4, c5, c6, c7, e_c0, e_c1, e_cs, h_o0, h_o1]
        rcases h_os with ⟨ hs, _ ⟩ | ⟨ hs, _ ⟩ <;> rw [hs] <;> refine ⟨ by omega, by omega, by decide, by decide ⟩
      -- The JALR addition: rs1 + imm = next_pc + lsb, exactly, mod 2^64.
      have h_lsb : air.cols.jalr_lsb row 0 = 0 ∨ air.cols.jalr_lsb row 0 = 1 := by
        rcases c26 with h | h
        · left; exact h
        · right; exact sub_eq_zero.mp h
      have h_sum := jalr_sum _ _ _ _ _ _ _ _ _ _ _ h_b_range h_c_range
        ⟨ by omega, h_npc.2.1 ⟩ h_lsb c27 c28 c29 c30
      have h_lsb_v : (air.cols.jalr_lsb row 0).val ≤ 1 := by rcases h_lsb with h | h <;> rw [h] <;> decide
      have h_add : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat =
          next_pc_val air row + (air.cols.jalr_lsb row 0).val := by
        rw [← h_cv, BitVec.toNat_add]
        simp [U64w.toNat, op_b_value, op_c_value, next_pc_val]
        obtain ⟨ hb0, hb1, hb2, hb3 ⟩ := h_b_range
        obtain ⟨ hc0, hc1, hc2, hc3 ⟩ := h_c_range
        clear * - h_sum hb0 hb1 hb2 hb3 hc0 hc1 hc2 hc3
        omega
      have h_nv : next_pc_val air row % 4 = 0 ∧ next_pc_val air row < 2^32 := by
        simp only [next_pc_val]; omega
      have h_x_eq : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          BitVec.ofNat 64 (next_pc_val air row + (air.cols.jalr_lsb row 0).val) := by
        apply BitVec.eq_of_toNat_eq; rw [h_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      -- The masked target is next_pc; bit 1 of the unmasked one is 0.
      have h_target : (0xFFFFFFFFFFFFFFFE#64) &&& (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm') =
          BitVec.ofNat 64 (next_pc_val air row) := by
        rw [h_x_eq]; exact clear_low_bit _ _ _ rfl (by omega) h_lsb_v (by omega)
      have h_bit1 : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm')[1] = false := by
        rw [h_x_eq]; exact bit_one_zero _ _ _ rfl h_nv.1 h_lsb_v (by omega)
      -- The return address pc + 4 (`jump/constraints.rs:29-46`).
      have h_ret : air.cols.instruction.op_a_is_x0 row 0 = 0 →
          U64w.toBV (op_a_value air row) = BitVec.ofNat 64 (pc_val air row) + 4#64 := by
        intro h_x0
        simp [constraint_20, constraint_21, constraint_22, constraint_23, e_jal, e_jalr, h_x0,
              sub_eq_zero] at c20 c21 c22 c23
        obtain ⟨ hp0, hp1, hp4, hpv, hcarry ⟩ := h_pc
        simp only [pc_val] at hpv ⊢
        simp only [op_a_value]
        exact jump_return_address _ _ _ _ _ _ _ hp0 hp4 hpv hcarry c20 c21 c22 c23
      -- The row's register reads and writes.
      simp only [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                 RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row] at h_bus_hypotheses
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1,
            mem_width_of_opcode, h_opcode] at h_bus_hypotheses
      rw [operation_list_effect_hypotheses_writeReg_same (by grind)] at h_bus_hypotheses
      simp at h_bus_hypotheses
      obtain ⟨ h_rpc, h_reg1, h_reg0, _ ⟩ := h_bus_hypotheses
      simp only [BitVec.ofNatLT_eq_ofNat] at h_rpc h_reg1 h_reg0
      intro rd' rs1' immv
      have h_immv : immv = imm' := h_imm_eq
      rw [h_immv]
      have h_m : Sail.readReg Register.misa state = EStateM.Result.ok misa state := by
        clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto
      have h_cp : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state := by
        clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto
      have h_ms : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state := by
        clear *- h_assumptions; simp [RISC_V_assumptions] at h_assumptions; tauto
      have h_su : BitVec.ofBool (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm')[1] = 0#1 := by
        rw [h_bit1]; decide
      have h_hyp : (operation_list_effect (OpcodeSpec.RV64.spec_JALR rs1' rd' imm' (BitVec.ofNat 64 (pc_val air row)) (U64w.toBV (op_b_value air row))) state).hypotheses := by
        rw [OpcodeSpec.RV64.spec_JALR_hypotheses]
        refine ⟨ ?_, ?_ ⟩
        · simpa [pc_val] using h_rpc
        · simpa [op_b_value, rs1'] using h_reg1
      have key := OpcodeSpec.RV64.execute_JALR_equiv h_hyp h_m h_cp h_ms h_su
      rw [key]
      simp only [OpcodeSpec.RV64.spec_JALR, CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, bus_row,
                 RV64IM_Interactions.V3.deserialise_bus_row, raw_bus_row]
      simp [h_is_real, e_ib, e_ic, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, h_rd, h_rs1,
            mem_width_of_opcode, h_opcode]
      simp only [BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_writeReg_same h_reg1]
      simp only [operation_list_effect_state_readReg]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      rw [h_target]
      by_cases h_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0
      · rw [show U64w.toBV
              #v[BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0),
                 BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0),
                 BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_2 row 0),
                 BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_3 row 0)] =
              U64w.toBV (op_a_value air row) from rfl, h_ret h_x0]
        rfl
      · have h_a0 : (air.cols.instruction.op_a_0 row 0).val = 0 := by
          rw [e_ax0] at h_x0
          simp at h_x0
          simp [e_a, h_x0, Transpiler.reg_to_KB, regidx_to_fin]
        simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin, rd', h_a0]

  end Trials

end Equivalence.TrialV3
