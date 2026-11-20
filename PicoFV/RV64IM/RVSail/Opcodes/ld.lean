import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Misaligned
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure LdInput where
    r1 : Fin 32
    imm : BitVec 12
    r1_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8
    data4 : BitVec 8
    data5 : BitVec 8
    data6 : BitVec 8
    data7 : BitVec 8

  structure LdOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_LOADD_pure (input : LdInput) : LdOutput := {
    nextPC := input.PC + 4#64
    rd_val := input.data7 ++ input.data6 ++ input.data5 ++ input.data4 ++ input.data3 ++ input.data2 ++ input.data1 ++ input.data0
    : LdOutput
  }

  def ld_state_assumptions
    (i : LdInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    (if i.rd == 0
      then state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 2]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 3]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 4]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 5]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 6]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 7]?.isSome
      else state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 2]? = .some i.data2 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 3]? = .some i.data3 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 4]? = .some i.data4 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 5]? = .some i.data5 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 6]? = .some i.data6 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 7]? = .some i.data7) ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat + 8 ≤ Pico_address_space_size_64

  set_option maxHeartbeats 16_000_000 in
  lemma execute_LOADD_pure_equiv
    (input : LdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : ld_state_assumptions input state)
  :
    execute_instruction (instruction.LOAD (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      regidx.Regidx (BitVec.ofNat 5 input.rd.val),
      false,
      8
    )) state =
    let output := execute_LOADD_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      write_xreg input.rd output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    obtain ⟨ h_pc, h_r1, h_mem, h_range ⟩ := h_opcode_assumptions
    by_cases h_aligned : (input.r1_val + BitVec.signExtend 64 input.imm).toNat % 8 = 0
    swap
    · -- The address is not a multiple of the width: Sail splits the access.
      rcases (by omega : (input.r1_val + BitVec.signExtend 64 input.imm).toNat % 2 = 1 ∨ (input.r1_val + BitVec.signExtend 64 input.imm).toNat % 4 = 2 ∨ (input.r1_val + BitVec.signExtend 64 input.imm).toNat % 8 = 4) with h_k | h_k | h_k
      all_goals by_cases h_rd : input.rd = 0 <;>
        simp only [h_rd, beq_self_eq_true, if_true, beq_iff_eq, if_false] at h_mem
      · simp only [Option.isSome_iff_exists] at h_mem
        obtain ⟨⟨v0, h0⟩, ⟨v1, h1⟩, ⟨v2, h2⟩, ⟨v3, h3⟩,
            ⟨v4, h4⟩, ⟨v5, h5⟩, ⟨v6, h6⟩, ⟨v7, h7⟩⟩ := h_mem
        have h_mem :=
          And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
            (And.intro h4 (And.intro h5 (And.intro h6 h7))))))
        misaligned_load_tac split_misaligned_8_0 _ h_k, execute_LOADD_pure, 8, 1, 64,
          [v0, v1, v2, v3, v4, v5, v6, v7],
          (v7 ++ v6 ++ v5 ++ v4 ++ v3 ++ v2 ++ v1 ++ v0)
      · misaligned_load_tac split_misaligned_8_0 _ h_k, execute_LOADD_pure, 8, 1, 64,
          [input.data0, input.data1, input.data2, input.data3,
           input.data4, input.data5, input.data6, input.data7],
          (input.data7 ++ input.data6 ++ input.data5 ++ input.data4 ++
           input.data3 ++ input.data2 ++ input.data1 ++ input.data0)
      · simp only [Option.isSome_iff_exists] at h_mem
        obtain ⟨⟨v0, h0⟩, ⟨v1, h1⟩, ⟨v2, h2⟩, ⟨v3, h3⟩,
            ⟨v4, h4⟩, ⟨v5, h5⟩, ⟨v6, h6⟩, ⟨v7, h7⟩⟩ := h_mem
        have h_mem :=
          And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
            (And.intro h4 (And.intro h5 (And.intro h6 h7))))))
        misaligned_load_tac split_misaligned_8_1 _ h_k, execute_LOADD_pure, 4, 2, 64,
          [v1 ++ v0, v3 ++ v2, v5 ++ v4, v7 ++ v6],
          (v7 ++ v6 ++ v5 ++ v4 ++ v3 ++ v2 ++ v1 ++ v0)
      · misaligned_load_tac split_misaligned_8_1 _ h_k, execute_LOADD_pure, 4, 2, 64,
          [input.data1 ++ input.data0, input.data3 ++ input.data2,
           input.data5 ++ input.data4, input.data7 ++ input.data6],
          (input.data7 ++ input.data6 ++ input.data5 ++ input.data4 ++
           input.data3 ++ input.data2 ++ input.data1 ++ input.data0)
      · simp only [Option.isSome_iff_exists] at h_mem
        obtain ⟨⟨v0, h0⟩, ⟨v1, h1⟩, ⟨v2, h2⟩, ⟨v3, h3⟩,
            ⟨v4, h4⟩, ⟨v5, h5⟩, ⟨v6, h6⟩, ⟨v7, h7⟩⟩ := h_mem
        have h_mem :=
          And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
            (And.intro h4 (And.intro h5 (And.intro h6 h7))))))
        misaligned_load_tac split_misaligned_8_2 _ h_k, execute_LOADD_pure, 2, 4, 64,
          [v3 ++ v2 ++ v1 ++ v0, v7 ++ v6 ++ v5 ++ v4],
          (v7 ++ v6 ++ v5 ++ v4 ++ v3 ++ v2 ++ v1 ++ v0)
      · misaligned_load_tac split_misaligned_8_2 _ h_k, execute_LOADD_pure, 2, 4, 64,
          [input.data3 ++ input.data2 ++ input.data1 ++ input.data0,
           input.data7 ++ input.data6 ++ input.data5 ++ input.data4],
          (input.data7 ++ input.data6 ++ input.data5 ++ input.data4 ++
           input.data3 ++ input.data2 ++ input.data1 ++ input.data0)
    have h_align : (8 : ℤ) ∣ (input.r1_val + BitVec.signExtend 64 input.imm).toNat := by omega
    replace h_range : (input.r1_val + BitVec.signExtend 64 input.imm).toNat < Pico_address_space_size_64 := by omega
    rw [readReg_succ] at h_pc
    simp at h_mem h_range h_align

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      *
    ]

    rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r1)) (h_rd := by rfl)] at h_r1
    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_r1 reg_of_fin_neq_nextPC
    simp at h_r1_val

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp [LeanRV64D.Functions.execute_LOAD, LeanRV64D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_read_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg (by omega)]

    simp [write_reg_state, execute_LOADD_pure, *]
    split_ifs at h_mem with h_mem_if
    . simp [*, LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.wX, write_xreg]
    . simp [*, wX_write_xreg_equiv]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_LD
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 64)
    (data0 data1 data2 data3 data4 data5 data6 data7 : BitVec 8)
  : List Operation :=
    if rd == regidx.Regidx 0#5
    then
      [
        .ReadPC pc_val,
        .ReadReg r1 r1_val,
        .ReadMemAny (r1_val + BitVec.signExtend 64 imm).toNat .Double,
        .WritePC (pc_val + 4#64),
      ]
    else
      [
        .ReadPC pc_val,
        .ReadReg r1 r1_val,
        .ReadMem (r1_val + BitVec.signExtend 64 imm).toNat .Double (data7 ++ data6 ++ data5 ++ data4 ++ data3 ++ data2 ++ data1 ++ data0),
        .WritePC (pc_val + 4#64),
        .WriteReg rd (data7 ++ data6 ++ data5 ++ data4 ++ data3 ++ data2 ++ data1 ++ data0),
      ]

  set_option maxHeartbeats 0 in
  lemma spec_LD_hypotheses
  :
    (operation_list_effect (spec_LD r1 rd imm pc_val r1_val data0 data1 data2 data3 data4 data5 data6 data7) state).hypotheses
      =
    if rd == regidx.Regidx 0#5
    then
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
       read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 1]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 2]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 3]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 4]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 5]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 6]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 7]?.isSome)
    else
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
       read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat]? = .some data0 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 1]? = .some data1 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 2]? = .some data2 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 3]? = .some data3 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 4]? = .some data4 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 5]? = .some data5 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 6]? = .some data6 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 7]? = .some data7)
  := by
    split_ifs with h_rd_zero
    . simp [operation_list_effect, spec_LD, List.foldl, operation_effect, h_rd_zero]
      grind
    . simp [operation_list_effect, spec_LD, List.foldl, operation_effect, h_rd_zero]
      simp [Sail.writeReg, PreSail.writeReg, BitVec.extractLsb, and_assoc]
      repeat rw [BitVec.extractLsb'_append_eq_ite]
      simp

  lemma execute_LD_equiv
    (h : (operation_list_effect (spec_LD r1 rd imm pc_val r1_val data0 data1 data2 data3 data4 data5 data6 data7) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 64 imm).toNat + 8 ≤ Pico_address_space_size_64)
  :
    execute_instruction (instruction.LOAD (imm, r1, rd, false, 8)) state =
    (operation_list_effect (spec_LD r1 rd imm pc_val r1_val data0 data1 data2 data3 data4 data5 data6 data7) state).state
  := by
    let input : PureSpec.RV64.LdInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      rd := regidx_to_fin rd,
      r1_val := r1_val,
      PC := pc_val,
      data0 := data0, data1 := data1, data2 := data2, data3 := data3,
      data4 := data4, data5 := data5, data6 := data6, data7 := data7
    }

    rw [spec_LD_hypotheses] at h
    simp at h_range

    trans execute_instruction (instruction.LOAD (imm, regidx.Regidx (BitVec.ofNat 5 input.r1.val), regidx.Regidx (BitVec.ofNat 5 input.rd.val), false, 8)) state
    . simp; congr
    . rw [PureSpec.RV64.execute_LOADD_pure_equiv input risc_v_assumptions]
      . split_ifs at h with h_zero <;>
        [ (have h_zero' : (regidx_to_fin rd).val = 0 := by clear *- h_zero; simp_all [regidx_to_fin]);
          (have h_zero' : ¬ (regidx_to_fin rd).val = 0 := by clear *- h_zero; obtain ⟨ rd, _ ⟩ := rd; simp_all [regidx_to_fin, ← BitVec.toNat_inj]) ]
        . simp [ input, PureSpec.RV64.execute_LOADD_pure, writeReg_state_success,
                 operation_list_effect, operation_effect, spec_LD, write_reg_state,
                 write_xreg, h_zero, h_zero' ]
        . simp [ input, PureSpec.RV64.execute_LOADD_pure, writeReg_state_success,
                 operation_list_effect, operation_effect, spec_LD, write_reg_state,
                 write_xreg, h_zero ]
      . simp [PureSpec.RV64.ld_state_assumptions, regidx_to_fin, input, *]
        obtain ⟨ rd, _ ⟩ := rd; simp [← BitVec.toNat_inj] at *
        split_ifs at h with h_if <;> simp_all [regidx_to_fin]

end OpcodeSpec.RV64
