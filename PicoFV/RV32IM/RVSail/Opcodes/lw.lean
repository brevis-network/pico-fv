import PicoFV.RV32IM.RVSail.Auxiliaries
import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.RVSail.Execution

namespace PureSpec.RV32

  open RV32IM

  structure LwInput where
    r1 : Fin 32
    imm : BitVec 12
    r1_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8

  structure LwOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_LOADW_pure (input : LwInput) : LwOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.data3 ++ input.data2 ++ input.data1 ++ input.data0
    : LwOutput
  }

  def lw_state_assumptions
    (i : LwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    (if i.rd == 0
      then state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat + 1]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat + 2]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat + 3]?.isSome
      else state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat]? = .some i.data0 ∧
           state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat + 1]? = .some i.data1 ∧
           state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat + 2]? = .some i.data2 ∧
           state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat + 3]? = .some i.data3) ∧
    (i.r1_val + BitVec.signExtend 32 i.imm).toNat < Pico_address_space_size_32 ∧
    (4 : ℤ) ∣ (i.r1_val + BitVec.signExtend 32 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADW_pure_equiv
    (input : LwInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lw_state_assumptions input state)
  :
    execute_instruction (instruction.LOAD (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      regidx.Regidx (BitVec.ofNat 5 input.rd.val),
      true,
      4
    )) state =
    let output := execute_LOADW_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      write_xreg input.rd output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#32)
    obtain ⟨ h_pc, h_r1, h_mem, h_range, h_align ⟩ := h_opcode_assumptions
    rw [readReg_succ] at h_pc
    simp at h_mem h_range h_align

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r1)) (h_rd := by rfl)] at h_r1
    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_r1 reg_of_fin_neq_nextPC
    simp at h_r1_val

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp [LeanRV32D.Functions.execute_LOAD, LeanRV32D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV32D.Functions.vmem_read_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_pos
         (by
          repeat rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)];
          omega)]; simp [*]
    rw [if_neg (by omega)]

    simp [write_reg_state, execute_LOADW_pure, *]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
    split_ifs at h_mem with h_mem_if
    . simp [*, LeanRV32D.Functions.wX_bits, LeanRV32D.Functions.wX, write_xreg]
    . simp [*, wX_write_xreg_equiv]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_LW
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 32)
    (data0 data1 data2 data3 : BitVec 8)
  : List Operation :=
    if rd == regidx.Regidx 0#5
    then
      [
        .ReadPC pc_val,
        .ReadReg r1 r1_val,
        .ReadMemAny (r1_val + BitVec.signExtend 32 imm).toNat .Word,
        .WritePC (pc_val + 4#32),
      ]
    else
      [
        .ReadPC pc_val,
        .ReadReg r1 r1_val,
        .ReadMem (r1_val + BitVec.signExtend 32 imm).toNat .Word (data3 ++ data2 ++ data1 ++ data0),
        .WritePC (pc_val + 4#32),
        .WriteReg rd (data3 ++ data2 ++ data1 ++ data0),
      ]

  lemma spec_LW_hypotheses
  :
    (operation_list_effect (spec_LW r1 rd imm pc_val r1_val data0 data1 data2 data3) state).hypotheses
      =
    if rd == regidx.Regidx 0#5
    then
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
       read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat + 1]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat + 2]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat + 3]?.isSome)
    else
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
       read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat]? = .some data0 ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat + 1]? = .some data1 ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat + 2]? = .some data2 ∧
       state.mem[(r1_val + BitVec.signExtend 32 imm).toNat + 3]? = .some data3)
  := by
    split_ifs with h_rd_zero
    . simp [operation_list_effect, spec_LW, List.foldl, operation_effect, h_rd_zero]
      grind
    . simp [operation_list_effect, spec_LW, List.foldl, operation_effect, h_rd_zero]
      simp [Sail.writeReg, PreSail.writeReg, BitVec.extractLsb, and_assoc]
      repeat rw [BitVec.extractLsb'_append_eq_ite]
      simp

  lemma execute_LW_equiv
    (h : (operation_list_effect (spec_LW r1 rd imm pc_val r1_val data0 data1 data2 data3) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 32 imm).toNat < Pico_address_space_size_32)
    (h_align : (4 : ℤ) ∣ (r1_val + BitVec.signExtend 32 imm).toNat)
  :
    execute_instruction (instruction.LOAD (imm, r1, rd, true, 4)) state =
    (operation_list_effect (spec_LW r1 rd imm pc_val r1_val data0 data1 data2 data3) state).state
  := by
    let input : PureSpec.RV32.LwInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      rd := regidx_to_fin rd,
      r1_val := r1_val,
      PC := pc_val,
      data0 := data0,
      data1 := data1,
      data2 := data2,
      data3 := data3
    }

    rw [spec_LW_hypotheses] at h
    simp at h_range h_align

    trans execute_instruction (instruction.LOAD (imm, regidx.Regidx (BitVec.ofNat 5 input.r1.val), regidx.Regidx (BitVec.ofNat 5 input.rd.val), true, 4)) state
    . simp; congr
    . rw [PureSpec.RV32.execute_LOADW_pure_equiv input risc_v_assumptions]
      . split_ifs at h with h_zero <;>
        [ (have h_zero' : (regidx_to_fin rd).val = 0 := by clear *- h_zero; simp_all [regidx_to_fin]);
          (have h_zero' : ¬ (regidx_to_fin rd).val = 0 := by clear *- h_zero; obtain ⟨ rd, _ ⟩ := rd; simp_all [regidx_to_fin, ← BitVec.toNat_inj]) ]
        . simp [ input, PureSpec.RV32.execute_LOADW_pure, writeReg_state_success,
                 operation_list_effect, operation_effect, spec_LW, write_reg_state,
                 write_xreg, h_zero, h_zero' ]
        . simp [ input, PureSpec.RV32.execute_LOADW_pure, writeReg_state_success,
                 operation_list_effect, operation_effect, spec_LW, write_reg_state,
                 write_xreg, h_zero ]
      . simp [PureSpec.RV32.lw_state_assumptions, regidx_to_fin, input, *]
        obtain ⟨ rd, _ ⟩ := rd; simp [← BitVec.toNat_inj] at *
        split_ifs at h with h_if <;> simp_all [regidx_to_fin]

end OpcodeSpec.RV32
