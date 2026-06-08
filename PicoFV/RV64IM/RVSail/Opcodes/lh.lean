import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure LhInput where
    r1 : Fin 32
    imm : BitVec 12
    r1_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64
    data0 : BitVec 8
    data1 : BitVec 8

  structure LhOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_LOADH_pure (input : LhInput) : LhOutput := {
    nextPC := input.PC + 4#64
    rd_val := BitVec.signExtend 64 (input.data1 ++ input.data0)
    : LhOutput
  }

  def lh_state_assumptions
    (i : LhInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    (if i.rd == 0
      then state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat]?.isSome ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1]?.isSome
      else state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
           state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1) ∧
    (i.r1_val + (BitVec.signExtend 64 i.imm)).toNat < Pico_address_space_size_64 ∧
    (2 : ℤ) ∣ (i.r1_val + BitVec.signExtend 64 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADH_pure_equiv
    (input : LhInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lh_state_assumptions input state)
  :
    execute_instruction (instruction.LOAD (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      regidx.Regidx (BitVec.ofNat 5 input.rd.val),
      false,
      2
    )) state =
    let output := execute_LOADH_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      write_xreg input.rd output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    obtain ⟨ h_pc, h_r1, h_mem, h_range, h_align ⟩ := h_opcode_assumptions
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

    simp [write_reg_state, execute_LOADH_pure, *]
    split_ifs at h_mem with h_mem_if
    . simp [*, LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.wX, write_xreg]
    . simp [*, wX_write_xreg_equiv]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_LH
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 64)
    (data0 data1 : BitVec 8)
  : List Operation :=
    if rd == regidx.Regidx 0#5
    then
      [
        .ReadPC pc_val,
        .ReadReg r1 r1_val,
        .ReadMemAny (r1_val + BitVec.signExtend 64 imm).toNat .Half,
        .WritePC (pc_val + 4#64),
      ]
    else
      [
        .ReadPC pc_val,
        .ReadReg r1 r1_val,
        .ReadMem (r1_val + BitVec.signExtend 64 imm).toNat .Half (data1 ++ data0),
        .WritePC (pc_val + 4#64),
        .WriteReg rd (BitVec.signExtend 64 (data1 ++ data0)),
      ]

  lemma spec_LH_hypotheses
  :
    (operation_list_effect (spec_LH r1 rd imm pc_val r1_val data0 data1) state).hypotheses
      =
    if rd == regidx.Regidx 0#5
    then
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
       read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat]?.isSome ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 1]?.isSome)
    else
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
       read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat]? = .some data0 ∧
       state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 1]? = .some data1)
  := by
    split_ifs with h_rd_zero
    . simp [operation_list_effect, spec_LH, List.foldl, operation_effect, h_rd_zero]
      grind
    . simp [operation_list_effect, spec_LH, List.foldl, operation_effect, h_rd_zero]
      simp [Sail.writeReg, PreSail.writeReg, BitVec.extractLsb, and_assoc]
      repeat rw [BitVec.extractLsb'_append_eq_ite]
      simp

  lemma execute_LH_equiv
    (h : (operation_list_effect (spec_LH r1 rd imm pc_val r1_val data0 data1) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 64 imm).toNat < Pico_address_space_size_64)
    (h_align : (2 : ℤ) ∣ (r1_val + BitVec.signExtend 64 imm).toNat)
  :
    execute_instruction (instruction.LOAD (imm, r1, rd, false, 2)) state =
    (operation_list_effect (spec_LH r1 rd imm pc_val r1_val data0 data1) state).state
  := by
    let input : PureSpec.RV64.LhInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      rd := regidx_to_fin rd,
      r1_val := r1_val,
      PC := pc_val,
      data0 := data0,
      data1 := data1
    }

    rw [spec_LH_hypotheses] at h
    simp at h_range h_align

    trans execute_instruction (instruction.LOAD (imm, regidx.Regidx (BitVec.ofNat 5 input.r1.val), regidx.Regidx (BitVec.ofNat 5 input.rd.val), false, 2)) state
    . simp; congr
    . rw [PureSpec.RV64.execute_LOADH_pure_equiv input risc_v_assumptions]
      . split_ifs at h with h_zero <;>
        [ (have h_zero' : (regidx_to_fin rd).val = 0 := by clear *- h_zero; simp_all [regidx_to_fin]);
          (have h_zero' : ¬ (regidx_to_fin rd).val = 0 := by clear *- h_zero; obtain ⟨ rd, _ ⟩ := rd; simp_all [regidx_to_fin, ← BitVec.toNat_inj]) ]
        . simp [ input, PureSpec.RV64.execute_LOADH_pure, writeReg_state_success,
                 operation_list_effect, operation_effect, spec_LH, write_reg_state,
                 write_xreg, h_zero, h_zero' ]
        . simp [ input, PureSpec.RV64.execute_LOADH_pure, writeReg_state_success,
                 operation_list_effect, operation_effect, spec_LH, write_reg_state,
                 write_xreg, h_zero ]
      . simp [PureSpec.RV64.lh_state_assumptions, regidx_to_fin, input, *]
        obtain ⟨ rd, _ ⟩ := rd; simp [← BitVec.toNat_inj] at *
        split_ifs at h with h_if <;> simp_all [regidx_to_fin]

end OpcodeSpec.RV64
