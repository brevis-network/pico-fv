import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Operations
import PicoFV.RVSail.RV32IM.Execution

namespace PureSpec.RV32

  open RV32IM

  structure JalrInput where
    imm : BitVec 12
    rs1_val: BitVec 32
    rd: Fin 32
    PC : BitVec 32

  structure JalrOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32
    success : Bool

  def execute_JALR_pure (input : JalrInput) : JalrOutput :=
    let bit1_valid := (BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 input.imm)[1]! == 0#1)
    let mask := 0xFFFFFFFE
    {
      nextPC :=
        if (!bit1_valid)
        then (input.PC + 4)
        else (mask &&& (input.rs1_val + BitVec.signExtend 32 input.imm))
      rd_val := input.PC + 4
      success := (bit1_valid)
    }

  set_option maxHeartbeats 0 in
  lemma execute_JALR_pure_equiv
    (input : JalrInput)
    (rs1 rd: regidx)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok input.PC state)
    (h_input_misa: Sail.readReg Register.misa state = EStateM.Result.ok misa state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    execute_instruction (instruction.JALR (input.imm, rs1, rd)) state =
    let output := execute_JALR_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      if !output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (0xFFFFFFFE &&& (input.rs1_val + BitVec.signExtend 32 input.imm))),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        write_xreg (regidx_to_fin rd) output.rd_val
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      LeanRV32D.Functions.execute_JALR,
      LeanRV32D.Functions.jump_to,
      LeanRV32D.Functions.update_elp_state,
    ]
    rw [readReg_of_write_other_reg_state h_cur_privilege (by simp)]
    simp [
      LeanRV32D.Functions.get_xLPE
    ]
    rw [readReg_of_write_other_reg_state h_mseccfg (by simp)]
    simp

    rewrite [rX_read_xreg_equiv _ rs1 (regidx_to_fin rs1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_rs1 reg_of_fin_neq_nextPC]
    simp [
      Sail.BitVec.update,
      execute_JALR_pure
    ]
    rw [readReg_of_write_other_reg_state h_input_misa (by simp)]
    simp

    by_cases h_bit1 : BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 input.imm)[1] = 1#1
    . simp [h_bit1]
    . have h_bit1' : BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 input.imm)[1] = 0#1 := by grind
      simp [h_bit1']
      congr
      rw [wX_write_xreg_equiv]
      simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_JALR
    (rs1 rd : regidx)
    (imm : BitVec 12)
    (pc_val rs1_val : BitVec 32)
  : List Operation :=
    let mask := 0xFFFFFFFE
    [
      .ReadPC pc_val,
      .ReadReg rs1 rs1_val,
      .WritePC (mask &&& (rs1_val + BitVec.signExtend 32 imm)),
      .WriteReg rd (pc_val + 4#32),
    ]

  lemma spec_JALR_hypotheses
  :
    (operation_list_effect (spec_JALR rs1 rd imm pc_val rs1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok rs1_val state)
  := by
    simp [operation_list_effect, spec_JALR, List.foldl, operation_effect]
    split <;> simp

  lemma execute_JALR_equiv
    (h : (operation_list_effect (spec_JALR rs1 rd imm pc_val rs1_val) state).hypotheses)
    (h_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
    (h_success :
      BitVec.ofBool (rs1_val + BitVec.signExtend 32 imm)[1] = 0#1
    )
  :
    execute_instruction (instruction.JALR (imm, rs1, rd)) state =
    (operation_list_effect (spec_JALR rs1 rd imm pc_val rs1_val) state).state
  := by
    let input : PureSpec.RV32.JalrInput := {
      imm := imm,
      rs1_val := rs1_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_JALR_hypotheses] at h
    obtain ⟨h_pc, h_rs1⟩ := h
    rw [PureSpec.RV32.execute_JALR_pure_equiv input rs1 rd h_rs1 h_pc h_misa h_cur_privilege h_mseccfg]

    simp [
      input,
      PureSpec.RV32.execute_JALR_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_JALR,
      h_success
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
