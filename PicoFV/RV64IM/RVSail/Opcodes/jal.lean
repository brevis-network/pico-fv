import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure JalInput where
    imm : BitVec 21
    rd : Fin 32
    PC : BitVec 64

  structure JalOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64
    success : Bool
    throws : Bool

  def execute_JAL_pure (input : JalInput) : JalOutput :=
    let bit0_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0]! == 0#1)
    let bit1_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1]! == 0#1)
    {
      nextPC :=
        if !bit0_valid || !bit1_valid
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      rd_val := input.PC + 4
      success := bit0_valid && bit1_valid
      throws := !bit0_valid
    }

  lemma rv64d_execute_jal :
    LeanRV64D.Functions.execute (instruction.JAL (imm, rd)) state =
    LeanRV64D.Functions.execute_JAL imm rd state
  := by
    simp [LeanRV64D.Functions.execute]

  set_option maxHeartbeats 0 in
  lemma execute_JAL_pure_equiv
    (jal_input : JalInput)
    (rd : regidx)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok jal_input.PC state)
    (h_input_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
  :
    execute_instruction (instruction.JAL (jal_input.imm, rd)) state =
    let jal_output := execute_JAL_pure jal_input
    (do
      Sail.writeReg Register.nextPC jal_output.nextPC
      if jal_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.25-59.26")
      else if !jal_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        write_xreg (regidx_to_fin rd) jal_output.rd_val
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_JAL,
      LeanRV64D.Functions.get_next_pc,
      LeanRV64D.Functions.jump_to
    ]
    rw [readReg_of_write_other_reg_state h_input_pc (by simp)]
    simp

    by_cases h_bit0 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[0] = 0#1
    . simp [h_bit0]
      rw [readReg_of_write_other_reg_state h_input_misa (by simp)]
      simp
      by_cases h_bit1 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[1] = 1#1
      . simp [h_bit0, h_bit1, execute_JAL_pure]
      . have h_bit1' : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[1] = 0#1 := by grind
        simp [h_bit0, h_bit1', execute_JAL_pure]
        congr
        rw [wX_write_xreg_equiv]
        simp [regidx_to_fin]
    . simp_all [execute_JAL_pure]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_JAL
    (rd : regidx)
    (imm : BitVec 21)
    (pc_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .WritePC (pc_val + BitVec.signExtend 64 imm),
      .WriteReg rd (pc_val + 4#64),
    ]

  lemma spec_JAL_hypotheses
  :
    (operation_list_effect (spec_JAL rd imm pc_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state)
  := by
    simp [operation_list_effect, spec_JAL, List.foldl, operation_effect]
    split <;> simp

  lemma execute_JAL_equiv
    (h : (operation_list_effect (spec_JAL rd imm pc_val) state).hypotheses)
    (h_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
    (h_success :
      (BitVec.ofBool (pc_val + BitVec.signExtend 64 imm)[0] = 0#1) ∧
      (BitVec.ofBool (pc_val + BitVec.signExtend 64 imm)[1] = 0#1)
    )
  :
    execute_instruction (instruction.JAL (imm, rd)) state =
    (operation_list_effect (spec_JAL rd imm pc_val) state).state
  := by
    let input : PureSpec.RV64.JalInput := {
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_JAL_hypotheses] at h
    have h_pc : Sail.readReg Register.PC state = EStateM.Result.ok pc_val state := by
      cases h_read : (Sail.readReg Register.PC state)
      . simp_all
      . simp_all
    rw [PureSpec.RV64.execute_JAL_pure_equiv input rd h_pc h_misa]

    simp [
      input,
      PureSpec.RV64.execute_JAL_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_JAL,
      h_success
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
