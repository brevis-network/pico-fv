import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure BeqInput where
    imm : BitVec 13
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure BeqOutput where
    nextPC : BitVec 64
    success : Bool
    throws : Bool

  def execute_BEQ_pure (input : BeqInput) : BeqOutput :=
    let skip := !(input.r1_val == input.r2_val)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BeqOutput
    }

  lemma execute_BEQ_pure_succ_throws
    (input : BeqInput)
  :
    let output := execute_BEQ_pure input
    output.success = true → output.throws = false
  := by
    simp [execute_BEQ_pure]
    grind

  lemma execute_BEQ_pure_equiv
    (beq_input : BeqInput)
    (r1 r2 : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (beq_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (beq_input.r2_val) state)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok beq_input.PC state)
    (h_input_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
  :
    execute_instruction (instruction.BTYPE (beq_input.imm, r2, r1, bop.BEQ)) state =
    let beq_output := execute_BEQ_pure beq_input
    (do
      Sail.writeReg Register.nextPC beq_output.nextPC
      if beq_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.25-59.26")
      else if !beq_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_BTYPE
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_BEQ_pure]

    by_cases h_eq: beq_input.r1_val = beq_input.r2_val <;> simp [h_eq]
    rw [readReg_of_write_other_reg_state h_input_pc (by simp)]
    simp
    rewrite [writeReg_read_diff h_input_misa (by trivial)]
    simp

    by_cases h_throws : (execute_BEQ_pure beq_input).throws <;> simp_all [execute_BEQ_pure]
    by_cases h_success : (execute_BEQ_pure beq_input).success <;> simp_all [execute_BEQ_pure]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_BEQ
    (r1 r2 : regidx)
    (imm : BitVec 13)
    (pc_val r1_val r2_val : BitVec 64)
  : List Operation :=
    let increment := if r1_val == r2_val then BitVec.signExtend 64 imm else 4#64
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + increment),
    ]

  lemma spec_BEQ_hypotheses
  :
    (operation_list_effect (spec_BEQ r1 r2 imm pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_BEQ, List.foldl, operation_effect, and_assoc]

  lemma execute_BEQ_equiv
    (h : (operation_list_effect (spec_BEQ r1 r2 imm pc_val r1_val r2_val) state).hypotheses)
    (h_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
    (h_success :
      (BitVec.ofBool (pc_val + BitVec.signExtend 64 imm)[0] = 0#1) ∧
      (BitVec.ofBool (pc_val + BitVec.signExtend 64 imm)[1] = 0#1)
    )
  :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state =
    (operation_list_effect (spec_BEQ r1 r2 imm pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.BeqInput := {
      imm := imm,
      r1_val := r1_val,
      r2_val := r2_val,
      PC := pc_val
    }

    rw [spec_BEQ_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_r2⟩ := h
    rw [PureSpec.RV64.execute_BEQ_pure_equiv input r1 r2 h_r1 h_r2 h_pc h_misa]

    simp [
      input,
      PureSpec.RV64.execute_BEQ_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_BEQ,
      h_success
    ]
    congr 1; split_ifs <;> rfl

end OpcodeSpec.RV64
