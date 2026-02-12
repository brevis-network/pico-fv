import PicoFV.RV32D.Auxiliaries
import PicoFV.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  structure XorInput where
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32

  structure XorOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_RTYPE_xor_pure (input : XorInput) : XorOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.r1_val ^^^ input.r2_val
    : XorOutput
  }

  lemma execute_RTYPE_xor_pure_equiv
    (xor_input : XorInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (xor_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (xor_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok xor_input.PC state)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.XOR)) state =
    let xor_output := execute_RTYPE_xor_pure xor_input
    (do
      Sail.writeReg Register.nextPC xor_output.nextPC
      write_xreg (regidx_to_fin rd) xor_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_RTYPE'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_RTYPE_pure,
      execute_RTYPE_xor_pure
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  def spec_XOR
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 32)
  : List RV32Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (r1_val ^^^ r2_val),
    ]

  lemma spec_XOR_hypotheses
  :
    (RV32_operation_effect (spec_XOR r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [RV32_operation_effect, spec_XOR, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_XOR_equiv
    (h : (RV32_operation_effect (spec_XOR r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.XOR)) state =
    (RV32_operation_effect (spec_XOR r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32IM.XorInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_XOR_hypotheses] at h
    rw [PureSpec.RV32IM.execute_RTYPE_xor_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32IM.execute_RTYPE_xor_pure,
      writeReg_state_success,
      RV32_operation_effect,
      operation_effect,
      spec_XOR,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32IM
