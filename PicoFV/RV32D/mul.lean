import PicoFV.RV32D.Auxiliaries
import PicoFV.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  structure MulInput where
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32

  structure MulOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_MULH_mul_pure (input : MulInput) : MulOutput := {
    nextPC := input.PC + 4#32
    rd_val := (execute_MUL_pure input.r1_val input.r2_val .MUL)
    : MulOutput
  }

  lemma execute_MULH_mul_pure_equiv
    (mul_input : MulInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mul_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mul_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok mul_input.PC state)
  :
    execute_instruction (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.Low, signed_rs1 := srs1, signed_rs2 := srs2 })) state =
    let mul_output := execute_MULH_mul_pure mul_input
    (do
      Sail.writeReg Register.nextPC mul_output.nextPC
      write_xreg (regidx_to_fin rd) mul_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_MUL'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_MUL_pure,
      execute_MULH_mul_pure,
      mop_of_mul_op
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  def spec_MUL
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 32)
  : List RV32Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (execute_MUL_pure r1_val r2_val .MUL),
    ]

  lemma spec_MUL_hypotheses
  :
    (RV32_operation_effect (spec_MUL r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [RV32_operation_effect, spec_MUL, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_MUL_equiv
    (h : (RV32_operation_effect (spec_MUL r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.Low, signed_rs1 := srs1, signed_rs2 := srs2 })) state =
    (RV32_operation_effect (spec_MUL r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32IM.MulInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_MUL_hypotheses] at h
    rw [PureSpec.RV32IM.execute_MULH_mul_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32IM.execute_MULH_mul_pure,
      writeReg_state_success,
      RV32_operation_effect,
      operation_effect,
      spec_MUL,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32IM
