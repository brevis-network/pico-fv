import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure MulhsuInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure MulhsuOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_MULH_mulhsu_pure (input : MulhsuInput) : MulhsuOutput := {
    nextPC := input.PC + 4#64
    rd_val := (execute_MUL_pure input.r1_val input.r2_val .MULHSU)
    : MulhsuOutput
  }

  lemma execute_MULH_mulhsu_pure_equiv
    (mulhsu_input : MulhsuInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mulhsu_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mulhsu_input.r2_val) state)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok mulhsu_input.PC state)
  :
    execute_instruction (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Unsigned })) state =
    let mulhsu_output := execute_MULH_mulhsu_pure mulhsu_input
    (do
      Sail.writeReg Register.nextPC mulhsu_output.nextPC
      write_xreg (regidx_to_fin rd) mulhsu_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_MUL'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_MUL_pure, execute_MULH_mulhsu_pure, mop_of_mul_op]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_MULHSU
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (execute_MUL_pure r1_val r2_val .MULHSU),
    ]

  lemma spec_MULHSU_hypotheses
  :
    (operation_list_effect (spec_MULHSU r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_MULHSU, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_MULHSU_equiv
    (h : (operation_list_effect (spec_MULHSU r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := Signedness.Signed, signed_rs2 := Signedness.Unsigned })) state =
    (operation_list_effect (spec_MULHSU r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.MulhsuInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_MULHSU_hypotheses] at h
    rw [PureSpec.RV64.execute_MULH_mulhsu_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_MULH_mulhsu_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_MULHSU,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
