import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Operations
import PicoFV.RVSail.RV32IM.Execution

namespace PureSpec.RV32

  open RV32IM

  structure MulhuInput where
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32

  structure MulhuOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_MULH_mulhu_pure (input : MulhuInput) : MulhuOutput := {
    nextPC := input.PC + 4#32
    rd_val := (execute_MUL_pure input.r1_val input.r2_val .MULHU)
    : MulhuOutput
  }

  lemma execute_MULH_mulhu_pure_equiv
    (mulhu_input : MulhuInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mulhu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mulhu_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok mulhu_input.PC state)
  :
    execute_instruction (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) state =
    let mulhu_output := execute_MULH_mulhu_pure mulhu_input
    (do
      Sail.writeReg Register.nextPC mulhu_output.nextPC
      write_xreg (regidx_to_fin rd) mulhu_output.rd_val
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
      execute_MULH_mulhu_pure,
      mop_of_mul_op
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_MULHU
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (execute_MUL_pure r1_val r2_val .MULHU),
    ]

  lemma spec_MULHU_hypotheses
  :
    (operation_list_effect (spec_MULHU r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_MULHU, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_MULHU_equiv
    (h : (operation_list_effect (spec_MULHU r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) state =
    (operation_list_effect (spec_MULHU r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32.MulhuInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_MULHU_hypotheses] at h
    rw [PureSpec.RV32.execute_MULH_mulhu_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_MULH_mulhu_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_MULHU,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
