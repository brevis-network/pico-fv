import PicoFV.RVSail.RV32D.Auxiliaries
import PicoFV.RVSail.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  open RV32D

  structure DivuInput where
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32

  structure DivuOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_DIVREM_divu_pure (input : DivuInput) : DivuOutput := {
    nextPC := input.PC + 4#32
    rd_val := (execute_DIV_REM_pure input.r1_val input.r2_val .DRU).1
    : DivuOutput
  }

  lemma execute_DIVREM_divu_pure_equiv
    (divu_input : DivuInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (divu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (divu_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok divu_input.PC state)
  :
    execute_instruction (instruction.DIV (r2, r1, rd, true)) state =
    let divu_output := execute_DIVREM_divu_pure divu_input
    (do
      Sail.writeReg Register.nextPC divu_output.nextPC
      write_xreg (regidx_to_fin rd) divu_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_DIV'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_DIVREM_divu_pure
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  open RV32D

  def spec_DIVU
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 32)
  : List RV32Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd ((execute_DIV_REM_pure r1_val r2_val .DRU).1),
    ]

  lemma spec_DIVU_hypotheses
  :
    (RV32_operation_effect (spec_DIVU r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [RV32_operation_effect, spec_DIVU, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_DIVU_equiv
    (h : (RV32_operation_effect (spec_DIVU r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.DIV (r2, r1, rd, true)) state =
    (RV32_operation_effect (spec_DIVU r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32IM.DivuInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_DIVU_hypotheses] at h
    rw [PureSpec.RV32IM.execute_DIVREM_divu_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32IM.execute_DIVREM_divu_pure,
      writeReg_state_success,
      RV32_operation_effect,
      operation_effect,
      spec_DIVU,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32IM
