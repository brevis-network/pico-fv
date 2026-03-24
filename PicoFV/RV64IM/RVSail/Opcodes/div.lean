import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure DivInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure DivOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_DIVREM_div_pure (input : DivInput) : DivOutput := {
    nextPC := input.PC + 4#64
    rd_val := (execute_DIV_REM_pure input.r1_val input.r2_val .DRS).1
    : DivOutput
  }

  lemma execute_DIVREM_div_pure_equiv
    (div_input : DivInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (div_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (div_input.r2_val) state)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok div_input.PC state)
  :
    execute_instruction (instruction.DIV (r2, r1, rd, false)) state =
    let div_output := execute_DIVREM_div_pure div_input
    (do
      Sail.writeReg Register.nextPC div_output.nextPC
      write_xreg (regidx_to_fin rd) div_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_DIV'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_DIVREM_div_pure]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_DIV
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd ((execute_DIV_REM_pure r1_val r2_val .DRS).1),
    ]

  lemma spec_DIV_hypotheses
  :
    (operation_list_effect (spec_DIV r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_DIV, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_DIV_equiv
    (h : (operation_list_effect (spec_DIV r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.DIV (r2, r1, rd, false)) state =
    (operation_list_effect (spec_DIV r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.DivInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_DIV_hypotheses] at h
    rw [PureSpec.RV64.execute_DIVREM_div_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_DIVREM_div_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_DIV,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
