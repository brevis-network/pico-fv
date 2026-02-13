import PicoFV.RVSail.RV64IM.Auxiliaries
import PicoFV.RVSail.RV64IM.RV64Operations
import PicoFV.RVSail.RV64IM.Execution

namespace PureSpec.RV64

  open RV64IM

  structure SltInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure SltOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_RTYPE_slt_pure (input : SltInput) : SltOutput := {
    nextPC := input.PC + 4#64
    rd_val := BitVec.setWidth 64 (if input.r1_val.toInt < input.r2_val.toInt then 1#1 else 0#1)
    : SltOutput
  }

  lemma execute_RTYPE_slt_pure_equiv
    (slt_input : SltInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slt_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (slt_input.r2_val) state)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok slt_input.PC state)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLT)) state =
    let slt_output := execute_RTYPE_slt_pure slt_input
    (do
      Sail.writeReg Register.nextPC slt_output.nextPC
      write_xreg (regidx_to_fin rd) slt_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_RTYPE'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_RTYPE_pure, execute_RTYPE_slt_pure]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_SLT
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 64)
  : List RV64Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (BitVec.setWidth 64 (if r1_val.toInt < r2_val.toInt then 1#1 else 0#1)),
    ]

  lemma spec_SLT_hypotheses
  :
    (RV64_operation_effect (spec_SLT r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [RV64_operation_effect, spec_SLT, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_SLT_equiv
    (h : (RV64_operation_effect (spec_SLT r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLT)) state =
    (RV64_operation_effect (spec_SLT r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.SltInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_SLT_hypotheses] at h
    rw [PureSpec.RV64.execute_RTYPE_slt_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_RTYPE_slt_pure,
      writeReg_state_success,
      RV64_operation_effect,
      operation_effect,
      spec_SLT,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
