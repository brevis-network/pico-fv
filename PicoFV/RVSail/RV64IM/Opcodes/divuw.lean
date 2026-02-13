import PicoFV.RVSail.RV64IM.Auxiliaries
import PicoFV.RVSail.RV64IM.RV64Operations
import PicoFV.RVSail.RV64IM.Execution

namespace PureSpec.RV64

  open RV64IM

  structure DivuwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure DivuwOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_DIVWREMW_divuw_pure (input : DivuwInput) : DivuwOutput :=
    let r1_32 := BitVec.setWidth 32 input.r1_val
    let r2_32 := BitVec.setWidth 32 input.r2_val
    {
      nextPC := input.PC + 4#64
      rd_val := (execute_DIVW_REMW_pure r1_32 r2_32 .DRU).1
      : DivuwOutput
    }

  lemma execute_DIVWREMW_divuw_pure_equiv
    (divuw_input : DivuwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (divuw_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (divuw_input.r2_val) state)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok divuw_input.PC state)
  :
    execute_instruction (instruction.DIVW (r2, r1, rd, true)) state =
    let divuw_output := execute_DIVWREMW_divuw_pure divuw_input
    (do
      Sail.writeReg Register.nextPC divuw_output.nextPC
      write_xreg (regidx_to_fin rd) divuw_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_DIVW'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_DIVWREMW_divuw_pure, BitVec.extractLsb, BitVec.extractLsb']
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_DIVUW
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 64)
  : List RV64Operation :=
    let r1_32 := BitVec.setWidth 32 r1_val
    let r2_32 := BitVec.setWidth 32 r2_val
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd ((execute_DIVW_REMW_pure r1_32 r2_32 .DRU).1),
    ]

  lemma spec_DIVUW_hypotheses
  :
    (RV64_operation_effect (spec_DIVUW r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [RV64_operation_effect, spec_DIVUW, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_DIVUW_equiv
    (h : (RV64_operation_effect (spec_DIVUW r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.DIVW (r2, r1, rd, true)) state =
    (RV64_operation_effect (spec_DIVUW r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.DivuwInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_DIVUW_hypotheses] at h
    rw [PureSpec.RV64.execute_DIVWREMW_divuw_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_DIVWREMW_divuw_pure,
      writeReg_state_success,
      RV64_operation_effect,
      operation_effect,
      spec_DIVUW,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
