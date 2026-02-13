import PicoFV.RVSail.RV64IM.Auxiliaries
import PicoFV.RVSail.RV64IM.RV64Operations
import PicoFV.RVSail.RV64IM.Execution

namespace PureSpec.RV64

  open RV64IM

  structure SraiwInput where
    r1_val : BitVec 64
    imm : BitVec 5
    rd : Fin 32
    PC : BitVec 64

  structure SraiwOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_SHIFTIWOP_sraiw_pure (input : SraiwInput) : SraiwOutput :=
    let r1_32 := BitVec.setWidth 32 input.r1_val
    let result32 : BitVec 32 := r1_32.sshiftRight input.imm.toNat
    {
      nextPC := input.PC + 4#64
      rd_val := BitVec.signExtend 64 result32
      : SraiwOutput
    }

  lemma execute_SHIFTIWOP_sraiw_pure_equiv
    (sraiw_input : SraiwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sraiw_input.r1_val) state)
    (h_input_imm : sraiw_input.imm = imm)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok sraiw_input.PC state)
  :
    execute_instruction (instruction.SHIFTIWOP (imm, r1, rd, sopw.SRAIW)) state =
    let sraiw_output := execute_SHIFTIWOP_sraiw_pure sraiw_input
    (do
      Sail.writeReg Register.nextPC sraiw_output.nextPC
      write_xreg (regidx_to_fin rd) sraiw_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_SHIFTIWOP'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_SHIFTIWOP_pure, execute_SHIFTIWOP_sraiw_pure, h_input_imm,
          BitVec.extractLsb, BitVec.extractLsb']
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_SRAIW
    (r1 rd : regidx)
    (imm : BitVec 5)
    (pc_val r1_val : BitVec 64)
  : List RV64Operation :=
    let r1_32 := BitVec.setWidth 32 r1_val
    let result32 : BitVec 32 := r1_32.sshiftRight imm.toNat
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (BitVec.signExtend 64 result32),
    ]

  lemma spec_SRAIW_hypotheses
  :
    (RV64_operation_effect (spec_SRAIW r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [RV64_operation_effect, spec_SRAIW, List.foldl, operation_effect]
    split <;> simp

  lemma execute_SRAIW_equiv
    (h : (RV64_operation_effect (spec_SRAIW r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.SHIFTIWOP (imm, r1, rd, sopw.SRAIW)) state =
    (RV64_operation_effect (spec_SRAIW r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV64.SraiwInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_SRAIW_hypotheses] at h
    rw [PureSpec.RV64.execute_SHIFTIWOP_sraiw_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_SHIFTIWOP_sraiw_pure,
      writeReg_state_success,
      RV64_operation_effect,
      operation_effect,
      spec_SRAIW,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
