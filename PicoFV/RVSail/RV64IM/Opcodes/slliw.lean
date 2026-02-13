import PicoFV.RVSail.RV64IM.Auxiliaries
import PicoFV.RVSail.RV64IM.RV64Operations
import PicoFV.RVSail.RV64IM.Execution

namespace PureSpec.RV64

  open RV64IM

  structure SlliwInput where
    r1_val : BitVec 64
    imm : BitVec 5
    rd : Fin 32
    PC : BitVec 64

  structure SlliwOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_SHIFTIWOP_slliw_pure (input : SlliwInput) : SlliwOutput :=
    let r1_32 := BitVec.setWidth 32 input.r1_val
    let result32 : BitVec 32 := r1_32 <<< input.imm.toNat
    {
      nextPC := input.PC + 4#64
      rd_val := BitVec.signExtend 64 result32
      : SlliwOutput
    }

  lemma execute_SHIFTIWOP_slliw_pure_equiv
    (slliw_input : SlliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slliw_input.r1_val) state)
    (h_input_imm : slliw_input.imm = imm)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok slliw_input.PC state)
  :
    execute_instruction (instruction.SHIFTIWOP (imm, r1, rd, sopw.SLLIW)) state =
    let slliw_output := execute_SHIFTIWOP_slliw_pure slliw_input
    (do
      Sail.writeReg Register.nextPC slliw_output.nextPC
      write_xreg (regidx_to_fin rd) slliw_output.rd_val
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
    simp [execute_SHIFTIWOP_pure, execute_SHIFTIWOP_slliw_pure, h_input_imm,
          BitVec.extractLsb, BitVec.extractLsb']
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_SLLIW
    (r1 rd : regidx)
    (imm : BitVec 5)
    (pc_val r1_val : BitVec 64)
  : List RV64Operation :=
    let r1_32 := BitVec.setWidth 32 r1_val
    let result32 : BitVec 32 := r1_32 <<< imm.toNat
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (BitVec.signExtend 64 result32),
    ]

  lemma spec_SLLIW_hypotheses
  :
    (RV64_operation_effect (spec_SLLIW r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [RV64_operation_effect, spec_SLLIW, List.foldl, operation_effect]
    split <;> simp

  lemma execute_SLLIW_equiv
    (h : (RV64_operation_effect (spec_SLLIW r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.SHIFTIWOP (imm, r1, rd, sopw.SLLIW)) state =
    (RV64_operation_effect (spec_SLLIW r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV64.SlliwInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_SLLIW_hypotheses] at h
    rw [PureSpec.RV64.execute_SHIFTIWOP_slliw_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_SHIFTIWOP_slliw_pure,
      writeReg_state_success,
      RV64_operation_effect,
      operation_effect,
      spec_SLLIW,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
