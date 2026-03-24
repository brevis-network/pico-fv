import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure AddiwInput where
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 64

  structure AddiwOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_ADDIW_addiw_pure (input : AddiwInput) : AddiwOutput :=
    let result := input.r1_val + BitVec.signExtend 64 input.imm
    let result32 := BitVec.setWidth 32 result
    {
      nextPC := input.PC + 4#64
      rd_val := BitVec.signExtend 64 result32
      : AddiwOutput
    }

  lemma execute_ADDIW_addiw_pure_equiv
    (addiw_input : AddiwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (addiw_input.r1_val) state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok addiw_input.PC state)
  :
    execute_instruction (instruction.ADDIW (imm, r1, rd)) state =
    let addiw_output := execute_ADDIW_addiw_pure addiw_input
    (do
      Sail.writeReg Register.nextPC addiw_output.nextPC
      write_xreg (regidx_to_fin rd) addiw_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_ADDIW'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_ADDIW_pure, execute_ADDIW_addiw_pure, h_input_imm,
          BitVec.extractLsb, BitVec.extractLsb', BitVec.setWidth]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_ADDIW
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 64)
  : List Operation :=
    let result := r1_val + BitVec.signExtend 64 imm
    let result32 := BitVec.setWidth 32 result
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (BitVec.signExtend 64 result32),
    ]

  lemma spec_ADDIW_hypotheses
  :
    (operation_list_effect (spec_ADDIW r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [operation_list_effect, spec_ADDIW, List.foldl, operation_effect]
    split <;> simp

  lemma execute_ADDIW_equiv
    (h : (operation_list_effect (spec_ADDIW r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.ADDIW (imm, r1, rd)) state =
    (operation_list_effect (spec_ADDIW r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV64.AddiwInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_ADDIW_hypotheses] at h
    rw [PureSpec.RV64.execute_ADDIW_addiw_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_ADDIW_addiw_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_ADDIW,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
