import PicoFV.RV32IM.RVSail.Auxiliaries
import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.RVSail.Execution

namespace PureSpec.RV32

  open RV32IM

  structure OriInput where
    r1_val : BitVec 32
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 32

  structure OriOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_ITYPE_ori_pure (input : OriInput) : OriOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.r1_val ||| BitVec.signExtend 32 input.imm
    : OriOutput
  }

  lemma execute_ITYPE_ori_pure_equiv
    (ori_input : OriInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (ori_input.r1_val) state)
    (h_input_imm: ori_input.imm = imm)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok ori_input.PC state)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.ORI)) state =
    let ori_output := execute_ITYPE_ori_pure ori_input
    (do
      Sail.writeReg Register.nextPC ori_output.nextPC
      write_xreg (regidx_to_fin rd) ori_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_ITYPE'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [
      execute_ITYPE_pure,
      execute_RTYPE_pure,
      execute_ITYPE_ori_pure,
      h_input_imm
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_ORI
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (r1_val ||| BitVec.signExtend 32 imm),
    ]

  lemma spec_ORI_hypotheses
  :
    (operation_list_effect (spec_ORI r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [operation_list_effect, spec_ORI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_ORI_equiv
    (h : (operation_list_effect (spec_ORI r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.ORI)) state =
    (operation_list_effect (spec_ORI r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV32.OriInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_ORI_hypotheses] at h
    rw [PureSpec.RV32.execute_ITYPE_ori_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_ITYPE_ori_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_ORI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
