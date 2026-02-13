import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Operations
import PicoFV.RVSail.RV32IM.Execution

namespace PureSpec.RV32

  open RV32IM

  structure SltiInput where
    r1_val : BitVec 32
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 32

  structure SltiOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_ITYPE_slti_pure (input : SltiInput) : SltiOutput := {
    nextPC := input.PC + 4#32
    rd_val := BitVec.setWidth 32 (if input.r1_val.toInt < (BitVec.signExtend 32 input.imm).toInt then 1#1 else 0#1)
    : SltiOutput
  }

  lemma execute_ITYPE_slti_pure_equiv
    (slti_input : SltiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slti_input.r1_val) state)
    (h_input_imm: slti_input.imm = imm)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok slti_input.PC state)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.SLTI)) state =
    let slti_output := execute_ITYPE_slti_pure slti_input
    (do
      Sail.writeReg Register.nextPC slti_output.nextPC
      write_xreg (regidx_to_fin rd) slti_output.rd_val
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
      execute_ITYPE_slti_pure,
      h_input_imm
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_SLTI
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (BitVec.setWidth 32 (if r1_val.toInt < (BitVec.signExtend 32 imm).toInt then 1#1 else 0#1)),
    ]

  lemma spec_SLTI_hypotheses
  :
    (operation_list_effect (spec_SLTI r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [operation_list_effect, spec_SLTI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_SLTI_equiv
    (h : (operation_list_effect (spec_SLTI r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.SLTI)) state =
    (operation_list_effect (spec_SLTI r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV32.SltiInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_SLTI_hypotheses] at h
    rw [PureSpec.RV32.execute_ITYPE_slti_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_ITYPE_slti_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_SLTI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
