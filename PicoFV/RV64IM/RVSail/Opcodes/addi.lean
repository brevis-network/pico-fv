import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure AddiInput where
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 64

  structure AddiOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_ITYPE_addi_pure (input : AddiInput) : AddiOutput := {
    nextPC := input.PC + 4#64
    rd_val := input.r1_val + BitVec.signExtend 64 input.imm
    : AddiOutput
  }

  lemma execute_ITYPE_addi_pure_equiv
    (addi_input : AddiInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (addi_input.r1_val) state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok addi_input.PC state)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.ADDI)) state =
    let addi_output := execute_ITYPE_addi_pure addi_input
    (do
      Sail.writeReg Register.nextPC addi_output.nextPC
      write_xreg (regidx_to_fin rd) addi_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_ITYPE'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [execute_ITYPE_pure, execute_RTYPE_pure, execute_ITYPE_addi_pure, h_input_imm]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_ADDI
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (r1_val + BitVec.signExtend 64 imm),
    ]

  lemma spec_ADDI_hypotheses
  :
    (operation_list_effect (spec_ADDI r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [operation_list_effect, spec_ADDI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_ADDI_equiv
    (h : (operation_list_effect (spec_ADDI r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.ADDI)) state =
    (operation_list_effect (spec_ADDI r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV64.AddiInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_ADDI_hypotheses] at h
    rw [PureSpec.RV64.execute_ITYPE_addi_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_ITYPE_addi_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_ADDI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
