import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Operations
import PicoFV.RVSail.RV32IM.Execution

namespace PureSpec.RV32

  open RV32IM

  structure SraiInput where
    r1_val : BitVec 32
    imm : BitVec 6
    rd : Fin 32
    PC : BitVec 32

  structure SraiOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_SHIFTIOP_srai_pure (input : SraiInput) : SraiOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.r1_val.sshiftRight (input.imm % 32).toNat
    : SraiOutput
  }

  lemma execute_SHIFTIOP_srai_pure_equiv
    (srai_input : SraiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (srai_input.r1_val) state)
    (h_input_imm: srai_input.imm = imm)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok srai_input.PC state)
  :
    execute_instruction (instruction.SHIFTIOP (imm, r1, rd, sop.SRAI)) state =
    let srai_output := execute_SHIFTIOP_srai_pure srai_input
    (do
      Sail.writeReg Register.nextPC srai_output.nextPC
      write_xreg (regidx_to_fin rd) srai_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_SHIFTIOP'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [
      execute_SHIFTIOP_pure,
      execute_RTYPE_pure,
      execute_SHIFTIOP_srai_pure,
      h_input_imm
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_SRAI
    (r1 rd : regidx)
    (imm : BitVec 6)
    (pc_val r1_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (r1_val.sshiftRight (imm % 32).toNat),
    ]

  lemma spec_SRAI_hypotheses
  :
    (operation_list_effect (spec_SRAI r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [operation_list_effect, spec_SRAI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_SRAI_equiv
    (h : (operation_list_effect (spec_SRAI r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.SHIFTIOP (imm, r1, rd, sop.SRAI)) state =
    (operation_list_effect (spec_SRAI r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV32.SraiInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_SRAI_hypotheses] at h
    rw [PureSpec.RV32.execute_SHIFTIOP_srai_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_SHIFTIOP_srai_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_SRAI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
