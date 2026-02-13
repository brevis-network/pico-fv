import PicoFV.RVSail.RV32D.Auxiliaries
import PicoFV.RVSail.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  open RV32D

  structure SlliInput where
    r1_val : BitVec 32
    imm : BitVec 6
    rd : Fin 32
    PC : BitVec 32

  structure SlliOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_SHIFTIOP_slli_pure (input : SlliInput) : SlliOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.r1_val <<< (input.imm % 32)
    : SlliOutput
  }

  lemma execute_SHIFTIOP_slli_pure_equiv
    (slli_input : SlliInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slli_input.r1_val) state)
    (h_input_imm: slli_input.imm = imm)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok slli_input.PC state)
  :
    execute_instruction (instruction.SHIFTIOP (imm, r1, rd, sop.SLLI)) state =
    let slli_output := execute_SHIFTIOP_slli_pure slli_input
    (do
      Sail.writeReg Register.nextPC slli_output.nextPC
      write_xreg (regidx_to_fin rd) slli_output.rd_val
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
      execute_SHIFTIOP_slli_pure,
      h_input_imm
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  open RV32D

  def spec_SLLI
    (r1 rd : regidx)
    (imm : BitVec 6)
    (pc_val r1_val : BitVec 32)
  : List RV32Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (r1_val <<< (imm % 32)),
    ]

  lemma spec_SLLI_hypotheses
  :
    (RV32_operation_effect (spec_SLLI r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [RV32_operation_effect, spec_SLLI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_SLLI_equiv
    (h : (RV32_operation_effect (spec_SLLI r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.SHIFTIOP (imm, r1, rd, sop.SLLI)) state =
    (RV32_operation_effect (spec_SLLI r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV32IM.SlliInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_SLLI_hypotheses] at h
    rw [PureSpec.RV32IM.execute_SHIFTIOP_slli_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32IM.execute_SHIFTIOP_slli_pure,
      writeReg_state_success,
      RV32_operation_effect,
      operation_effect,
      spec_SLLI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32IM
