import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure SraiInput where
    r1_val : BitVec 64
    imm : BitVec 6
    rd : Fin 32
    PC : BitVec 64

  structure SraiOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_SHIFTIOP_srai_pure (input : SraiInput) : SraiOutput := {
    nextPC := input.PC + 4#64
    rd_val := input.r1_val.sshiftRight input.imm.toNat
    : SraiOutput
  }

  lemma execute_SHIFTIOP_srai_pure_equiv
    (srai_input : SraiInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (srai_input.r1_val) state)
    (h_input_imm : srai_input.imm = imm)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok srai_input.PC state)
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
      LeanRV64D.Functions.execute,
      execute_SHIFTIOP'
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    have h_mod : imm.toNat % 64 = imm.toNat := Nat.mod_eq_of_lt (by have := imm.isLt; omega)
    simp [execute_SHIFTIOP_pure, execute_RTYPE_pure, execute_SHIFTIOP_srai_pure, h_input_imm, h_mod]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_SRAI
    (r1 rd : regidx)
    (imm : BitVec 6)
    (pc_val r1_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (r1_val.sshiftRight imm.toNat),
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
    let input : PureSpec.RV64.SraiInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }
    rw [spec_SRAI_hypotheses] at h
    rw [PureSpec.RV64.execute_SHIFTIOP_srai_pure_equiv input] <;> simp [input, h]
    simp [
      PureSpec.RV64.execute_SHIFTIOP_srai_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_SRAI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
