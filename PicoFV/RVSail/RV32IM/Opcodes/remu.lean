import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Operations
import PicoFV.RVSail.RV32IM.Execution

namespace PureSpec.RV32

  open RV32IM

  structure RemuInput where
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32

  structure RemuOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_DIVREM_remu_pure (input : RemuInput) : RemuOutput := {
    nextPC := input.PC + 4#32
    rd_val := (execute_DIV_REM_pure input.r1_val input.r2_val .DRU).2
    : RemuOutput
  }

  lemma execute_DIVREM_remu_pure_equiv
    (remu_input : RemuInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (remu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (remu_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok remu_input.PC state)
  :
    execute_instruction (instruction.REM (r2, r1, rd, true)) state =
    let remu_output := execute_DIVREM_remu_pure remu_input
    (do
      Sail.writeReg Register.nextPC remu_output.nextPC
      write_xreg (regidx_to_fin rd) remu_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_REM'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_DIVREM_remu_pure
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_REMU
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd ((execute_DIV_REM_pure r1_val r2_val .DRU).2),
    ]

  lemma spec_REMU_hypotheses
  :
    (operation_list_effect (spec_REMU r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_REMU, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_REMU_equiv
    (h : (operation_list_effect (spec_REMU r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.REM (r2, r1, rd, true)) state =
    (operation_list_effect (spec_REMU r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32.RemuInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_REMU_hypotheses] at h
    rw [PureSpec.RV32.execute_DIVREM_remu_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_DIVREM_remu_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_REMU,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
