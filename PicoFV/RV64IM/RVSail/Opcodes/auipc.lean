import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure AuipcInput where
    imm : BitVec 20
    rd : Fin 32
    PC : BitVec 64

  structure AuipcOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_AUIPC_pure (input : AuipcInput) : AuipcOutput := {
    nextPC := input.PC + 4#64
    rd_val := input.PC + BitVec.signExtend 64 (input.imm ++ 0#12)
    : AuipcOutput
  }

  lemma execute_AUIPC_pure_equiv
    (auipc_input : AuipcInput)
    (rd : regidx)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok auipc_input.PC state)
  :
    execute_instruction (instruction.UTYPE (auipc_input.imm, rd, .AUIPC)) state =
    let auipc_output := execute_AUIPC_pure auipc_input
    (do
      Sail.writeReg Register.nextPC auipc_output.nextPC
      write_xreg (regidx_to_fin rd) auipc_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_UTYPE,
      LeanRV64D.Functions.get_arch_pc,
      execute_AUIPC_pure,
    ]
    rw [readReg_of_write_other_reg_state h_input_pc (by simp)]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_AUIPC
    (rd : regidx)
    (imm : BitVec 20)
    (pc_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (pc_val + BitVec.signExtend 64 (imm ++ 0#12)),
    ]

  lemma spec_AUIPC_hypotheses
  :
    (operation_list_effect (spec_AUIPC rd imm pc_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state)
  := by
    simp [operation_list_effect, spec_AUIPC, List.foldl, operation_effect]
    split <;> simp

  lemma execute_AUIPC_equiv
    (h : (operation_list_effect (spec_AUIPC rd imm pc_val) state).hypotheses)
  :
    execute_instruction (instruction.UTYPE (imm, rd, .AUIPC)) state =
    (operation_list_effect (spec_AUIPC rd imm pc_val) state).state
  := by
    let input : PureSpec.RV64.AuipcInput := {
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_AUIPC_hypotheses] at h
    rw [PureSpec.RV64.execute_AUIPC_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV64.execute_AUIPC_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_AUIPC,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
