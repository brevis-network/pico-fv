import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure LuiInput where
    imm : BitVec 20
    rd : Fin 32
    PC : BitVec 64

  structure LuiOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_LUI_pure (input : LuiInput) : LuiOutput := {
    nextPC := input.PC + 4#64
    rd_val := BitVec.signExtend 64 (input.imm ++ 0#12)
    : LuiOutput
  }

  lemma execute_LUI_pure_equiv
    (lui_input : LuiInput)
    (rd : regidx)
    (h_input_pc : Sail.readReg Register.PC state = EStateM.Result.ok lui_input.PC state)
  :
    execute_instruction (instruction.UTYPE (lui_input.imm, rd, uop.LUI)) state =
    let lui_output := execute_LUI_pure lui_input
    (do
      Sail.writeReg Register.nextPC lui_output.nextPC
      write_xreg (regidx_to_fin rd) lui_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_UTYPE,
      execute_LUI_pure
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_LUI
    (rd : regidx)
    (imm : BitVec 20)
    (pc_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .WritePC (pc_val + 4#64),
      .WriteReg rd (BitVec.signExtend 64 (imm ++ 0#12)),
    ]

  lemma spec_LUI_hypotheses
  :
    (operation_list_effect (spec_LUI rd imm pc_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state)
  := by
    simp [operation_list_effect, spec_LUI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_LUI_equiv
    (h : (operation_list_effect (spec_LUI rd imm pc_val) state).hypotheses)
  :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state =
    (operation_list_effect (spec_LUI rd imm pc_val) state).state
  := by
    let input : PureSpec.RV64.LuiInput := {
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_LUI_hypotheses] at h
    rw [PureSpec.RV64.execute_LUI_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV64.execute_LUI_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_LUI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
