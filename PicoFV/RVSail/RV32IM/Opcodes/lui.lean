import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Operations
import PicoFV.RVSail.RV32IM.Execution

namespace PureSpec.RV32

  open RV32IM

  structure LuiInput where
    imm : BitVec 20
    rd: Fin 32
    PC : BitVec 32

  structure LuiOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_LUI_pure (input : LuiInput) : LuiOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.imm ++ 0#12
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
      LeanRV32D.Functions.execute,
      LeanRV32D.Functions.execute_UTYPE,
      execute_LUI_pure
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_LUI
    (rd : regidx)
    (imm : BitVec 20)
    (pc_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (imm ++ 0#12),
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
    let input : PureSpec.RV32.LuiInput := {
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_LUI_hypotheses] at h
    rw [PureSpec.RV32.execute_LUI_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_LUI_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_LUI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
