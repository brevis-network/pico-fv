import PicoFV.RV32IM.RVSail.Auxiliaries
import PicoFV.RV32IM.RVSail.Operations
import PicoFV.RV32IM.RVSail.Execution

namespace PureSpec.RV32

  open RV32IM

  structure SltuInput where
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32

  structure SltuOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_RTYPE_sltu_pure (input : SltuInput) : SltuOutput := {
    nextPC := input.PC + 4#32
    rd_val := BitVec.setWidth 32 (if input.r1_val.toNat < input.r2_val.toNat then 1#1 else 0#1)
    : SltuOutput
  }

  lemma execute_RTYPE_sltu_pure_equiv
    (sltu_input : SltuInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sltu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (sltu_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok sltu_input.PC state)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLTU)) state =
    let sltu_output := execute_RTYPE_sltu_pure sltu_input
    (do
      Sail.writeReg Register.nextPC sltu_output.nextPC
      write_xreg (regidx_to_fin rd) sltu_output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_RTYPE'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_RTYPE_pure,
      execute_RTYPE_sltu_pure
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32

namespace OpcodeSpec.RV32

  open RV32IM

  def spec_SLTU
    (r1 r2 rd : regidx)
    (pc_val r1_val r2_val : BitVec 32)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (BitVec.setWidth 32 (if r1_val.toNat < r2_val.toNat then 1#1 else 0#1)),
    ]

  lemma spec_SLTU_hypotheses
  :
    (operation_list_effect (spec_SLTU r1 r2 rd pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_SLTU, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_SLTU_equiv
    (h : (operation_list_effect (spec_SLTU r1 r2 rd pc_val r1_val r2_val) state).hypotheses)
  :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLTU)) state =
    (operation_list_effect (spec_SLTU r1 r2 rd pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32.SltuInput := {
      r1_val := r1_val,
      r2_val := r2_val,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_SLTU_hypotheses] at h
    rw [PureSpec.RV32.execute_RTYPE_sltu_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32.execute_RTYPE_sltu_pure,
      writeReg_state_success,
      operation_list_effect,
      operation_effect,
      spec_SLTU,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32
