import PicoFV.RVSail.RV32D.Auxiliaries
import PicoFV.RVSail.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  open RV32D

  structure AndiInput where
    r1_val : BitVec 32
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 32

  structure AndiOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_ITYPE_andi_pure (input : AndiInput) : AndiOutput := {
    nextPC := input.PC + 4#32
    rd_val := input.r1_val &&& BitVec.signExtend 32 input.imm
    : AndiOutput
  }

  lemma execute_ITYPE_andi_pure_equiv
    (andi_input : AndiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (andi_input.r1_val) state)
    (h_input_imm: andi_input.imm = imm)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok andi_input.PC state)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.ANDI)) state =
    let andi_output := execute_ITYPE_andi_pure andi_input
    (do
      Sail.writeReg Register.nextPC andi_output.nextPC
      write_xreg (regidx_to_fin rd) andi_output.rd_val
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
      execute_ITYPE_andi_pure,
      h_input_imm
    ]
    congr
    rw [wX_write_xreg_equiv]
    simp [regidx_to_fin]

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  open RV32D

  def spec_ANDI
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 32)
  : List RV32Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (r1_val &&& BitVec.signExtend 32 imm),
    ]

  lemma spec_ANDI_hypotheses
  :
    (RV32_operation_effect (spec_ANDI r1 rd imm pc_val r1_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state)
  := by
    simp [RV32_operation_effect, spec_ANDI, List.foldl, operation_effect]
    split <;> simp

  lemma execute_ANDI_equiv
    (h : (RV32_operation_effect (spec_ANDI r1 rd imm pc_val r1_val) state).hypotheses)
  :
    execute_instruction (instruction.ITYPE (imm, r1, rd, iop.ANDI)) state =
    (RV32_operation_effect (spec_ANDI r1 rd imm pc_val r1_val) state).state
  := by
    let input : PureSpec.RV32IM.AndiInput := {
      r1_val := r1_val,
      imm := imm,
      rd := regidx_to_fin rd,
      PC := pc_val
    }

    rw [spec_ANDI_hypotheses] at h
    rw [PureSpec.RV32IM.execute_ITYPE_andi_pure_equiv input] <;> simp [input, h]

    simp [
      PureSpec.RV32IM.execute_ITYPE_andi_pure,
      writeReg_state_success,
      RV32_operation_effect,
      operation_effect,
      spec_ANDI,
    ]
    by_cases h_zero : (regidx_to_fin rd).val = 0
    . simp [write_xreg, h_zero]
    . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32IM
