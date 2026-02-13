import PicoFV.RVSail.RV32D.Auxiliaries
import PicoFV.RVSail.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  open RV32D

  structure BneInput where
    imm : BitVec 13
    r1_val: BitVec 32
    r2_val: BitVec 32
    PC : BitVec 32

  structure BneOutput where
    nextPC : BitVec 32
    success : Bool
    throws : Bool

  def execute_BNE_pure (input : BneInput) : BneOutput :=
    let skip := !(input.r1_val != input.r2_val)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 32 input.imm)
      success := !fails
      throws := throws
      : BneOutput
    }

  lemma execute_BNE_pure_succ_throws
    (input : BneInput)
  :
    let output := execute_BNE_pure input
    output.success = true → output.throws = false
  := by
    simp [execute_BNE_pure]
    grind

  @[simp]
  lemma sign_extend_equiv :
    @LeanRV32D.Functions.sign_extend width1 width2 =
    @BitVec.signExtend width1 width2
  := rfl

  lemma execute_BNE_pure_equiv
    (bne_input : BneInput)
    (r1 r2 : regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bne_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bne_input.r2_val) state)
    (h_input_pc: Sail.readReg Register.PC state = EStateM.Result.ok bne_input.PC state)
    (h_input_misa: Sail.readReg Register.misa state = EStateM.Result.ok misa state)
  :
    execute_instruction (instruction.BTYPE (bne_input.imm, r2, r1, bop.BNE)) state =
    let bne_output := execute_BNE_pure bne_input
    (do
      Sail.writeReg Register.nextPC bne_output.nextPC
      if bne_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.25-59.26")
      else if !bne_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 32 bne_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      LeanRV32D.Functions.execute_BTYPE
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [execute_BNE_pure]

    by_cases h_eq: bne_input.r1_val = bne_input.r2_val
    · simp [h_eq]
    · have h_ne : bne_input.r1_val != bne_input.r2_val := by
        simp [ne_eq, h_eq]
      simp [h_eq]
      rw [readReg_of_write_other_reg_state h_input_pc (by simp)]
      simp
      rewrite [writeReg_read_diff h_input_misa (by trivial)]
      simp

      by_cases h_throws : (execute_BNE_pure bne_input).throws <;> simp_all [execute_BNE_pure]
      by_cases h_success : (execute_BNE_pure bne_input).success <;> simp_all [execute_BNE_pure]

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  open RV32D

  def spec_BNE
    (r1 r2 : regidx)
    (imm : BitVec 13)
    (pc_val r1_val r2_val : BitVec 32)
  : List RV32Operation :=
    let nextPC := if r1_val == r2_val then pc_val + 4#32 else pc_val + BitVec.signExtend 32 imm
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC nextPC,
    ]

  lemma spec_BNE_hypotheses
  :
    (RV32_operation_effect (spec_BNE r1 r2 imm pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [RV32_operation_effect, spec_BNE, List.foldl, operation_effect, and_assoc]

  lemma execute_BNE_equiv
    (h : (RV32_operation_effect (spec_BNE r1 r2 imm pc_val r1_val r2_val) state).hypotheses)
    (h_misa : Sail.readReg Register.misa state = EStateM.Result.ok misa state)
    (h_success :
      (BitVec.ofBool (pc_val + BitVec.signExtend 32 imm)[0] = 0#1) ∧
      (BitVec.ofBool (pc_val + BitVec.signExtend 32 imm)[1] = 0#1)
    )
  :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state =
    (RV32_operation_effect (spec_BNE r1 r2 imm pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV32IM.BneInput := {
      imm := imm,
      r1_val := r1_val,
      r2_val := r2_val,
      PC := pc_val
    }

    rw [spec_BNE_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_r2⟩ := h
    rw [PureSpec.RV32IM.execute_BNE_pure_equiv input r1 r2 h_r1 h_r2 h_pc h_misa]

    simp [
      input,
      PureSpec.RV32IM.execute_BNE_pure,
      writeReg_state_success,
      RV32_operation_effect,
      operation_effect,
      spec_BNE,
      h_success
    ]

end OpcodeSpec.RV32IM
