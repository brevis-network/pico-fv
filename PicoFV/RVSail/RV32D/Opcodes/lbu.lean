import PicoFV.RVSail.RV32D.Auxiliaries
import PicoFV.RVSail.RV32D.RV32Operations
import PicoFV.Fundamentals.Execution

namespace PureSpec.RV32IM

  open RV32D

  structure LbuInput where
    r1 : Fin 32
    imm : BitVec 12
    r1_val : BitVec 32
    rd : Fin 32
    PC : BitVec 32
    data0 : BitVec 8

  structure LbuOutput where
    nextPC : BitVec 32
    rd_val : BitVec 32

  def execute_LOADBU_pure (input : LbuInput) : LbuOutput := {
    nextPC := input.PC + 4#32
    rd_val := BitVec.setWidth 32 input.data0
    : LbuOutput
  }

  def lbu_state_assumptions
    (i : LbuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    state.mem[(i.r1_val + BitVec.signExtend 32 i.imm).toNat]? = .some i.data0 ∧
    (i.r1_val + BitVec.signExtend 32 i.imm).toNat < Pico_address_space_size_32

  set_option maxHeartbeats 0 in
  lemma execute_LOADBU_pure_equiv
    (input : LbuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lbu_state_assumptions input state)
  :
    execute_instruction (instruction.LOAD (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      regidx.Regidx (BitVec.ofNat 5 input.rd.val),
      true,
      1
    )) state =
    let output := execute_LOADBU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      write_xreg input.rd output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#32)
    obtain ⟨ h_pc, h_r1, h_mem, h_range ⟩ := h_opcode_assumptions
    rw [readReg_succ] at h_pc
    simp at h_mem h_range

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r1)) (h_rd := by rfl)] at h_r1
    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_r1 reg_of_fin_neq_nextPC
    simp at h_r1_val

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp [LeanRV32D.Functions.execute_LOAD, LeanRV32D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV32D.Functions.vmem_read_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg (by omega)]

    simp [write_reg_state, execute_LOADBU_pure, *]
    rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]
    simp [*]
    congr
    rw [wX_write_xreg_equiv]
    simp

end PureSpec.RV32IM

namespace OpcodeSpec.RV32IM

  open RV32D

  def spec_LBU
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 32)
    (data0 : BitVec 8)
  : List RV32Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadMem (r1_val + BitVec.signExtend 32 imm).toNat .Byte data0,
      .WritePC (pc_val + 4#32),
      .WriteReg rd (BitVec.setWidth 32 data0),
    ]

  lemma spec_LBU_hypotheses
  :
    (RV32_operation_effect (spec_LBU r1 rd imm pc_val r1_val data0) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     state.mem[(r1_val + BitVec.signExtend 32 imm).toNat]? = .some data0)
  := by
    simp [RV32_operation_effect, spec_LBU, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_LBU_equiv
    (h : (RV32_operation_effect (spec_LBU r1 rd imm pc_val r1_val data0) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 32 imm).toNat < Pico_address_space_size_32)
  :
    execute_instruction (instruction.LOAD (imm, r1, rd, true, 1)) state =
    (RV32_operation_effect (spec_LBU r1 rd imm pc_val r1_val data0) state).state
  := by
    let input : PureSpec.RV32IM.LbuInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      rd := regidx_to_fin rd,
      r1_val := r1_val,
      PC := pc_val,
      data0 := data0
    }

    rw [spec_LBU_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_mem⟩ := h
    simp at h_mem h_range

    have h_opcode_assumptions : PureSpec.RV32IM.lbu_state_assumptions input state := by
      simp [PureSpec.RV32IM.lbu_state_assumptions, input, *]

    trans execute_instruction (instruction.LOAD (imm, regidx.Regidx (BitVec.ofNat 5 input.r1.val), regidx.Regidx (BitVec.ofNat 5 input.rd.val), true, 1)) state
    . simp; congr
    . rw [PureSpec.RV32IM.execute_LOADBU_pure_equiv input risc_v_assumptions h_opcode_assumptions]
      simp [
        input,
        PureSpec.RV32IM.execute_LOADBU_pure,
        writeReg_state_success,
        RV32_operation_effect,
      operation_effect,
        spec_LBU,
        write_reg_state
      ]
      by_cases h_zero : (regidx_to_fin rd).val = 0
      . simp [write_xreg, h_zero]
      . simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV32IM
