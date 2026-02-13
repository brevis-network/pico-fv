import PicoFV.RVSail.RV64IM.Auxiliaries
import PicoFV.RVSail.RV64IM.RV64Operations
import PicoFV.RVSail.RV64IM.Execution

namespace PureSpec.RV64

  open RV64IM

  structure LhuInput where
    r1 : Fin 32
    imm : BitVec 12
    r1_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64
    data0 : BitVec 8
    data1 : BitVec 8

  structure LhuOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_LOADHU_pure (input : LhuInput) : LhuOutput := {
    nextPC := input.PC + 4#64
    rd_val := BitVec.setWidth 64 (input.data1 ++ input.data0)
    : LhuOutput
  }

  def lhu_state_assumptions
    (i : LhuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat < Pico_address_space_size_64 ∧
    (2 : ℤ) ∣ (i.r1_val + BitVec.signExtend 64 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADHU_pure_equiv
    (input : LhuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lhu_state_assumptions input state)
  :
    execute_instruction (instruction.LOAD (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      regidx.Regidx (BitVec.ofNat 5 input.rd.val),
      true,
      2
    )) state =
    let output := execute_LOADHU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      write_xreg input.rd output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    obtain ⟨ h_pc, h_r1, h_mem0, h_mem1, h_range, h_align ⟩ := h_opcode_assumptions
    rw [readReg_succ] at h_pc
    simp at h_mem0 h_mem1 h_range h_align

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      *
    ]

    rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r1)) (h_rd := by rfl)] at h_r1
    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_r1 reg_of_fin_neq_nextPC
    simp at h_r1_val

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp [LeanRV64D.Functions.execute_LOAD, LeanRV64D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_read_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg (by omega)]

    simp [write_reg_state, execute_LOADHU_pure, *]
    simp [*, wX_write_xreg_equiv]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_LHU
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 64)
    (data0 data1 : BitVec 8)
  : List RV64Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadMem (r1_val + BitVec.signExtend 64 imm).toNat .Half (data1 ++ data0),
      .WritePC (pc_val + 4#64),
      .WriteReg rd (BitVec.setWidth 64 (data1 ++ data0)),
    ]

  lemma spec_LHU_hypotheses
  :
    (RV64_operation_effect (spec_LHU r1 rd imm pc_val r1_val data0 data1) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat]? = .some data0 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 1]? = .some data1)
  := by
    simp [RV64_operation_effect, spec_LHU, List.foldl, operation_effect]
    simp [Sail.writeReg, PreSail.writeReg, BitVec.extractLsb, and_assoc]
    repeat rw [BitVec.extractLsb'_append_eq_ite]
    simp

  lemma execute_LHU_equiv
    (h : (RV64_operation_effect (spec_LHU r1 rd imm pc_val r1_val data0 data1) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 64 imm).toNat < Pico_address_space_size_64)
    (h_align : (2 : ℤ) ∣ (r1_val + BitVec.signExtend 64 imm).toNat)
  :
    execute_instruction (instruction.LOAD (imm, r1, rd, true, 2)) state =
    (RV64_operation_effect (spec_LHU r1 rd imm pc_val r1_val data0 data1) state).state
  := by
    let input : PureSpec.RV64.LhuInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      rd := regidx_to_fin rd,
      r1_val := r1_val,
      PC := pc_val,
      data0 := data0,
      data1 := data1
    }

    rw [spec_LHU_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_mem0, h_mem1⟩ := h
    simp at h_mem0 h_mem1 h_range h_align

    have h_opcode_assumptions : PureSpec.RV64.lhu_state_assumptions input state := by
      simp [PureSpec.RV64.lhu_state_assumptions, input, *]

    trans execute_instruction (instruction.LOAD (imm, regidx.Regidx (BitVec.ofNat 5 input.r1.val), regidx.Regidx (BitVec.ofNat 5 input.rd.val), true, 2)) state
    · simp; congr
    · rw [PureSpec.RV64.execute_LOADHU_pure_equiv input risc_v_assumptions h_opcode_assumptions]
      simp [
        input,
        PureSpec.RV64.execute_LOADHU_pure,
        writeReg_state_success,
        RV64_operation_effect,
        operation_effect,
        spec_LHU,
        write_reg_state
      ]
      by_cases h_zero : (regidx_to_fin rd).val = 0
      · simp [write_xreg, h_zero]
      · simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
