import PicoFV.RVSail.RV64IM.Auxiliaries
import PicoFV.RVSail.RV64IM.RV64Operations
import PicoFV.RVSail.RV64IM.Execution

namespace PureSpec.RV64

  open RV64IM

  structure LdInput where
    r1 : Fin 32
    imm : BitVec 12
    r1_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8
    data4 : BitVec 8
    data5 : BitVec 8
    data6 : BitVec 8
    data7 : BitVec 8

  structure LdOutput where
    nextPC : BitVec 64
    rd_val : BitVec 64

  def execute_LOADD_pure (input : LdInput) : LdOutput := {
    nextPC := input.PC + 4#64
    rd_val := input.data7 ++ input.data6 ++ input.data5 ++ input.data4 ++ input.data3 ++ input.data2 ++ input.data1 ++ input.data0
    : LdOutput
  }

  def ld_state_assumptions
    (i : LdInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 3]? = .some i.data3 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 4]? = .some i.data4 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 5]? = .some i.data5 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 6]? = .some i.data6 ∧
    state.mem[(i.r1_val + BitVec.signExtend 64 i.imm).toNat + 7]? = .some i.data7 ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat < Pico_address_space_size_64 ∧
    (8 : ℤ) ∣ (i.r1_val + BitVec.signExtend 64 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADD_pure_equiv
    (input : LdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : ld_state_assumptions input state)
  :
    execute_instruction (instruction.LOAD (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      regidx.Regidx (BitVec.ofNat 5 input.rd.val),
      false,
      8
    )) state =
    let output := execute_LOADD_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      write_xreg input.rd output.rd_val
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    obtain ⟨ h_pc, h_r1, h_mem0, h_mem1, h_mem2, h_mem3, h_mem4, h_mem5, h_mem6, h_mem7, h_range, h_align ⟩ := h_opcode_assumptions
    rw [readReg_succ] at h_pc
    simp at h_mem0 h_mem1 h_mem2 h_mem3 h_mem4 h_mem5 h_mem6 h_mem7 h_range h_align

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

    simp [write_reg_state, execute_LOADD_pure, *]
    simp [*, wX_write_xreg_equiv]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_LD
    (r1 rd : regidx)
    (imm : BitVec 12)
    (pc_val r1_val : BitVec 64)
    (data0 data1 data2 data3 data4 data5 data6 data7 : BitVec 8)
  : List RV64Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadMem (r1_val + BitVec.signExtend 64 imm).toNat .Double (data7 ++ data6 ++ data5 ++ data4 ++ data3 ++ data2 ++ data1 ++ data0),
      .WritePC (pc_val + 4#64),
      .WriteReg rd (data7 ++ data6 ++ data5 ++ data4 ++ data3 ++ data2 ++ data1 ++ data0),
    ]

  set_option maxHeartbeats 0 in
  lemma spec_LD_hypotheses
  :
    (RV64_operation_effect (spec_LD r1 rd imm pc_val r1_val data0 data1 data2 data3 data4 data5 data6 data7) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat]? = .some data0 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 1]? = .some data1 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 2]? = .some data2 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 3]? = .some data3 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 4]? = .some data4 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 5]? = .some data5 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 6]? = .some data6 ∧
     state.mem[(r1_val + BitVec.signExtend 64 imm).toNat + 7]? = .some data7)
  := by
    simp [RV64_operation_effect, spec_LD, List.foldl, operation_effect]
    simp [Sail.writeReg, PreSail.writeReg, BitVec.extractLsb, and_assoc]
    repeat rw [BitVec.extractLsb'_append_eq_ite]
    simp

  lemma execute_LD_equiv
    (h : (RV64_operation_effect (spec_LD r1 rd imm pc_val r1_val data0 data1 data2 data3 data4 data5 data6 data7) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 64 imm).toNat < Pico_address_space_size_64)
    (h_align : (8 : ℤ) ∣ (r1_val + BitVec.signExtend 64 imm).toNat)
  :
    execute_instruction (instruction.LOAD (imm, r1, rd, false, 8)) state =
    (RV64_operation_effect (spec_LD r1 rd imm pc_val r1_val data0 data1 data2 data3 data4 data5 data6 data7) state).state
  := by
    let input : PureSpec.RV64.LdInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      rd := regidx_to_fin rd,
      r1_val := r1_val,
      PC := pc_val,
      data0 := data0, data1 := data1, data2 := data2, data3 := data3,
      data4 := data4, data5 := data5, data6 := data6, data7 := data7
    }

    rw [spec_LD_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_mem0, h_mem1, h_mem2, h_mem3, h_mem4, h_mem5, h_mem6, h_mem7⟩ := h
    simp at h_mem0 h_mem1 h_mem2 h_mem3 h_mem4 h_mem5 h_mem6 h_mem7 h_range h_align

    have h_opcode_assumptions : PureSpec.RV64.ld_state_assumptions input state := by
      simp [PureSpec.RV64.ld_state_assumptions, input, *]

    trans execute_instruction (instruction.LOAD (imm, regidx.Regidx (BitVec.ofNat 5 input.r1.val), regidx.Regidx (BitVec.ofNat 5 input.rd.val), false, 8)) state
    · simp; congr
    · rw [PureSpec.RV64.execute_LOADD_pure_equiv input risc_v_assumptions h_opcode_assumptions]
      simp [
        input,
        PureSpec.RV64.execute_LOADD_pure,
        writeReg_state_success,
        RV64_operation_effect,
        operation_effect,
        spec_LD,
        write_reg_state
      ]
      by_cases h_zero : (regidx_to_fin rd).val = 0
      · simp [write_xreg, h_zero]
      · simp [write_xreg, Sail.writeReg, PreSail.writeReg]

end OpcodeSpec.RV64
