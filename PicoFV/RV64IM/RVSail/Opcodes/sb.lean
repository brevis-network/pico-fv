import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure SbInput where
    r1 : Fin 32
    imm : BitVec 12
    r2 : Fin 32
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure SbOutput where
    nextPC : BitVec 64
    data0 : ℕ × BitVec 8

  def execute_STOREB_pure (input : SbInput) : SbOutput := {
    nextPC := input.PC + 4#64
    data0 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    : SbOutput
  }

  def modify_memory_1
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_output: SbOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      s.mem.insert sb_output.data0.1 sb_output.data0.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sb_state_assumptions
    (i : SbInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    read_xreg i.r2 state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + (BitVec.signExtend 64 i.imm)).toNat < Pico_address_space_size_64

  set_option maxHeartbeats 0 in
  lemma execute_STOREB_pure_equiv
    (input : SbInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sb_state_assumptions input state)
  :
    execute_instruction (instruction.STORE (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r2.val),
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      1
    )) state =
    let output := execute_STOREB_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_1 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    obtain ⟨ h_pc, h_r1, h_r2, h_range ⟩ := h_opcode_assumptions
    rw [readReg_succ] at h_pc
    simp at h_range

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

    rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r2)) (h_rd := by rfl)] at h_r2
    have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_r2 reg_of_fin_neq_nextPC
    simp at h_r2_val

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp [LeanRV64D.Functions.execute_STORE, LeanRV64D.Functions.vmem_write, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_write_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg (by omega)]; simp [*]

    simp [execute_STOREB_pure, EStateM.set, modify_memory_1,
          BitVec.extractLsb, BitVec.extractLsb', *]
    congr 1
    simp [← BitVec.toNat_inj]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_SB
    (r1 r2 : regidx)
    (imm : BitVec 12)
    (pc_val r1_val r2_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#64),
      .WriteMem (r1_val + (BitVec.signExtend 64 imm)).toNat .Byte (BitVec.extractLsb 7 0 r2_val),
    ]

  lemma spec_SB_hypotheses
  :
    (operation_list_effect (spec_SB r1 r2 imm pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_SB, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_SB_equiv
    (h : (operation_list_effect (spec_SB r1 r2 imm pc_val r1_val r2_val) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 64 imm).toNat < Pico_address_space_size_64)
  :
    execute_instruction (instruction.STORE (imm, r2, r1, 1)) state =
    (operation_list_effect (spec_SB r1 r2 imm pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.SbInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      r2 := regidx_to_fin r2,
      r1_val := r1_val,
      r2_val := r2_val,
      PC := pc_val
    }

    rw [spec_SB_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_r2⟩ := h
    simp at h_range

    have h_opcode_assumptions : PureSpec.RV64.sb_state_assumptions input state := by
      simp [PureSpec.RV64.sb_state_assumptions, input, *]

    trans execute_instruction (instruction.STORE (imm, regidx.Regidx (BitVec.ofNat 5 input.r2.val), regidx.Regidx (BitVec.ofNat 5 input.r1.val), 1)) state
    . simp; congr
    . rw [PureSpec.RV64.execute_STOREB_pure_equiv input risc_v_assumptions h_opcode_assumptions]
      simp [
        input,
        PureSpec.RV64.execute_STOREB_pure,
        writeReg_state_success,
        operation_list_effect,
        operation_effect,
        spec_SB,
        PureSpec.RV64.modify_memory_1,
        EStateM.set,
      ]

end OpcodeSpec.RV64
