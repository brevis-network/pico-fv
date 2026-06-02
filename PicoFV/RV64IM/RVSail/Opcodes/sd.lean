import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

namespace PureSpec.RV64

  open RV64IM

  structure SdInput where
    r1 : Fin 32
    imm : BitVec 12
    r2 : Fin 32
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure SdOutput where
    nextPC : BitVec 64
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8
    data2 : ℕ × BitVec 8
    data3 : ℕ × BitVec 8
    data4 : ℕ × BitVec 8
    data5 : ℕ × BitVec 8
    data6 : ℕ × BitVec 8
    data7 : ℕ × BitVec 8

  def execute_STORED_pure (input : SdInput) : SdOutput := {
    nextPC := input.PC + 4#64
    data0 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    data1 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 1,
      BitVec.extractLsb 15 8 input.r2_val
    )
    data2 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 2,
      BitVec.extractLsb 23 16 input.r2_val
    )
    data3 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 3,
      BitVec.extractLsb 31 24 input.r2_val
    )
    data4 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 4,
      BitVec.extractLsb 39 32 input.r2_val
    )
    data5 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 5,
      BitVec.extractLsb 47 40 input.r2_val
    )
    data6 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 6,
      BitVec.extractLsb 55 48 input.r2_val
    )
    data7 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 7,
      BitVec.extractLsb 63 56 input.r2_val
    )
    : SdOutput
  }

  def modify_memory_8
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (output: SdOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((((((((s.mem.insert output.data0.1 output.data0.2
      ).insert output.data1.1 output.data1.2)
      ).insert output.data2.1 output.data2.2
      ).insert output.data3.1 output.data3.2
      ).insert output.data4.1 output.data4.2
      ).insert output.data5.1 output.data5.2
      ).insert output.data6.1 output.data6.2
      ).insert output.data7.1 output.data7.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sd_state_assumptions
    (i : SdInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    Sail.readReg Register.PC state = EStateM.Result.ok i.PC state ∧
    read_xreg i.r1 state = EStateM.Result.ok i.r1_val state ∧
    read_xreg i.r2 state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat < Pico_address_space_size_64 ∧
    (8 : ℤ) ∣ (i.r1_val + (BitVec.signExtend 64 i.imm)).toNat

  set_option maxHeartbeats 0 in
  lemma execute_STORED_pure_equiv
    (input : SdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sd_state_assumptions input state)
  :
    execute_instruction (instruction.STORE (
      input.imm,
      regidx.Regidx (BitVec.ofNat 5 input.r2.val),
      regidx.Regidx (BitVec.ofNat 5 input.r1.val),
      8
    )) state =
    let output := execute_STORED_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_8 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    obtain ⟨ h_pc, h_r1, h_r2, h_range, h_align ⟩ := h_opcode_assumptions
    rw [readReg_succ] at h_pc
    simp at h_range h_align

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
    rw [if_pos (by omega)];
    dsimp; simp only [*]; rw [if_neg (by grind)]
    dsimp; simp only [LeanRV64D.Functions.translationMode]
    rw [if_pos (by rfl)];
    dsimp; simp only [*]; dsimp; simp only [*]; dsimp
    rw [if_pos (by simp [*]; omega)]
    dsimp; simp only [*]
    rw [if_pos (by simp)]
    dsimp; simp only [*]; dsimp
    rw [if_neg (by simp; omega)]; simp [*]
    simp [execute_STORED_pure, EStateM.set, modify_memory_8,
          BitVec.extractLsb, BitVec.extractLsb', *]

end PureSpec.RV64

namespace OpcodeSpec.RV64

  open RV64IM

  def spec_SD
    (r1 r2 : regidx)
    (imm : BitVec 12)
    (pc_val r1_val r2_val : BitVec 64)
  : List Operation :=
    [
      .ReadPC pc_val,
      .ReadReg r1 r1_val,
      .ReadReg r2 r2_val,
      .WritePC (pc_val + 4#64),
      .WriteMem (r1_val + (BitVec.signExtend 64 imm)).toNat .Double r2_val,
    ]

  lemma spec_SD_hypotheses
  :
    (operation_list_effect (spec_SD r1 r2 imm pc_val r1_val r2_val) state).hypotheses
      =
    (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧
     read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1_val state ∧
     read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2_val state)
  := by
    simp [operation_list_effect, spec_SD, List.foldl, operation_effect]
    split <;> simp [and_assoc]

  lemma execute_SD_equiv
    (h : (operation_list_effect (spec_SD r1 r2 imm pc_val r1_val r2_val) state).hypotheses)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_range : (r1_val + BitVec.signExtend 64 imm).toNat < Pico_address_space_size_64)
    (h_align : (8 : ℤ) ∣ (r1_val + BitVec.signExtend 64 imm).toNat)
  :
    execute_instruction (instruction.STORE (imm, r2, r1, 8)) state =
    (operation_list_effect (spec_SD r1 r2 imm pc_val r1_val r2_val) state).state
  := by
    let input : PureSpec.RV64.SdInput := {
      r1 := regidx_to_fin r1,
      imm := imm,
      r2 := regidx_to_fin r2,
      r1_val := r1_val,
      r2_val := r2_val,
      PC := pc_val
    }

    rw [spec_SD_hypotheses] at h
    obtain ⟨h_pc, h_r1, h_r2⟩ := h
    simp at h_range h_align

    have h_opcode_assumptions : PureSpec.RV64.sd_state_assumptions input state := by
      simp [PureSpec.RV64.sd_state_assumptions, input, *]

    trans execute_instruction (instruction.STORE (imm, regidx.Regidx (BitVec.ofNat 5 input.r2.val), regidx.Regidx (BitVec.ofNat 5 input.r1.val), 8)) state
    . simp; congr
    . rw [PureSpec.RV64.execute_STORED_pure_equiv input risc_v_assumptions h_opcode_assumptions]
      simp [
        input,
        PureSpec.RV64.execute_STORED_pure,
        writeReg_state_success,
        operation_list_effect,
        operation_effect,
        spec_SD,
        PureSpec.RV64.modify_memory_8,
        EStateM.set,
      ]

end OpcodeSpec.RV64
