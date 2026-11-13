import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Execution

/-! # `FENCE`, `FENCE_TSO` and `PAUSE` execute as the no-op

    Pico transpiles every fence word (`fence`, `fence.tso` and `pause`) to the canonical no-op
    `ADDI x0, x0, 0` (`process_fence`, `vm/src/compiler/riscv/disassembler/rrs.rs:509-517`,
    returning `Instruction::nop`, `rrs.rs:95-100`), so the Program table holds the no-op's row
    for it. The theorems below show that in the Sail model each of the three instructions has
    the same effect as that no-op: the same result and the same state. For `FENCE` this holds in
    machine mode, assumption A1.1 of `RISC_V_assumptions`, because `FENCE` reads the privilege
    level (`is_fiom_active`, `LeanRV64D/SysRegs.lean:1143-1151`).

    Sail sources, in `LeanRV64D/InstsEnd.lean`: `execute_PAUSE` (`:67008-67009`) retires at
    once; `execute_FENCE_TSO` (`:70360-70362`) issues a barrier, which the sequential model
    defines as `pure ()`, and retires; `execute_FENCE` (`:70368-70384`) reads the privilege
    level, issues a barrier or nothing, and retires. `ADDI x0, x0, 0` reads `x0`, which is the
    constant zero, and writes `x0`, which does nothing (`LeanRV64D/Regs.lean:616-620, 654-658`). -/

namespace PureSpec.RV64

  open RV64IM

  /-- The no-op `ADDI x0, x0, 0` that Pico transpiles every fence word to. -/
  abbrev nop_instruction : instruction :=
    .ITYPE (0#12, regidx.Regidx 0#5, regidx.Regidx 0#5, iop.ADDI)

  /-- `ADDI x0, x0, 0` retires without reading or writing any state. -/
  lemma execute_nop_instruction :
      LeanRV64D.Functions.execute nop_instruction = pure (ExecutionResult.Retire_Success ()) := by
    simp [LeanRV64D.Functions.execute, execute_ITYPE', LeanRV64D.Functions.rX_bits,
      LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.rX, LeanRV64D.Functions.wX]
    rfl

  /-- `PAUSE` executes as the no-op, in every state. -/
  lemma execute_pause_eq_nop :
      LeanRV64D.Functions.execute (.PAUSE ()) = LeanRV64D.Functions.execute nop_instruction := by
    rw [execute_nop_instruction]
    simp [LeanRV64D.Functions.execute, LeanRV64D.Functions.execute_PAUSE]

  /-- `FENCE_TSO` executes as the no-op, in every state. -/
  lemma execute_fence_tso_eq_nop :
      LeanRV64D.Functions.execute (.FENCE_TSO ()) =
      LeanRV64D.Functions.execute nop_instruction := by
    rw [execute_nop_instruction]
    simp [LeanRV64D.Functions.execute, LeanRV64D.Functions.execute_FENCE_TSO,
      Sail.ConcurrencyInterfaceV1.sail_barrier]
    rfl

  /-- In machine mode `FENCE` retires and leaves the state unchanged, whatever its fields. -/
  lemma execute_fence_of_machine
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (h_priv : Sail.readReg Register.cur_privilege state =
        EStateM.Result.ok Privilege.Machine state) :
      LeanRV64D.Functions.execute (.FENCE (fm, pred, succ, rs, rd)) state =
      EStateM.Result.ok (ExecutionResult.Retire_Success ()) state := by
    simp [LeanRV64D.Functions.execute, LeanRV64D.Functions.execute_FENCE,
      LeanRV64D.Functions.is_fiom_active, h_priv, PreSail.ConcurrencyInterfaceV1.sail_barrier,
      EStateM.pure]
    -- Every arm of the match on the two fence sets retires; case on their two-bit values.
    generalize BitVec.extractLsb 1 0 (LeanRV64D.Functions.effective_fence_set pred false) = a
    generalize BitVec.extractLsb 1 0 (LeanRV64D.Functions.effective_fence_set succ false) = b
    obtain ⟨⟨a, ha⟩⟩ := a
    obtain ⟨⟨b, hb⟩⟩ := b
    interval_cases a <;> interval_cases b <;> rfl

  /-- `PAUSE` executes as the no-op, including the pc update. -/
  lemma execute_instruction_pause_eq_nop
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
      execute_instruction (.PAUSE ()) state = execute_instruction nop_instruction state := by
    simp only [execute_instruction, execute_pause_eq_nop]

  /-- `FENCE_TSO` executes as the no-op, including the pc update. -/
  lemma execute_instruction_fence_tso_eq_nop
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
      execute_instruction (.FENCE_TSO ()) state = execute_instruction nop_instruction state := by
    simp only [execute_instruction, execute_fence_tso_eq_nop]

  /-- In machine mode `FENCE` executes as the no-op, including the pc update, whatever its
      fields. -/
  lemma execute_instruction_fence_eq_nop
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (h_priv : Sail.readReg Register.cur_privilege state =
        EStateM.Result.ok Privilege.Machine state) :
      execute_instruction (.FENCE (fm, pred, succ, rs, rd)) state =
      execute_instruction nop_instruction state := by
    simp only [execute_instruction, execute_nop_instruction]
    simp only [bind, EStateM.bind]
    rcases h_pc : Sail.readReg Register.PC state with ⟨pc, s⟩ | ⟨e, s⟩
    · -- Reading the pc leaves the state as it was.
      have h_s : s = state := by
        simp [Sail.readReg, PreSail.readReg] at h_pc
        rcases h_get : state.regs.get? Register.PC <;> simp [h_get] at h_pc
        exact h_pc.2.symm
      subst h_s
      simp only [writeReg_state_success]
      rw [execute_fence_of_machine _ (readReg_of_write_other_reg_state h_priv (by decide))]
      rfl
    · rfl

  /-- `FENCE` executes as the no-op under the standing RISC-V assumptions, which put the hart
      in machine mode. -/
  lemma execute_instruction_fence_eq_nop_of_assumptions
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (h_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg) :
      execute_instruction (.FENCE (fm, pred, succ, rs, rd)) state =
      execute_instruction nop_instruction state :=
    execute_instruction_fence_eq_nop state h_assumptions.1

end PureSpec.RV64
