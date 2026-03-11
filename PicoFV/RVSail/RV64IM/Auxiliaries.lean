import PicoFV.RVSail.Auxiliaries
import LeanRV64D

attribute [simp]
  instBEqSATPMode.beq

  LeanRV64D.Functions._get_Misa_C
  LeanRV64D.Functions._get_Mstatus_MPRV
  LeanRV64D.Functions.allowed_misaligned
  LeanRV64D.Functions.bits_of_physaddr
  LeanRV64D.Functions.bits_of_virtaddr
  LeanRV64D.Functions.check_misaligned
  LeanRV64D.Functions.checked_mem_read
  LeanRV64D.Functions.checked_mem_write
  LeanRV64D.Functions.currentlyEnabled
  LeanRV64D.Functions.effectivePrivilege
  LeanRV64D.Functions.encdec_reg_forwards
  LeanRV64D.Functions.encdec_reg_forwards_matches
  LeanRV64D.Functions.ext_control_check_pc
  LeanRV64D.Functions.ext_data_get_addr
  LeanRV64D.Functions.extend_value
  LeanRV64D.Functions.get_config_rvfi
  LeanRV64D.Functions.get_config_use_abi_names
  LeanRV64D.Functions.get_next_pc
  LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.is_aligned_vaddr
  LeanRV64D.Functions.is_aligned_paddr
  LeanRV64D.Functions.is_store_conditional
  LeanRV64D.Functions.matching_pma
  LeanRV64D.Functions.matching_pma_bits_range
  LeanRV64D.Functions.mem_read
  LeanRV64D.Functions.mem_read_priv
  LeanRV64D.Functions.mem_read_priv_meta
  LeanRV64D.Functions.mem_write_ea
  LeanRV64D.Functions.mem_write_value
  LeanRV64D.Functions.mem_write_value_meta
  LeanRV64D.Functions.mem_write_value_priv_meta
  LeanRV64D.Functions.MemoryOpResult_drop_meta
  LeanRV64D.Functions.misaligned_order
  LeanRV64D.Functions.not
  LeanRV64D.Functions.phys_access_check
  LeanRV64D.Functions.plat_enable_misaligned_access
  LeanRV64D.Functions.pmaCheck
  LeanRV64D.Functions.pmpCheck
  LeanRV64D.Functions.range_subset
  LeanRV64D.Functions.read_kind_of_flags
  LeanRV64D.Functions.read_ram
  LeanRV64D.Functions.reg_arch_name_raw_forwards
  LeanRV64D.Functions.reg_name_forwards
  LeanRV64D.Functions.regval_from_reg
  LeanRV64D.Functions.regval_into_reg
  LeanRV64D.Functions.RETIRE_SUCCESS
  LeanRV64D.Functions.sail_branch_announce
  LeanRV64D.Functions.sign_extend
  LeanRV64D.Functions.sign_extend
  LeanRV64D.Functions.split_misaligned
  LeanRV64D.Functions.sys_misaligned_order_decreasing
  LeanRV64D.Functions.sys_pmp_count
  LeanRV64D.Functions.to_bits
  LeanRV64D.Functions.to_bits_checked
  LeanRV64D.Functions.translateAddr
  LeanRV64D.Functions.within_clint
  LeanRV64D.Functions.within_htif_readable
  LeanRV64D.Functions.within_htif_writable
  LeanRV64D.Functions.within_mmio_readable
  LeanRV64D.Functions.within_mmio_writable
  LeanRV64D.Functions.write_kind_of_flags
  LeanRV64D.Functions.write_ram
  LeanRV64D.Functions.xlen
  LeanRV64D.Functions.xlen_bytes
  LeanRV64D.Functions.xreg_full_write_callback
  LeanRV64D.Functions.xreg_write_callback
  LeanRV64D.Functions.zero_reg
  LeanRV64D.Functions.zeros
  LeanRV64D.Functions.zeros
  LeanRV64D.Functions.zopz0zI_s
  LeanRV64D.Functions.zopz0zI_u
  LeanRV64D.Functions.zopz0zIzJ_u
  LeanRV64D.Functions.zopz0zKzJ_s
  LeanRV64D.Functions.zopz0zKzJ_u
  zero_extend

  Sail.ConcurrencyInterfaceV1.sail_mem_read
  Sail.ConcurrencyInterfaceV1.sail_mem_write
  Sail.SailME.run

namespace RV64IM

  section SimplerMonadicReasoning

    /-- Simpler monadic pure ok -/
    @[simp high]
    lemma pure_ok_equiv :
      @pure (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception) EStateM.instMonad.toPure T val =
      λ s => EStateM.Result.ok val s
    := by
      rfl

    /-- Simpler monadic pure exception -/
    @[simp high]
    lemma pure_except_equiv :
      @pure (SailME ExecutionResult) ExceptT.instMonad.toPure T val state =
      EStateM.Result.ok (Except.ok val) state
    := by
      rfl

    /-- Simpler monadic throw -/
    @[simp high]
    lemma throw_equiv :
      @throw
        (Sail.Error exception)
        (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception)
        (instMonadExceptOfMonadExceptOf
          (Sail.Error exception)
          (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception))
        T
        error =
      λ s_1 => EStateM.Result.error error s_1
    := by
      unfold throw instMonadExceptOfMonadExceptOf
      unfold throwThe MonadExceptOf.throw
      unfold EStateM.instMonadExceptOfOfBacktrackable EStateM.throw
      dsimp

    /-- Simpler bind equiv -/
    @[simp high]
    lemma bind_equiv :
      (@bind
        SailM
        EStateM.instMonad.toBind
        T1
        T2
        f1
        f2
      ) = λ s =>
        match f1 s with
        | EStateM.Result.ok a s => f2 a s
        | EStateM.Result.error e s => EStateM.Result.error e s
    := by
      unfold bind EStateM.instMonad EStateM.bind Monad.toBind
      simp
      funext state
      set state' := f1 state
      cases state' <;> simp

    @[simp high]
    lemma EStateM_bind_equiv :
      @EStateM.bind
        (Sail.Error exception)
        (PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
        (Except ExecutionResult Unit)
        (Except ExecutionResult ExecutionResult)
        f1
        f2
        state =
      (match f1 state with
      | EStateM.Result.ok a s => f2 a s
      | EStateM.Result.error e s => EStateM.Result.error e s)
    := by
      simp [EStateM.bind]
      set state' := f1 state
      cases state' <;> simp

  end SimplerMonadicReasoning

  section RegisterManipulation

    /-- Converting a register to a Fin 32 -/
    def regidx_to_fin (r : regidx): Fin 32 :=
      match r with
        | regidx.Regidx r => ⟨
            r.toNat,
            by {
              have : (if false = true then 4 else 5) ≤ 5 := by decide
              convert BitVec.toNat_lt_twoPow_of_le this
            }
          ⟩

    def reg_of_fin (r : Fin 32) : State :=
      match r.1 with
        | 1 => Register.x1
        | 2 => Register.x2
        | 3 => Register.x3
        | 4 => Register.x4
        | 5 => Register.x5
        | 6 => Register.x6
        | 7 => Register.x7
        | 8 => Register.x8
        | 9 => Register.x9
        | 10 => Register.x10
        | 11 => Register.x11
        | 12 => Register.x12
        | 13 => Register.x13
        | 14 => Register.x14
        | 15 => Register.x15
        | 16 => Register.x16
        | 17 => Register.x17
        | 18 => Register.x18
        | 19 => Register.x19
        | 20 => Register.x20
        | 21 => Register.x21
        | 22 => Register.x22
        | 23 => Register.x23
        | 24 => Register.x24
        | 25 => Register.x25
        | 26 => Register.x26
        | 27 => Register.x27
        | 28 => Register.x28
        | 29 => Register.x29
        | 30 => Register.x30
        | _ => Register.x31

    @[simp]
    lemma register_type_reg_of_fin_equiv (r : Fin 32) :
      RegisterType (reg_of_fin r) = BitVec 64
    := by
      fin_cases r <;>
      simp [reg_of_fin, RegisterType]

    @[simp]
    lemma register_type_pc_equiv :
      RegisterType Register.PC = BitVec 64
    := by
      simp [RegisterType]

    /-- Register read in terms of Fin 32 -/
    def read_xreg (reg : Fin 32) : SailM (BitVec 64) :=
      match reg.1 with
        | 0 => pure (0#64)
        | _ => (register_type_reg_of_fin_equiv reg) ▸ (Sail.readReg (reg_of_fin reg))

    set_option maxHeartbeats 0 in
    /-- Equivalence of register reading when in Fin 32 -/
    lemma rX_read_xreg_equiv
      (state)
      (rd_idx : regidx)
      (rd : Fin 32)
      (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
    :
      LeanRV64D.Functions.rX_bits rd_idx state =
      read_xreg rd state
    := by
      unfold LeanRV64D.Functions.rX_bits
      simp [h_rd]
      unfold LeanRV64D.Functions.rX read_xreg
      fin_cases rd
      . simp
      all_goals
        simp [PreSail.readReg, reg_of_fin]
        aesop

    /-- Successful read -/
    @[simp]
    lemma readReg_succ
    :
      (Sail.readReg reg state = EStateM.Result.ok reg_val state) ↔
      (state.regs.get? reg = .some reg_val)
    := by
      simp [Sail.readReg, PreSail.readReg]
      cases (state.regs.get? reg) <;> simp

    /-- Successful xread -/
    @[simp]
    lemma readXReg_succ
    :
      ((register_type_reg_of_fin_equiv reg) ▸ (Sail.readReg (reg_of_fin reg))) state = EStateM.Result.ok reg_val state ↔
      state.regs.get? (reg_of_fin reg) = .some ((register_type_reg_of_fin_equiv reg) ▸ reg_val)
    := by
      fin_cases reg <;> simp [reg_of_fin] <;> exact readReg_succ

    /-- Unsuccessful read -/
    @[simp]
    lemma readReg_fail
    :
      Sail.readReg reg state = EStateM.Result.error Sail.Error.Unreachable state ↔
      state.regs.get? reg = .none
    := by
      simp [Sail.readReg, PreSail.readReg]
      cases (state.regs.get? reg) <;> simp

    def write_xreg (reg : Fin 32) (val : BitVec 64) : SailM Unit :=
      match reg.1 with
      | 0 => pure ()
      | _ => Sail.writeReg (reg_of_fin reg) ((register_type_reg_of_fin_equiv reg) ▸ val)

    set_option maxHeartbeats 0
    lemma wX_write_xreg_equiv
      (data)
      (state)
      (rd_idx : regidx)
      (rd : Fin 32)
      (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
    :
      LeanRV64D.Functions.wX_bits rd_idx data state =
      write_xreg rd data state
    := by
      unfold LeanRV64D.Functions.wX_bits
      simp [h_rd]
      unfold LeanRV64D.Functions.wX
      simp [write_xreg]
      fin_cases rd <;> aesop

    def write_reg_state
      (state: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (register: Register)
      (value: RegisterType register)
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource := {
        regs := state.regs.insert register value,
        choiceState := state.choiceState,
        mem := state.mem,
        tags := state.tags,
        cycleCount := state.cycleCount,
        sailOutput := state.sailOutput
      }

    lemma writeReg_state_success:
      (Sail.writeReg register value state) =
      EStateM.Result.ok PUnit.unit (write_reg_state state register value)
    := by
      simp [
        PreSail.writeReg,
        write_reg_state,
      ]

    @[simp]
    lemma writeReg_get_same
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    :
      (write_reg_state state register value).regs.get? register = Option.some value
    := by
      unfold write_reg_state
      grind

    @[simp]
    lemma writeReg_read_same
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    :
      Sail.readReg register (write_reg_state state register value) = EStateM.Result.ok value (write_reg_state state register value)
    := by
      simp [write_reg_state, Sail.readReg, PreSail.readReg]

    @[simp]
    lemma writeReg_write_same
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    :
      write_reg_state
        (write_reg_state state register value1)
        register
        value2
      =
      write_reg_state state register value2
    := by
      simp [
        write_reg_state,
      ]
      apply Std.ExtDHashMap.ext_get?
      intro reg
      by_cases h: reg = register
      . grind
      . grind

    lemma writeReg_read_diff
      (h: Sail.readReg register1 state = EStateM.Result.ok value1 state)
      (h_neq: register1 ≠ register2)
    :
      (write_reg_state state register2 value2).regs.get? register1 = .some value1
    := by
      unfold write_reg_state
      simp at h
      grind

    set_option pp.proofs true in
    lemma read_xreg_write_other_reg_state
      (r1 : Fin 32)
      (h: read_xreg r1 state = EStateM.Result.ok read_val state)
      (h_neq: reg_of_fin r1 ≠ register)
    :
      read_xreg r1 (write_reg_state state register write_val) =
      EStateM.Result.ok
        read_val
        (write_reg_state state register write_val)
    := by
      by_cases rz : r1.val = 0
      . simp_all [read_xreg]
      . simp_all [read_xreg, write_reg_state]
        grind

    set_option maxHeartbeats 0 in
    lemma rX_bits_write_other_reg_state
      (h_r_val : LeanRV64D.Functions.rX_bits (regidx.Regidx r) state = EStateM.Result.ok r_val state)
      (h_neq : (reg_of_fin r.toFin) ≠ reg)
    :
      LeanRV64D.Functions.rX_bits (regidx.Regidx r) (write_reg_state state reg val) =
      EStateM.Result.ok r_val (write_reg_state state reg val)
    := by
      trans read_xreg r.toFin (write_reg_state state reg val)
      . clear *-
        simp [read_xreg, LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.rX]
        rcases r with ⟨r, ub_r⟩
        simp at *; simp at ub_r
        interval_cases r <;> simp [reg_of_fin] <;> grind
      . have := @read_xreg_write_other_reg_state state r_val reg val r.toFin
        have h_read_xreg : read_xreg r.toFin state = EStateM.Result.ok r_val state
        := by
          simp [read_xreg]
          simp [LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.rX] at h_r_val
          rw [← h_r_val]; clear *-
          simp [reg_of_fin]
          rcases r with ⟨r, ub_r⟩
          simp at *; simp at ub_r
          interval_cases r <;> simp <;> grind
        tauto

    lemma reg_of_fin_neq_nextPC :
      (reg_of_fin r) ≠ Register.nextPC
    := by
      fin_cases r <;> simp [reg_of_fin]

    lemma reg_of_fin_neq_mstatus :
      (reg_of_fin r) ≠ Register.mstatus
    := by
      fin_cases r <;> simp [reg_of_fin]

    lemma reg_of_fin_neq_cur_privilege :
      (reg_of_fin r) ≠ Register.cur_privilege
    := by
      fin_cases r <;> simp [reg_of_fin]

    lemma reg_of_fin_neq_htif_tohost_base :
      (reg_of_fin r) ≠ Register.htif_tohost_base
    := by
      fin_cases r <;> simp [reg_of_fin]

    lemma reg_of_fin_neq_pma_regions :
      (reg_of_fin r) ≠ Register.pma_regions
    := by
      fin_cases r <;> simp [reg_of_fin]

    lemma readReg_of_write_other_reg_state
      (h_reg : Sail.readReg reg state = EStateM.Result.ok val state)
      (h_neq : reg ≠ reg')
    :
      Sail.readReg reg (write_reg_state state reg' val') =
      EStateM.Result.ok val (write_reg_state state reg' val')
    := by
      simp [
        Sail.readReg, PreSail.readReg, write_reg_state
      ] at ⊢ h_reg
      have :
        (state.regs.insert reg' val').get? reg = state.regs.get? reg
      := by grind
      simp [this]
      rcases h: state.regs.get? reg
      . simp [h] at h_reg
      . simp [h] at ⊢ h_reg
        exact h_reg

    lemma insert_reg_eq_self
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      {r : Fin 32}
      (h_r_not_zero : ¬ r.val = 0)
      (h_read_xreg : (read_xreg r state = EStateM.Result.ok val state))
    :
      state.regs.insert (reg_of_fin r) ((register_type_reg_of_fin_equiv r) ▸ val) = state.regs
    := by
      rw [ExtDHashMap.insert_eq_self]
      suffices h_some : ((register_type_reg_of_fin_equiv r) ▸ (state.regs.get? (reg_of_fin r))) = .some val
      . generalize_proofs pfl pft at h_some
        rw [← eq_rec_inj (h := pft)]
        grind
      . simp [read_xreg, Sail.readReg, PreSail.readReg] at h_read_xreg
        cases h : state.regs.get? (reg_of_fin r) <;>
          fin_cases r <;> simp_all

  end RegisterManipulation

  section SimplerFunctions

    @[simp high]
    lemma bit_to_bool :
      LeanRV64D.Functions.bit_to_bool =
      λ b => b == 1#1
    := by
      unfold
        LeanRV64D.Functions.bit_to_bool
        LeanRV64D.Functions.bool_bit_backwards
      grind

    @[simp]
    lemma bool_bits_forwards_to_if {b : Bool} :
      LeanRV64D.Functions.bool_bit_forwards b = if b then 1#1 else 0#1
    := by aesop

    @[simp high]
    lemma currentlyEnabled_Zca_of_misa_val
      {misa_val : BitVec 64}
      (h : Sail.readReg Register.misa state = EStateM.Result.ok misa_val state)
    :
      LeanRV64D.Functions.currentlyEnabled extension.Ext_Zca state =
      EStateM.Result.ok false state
    := by
      simp [LeanRV64D.Functions.currentlyEnabled]
      aesop

      @[simp high]
      lemma sail_assert_equiv :
        Sail.assert =
        λ check msg state =>
          if check
          then EStateM.Result.ok () state
          else EStateM.Result.error (Sail.Error.Assertion msg) state
      := by
        unfold Sail.assert PreSail.assert
        simp
        funext check message state
        cases check <;> simp

    @[simp]
    lemma translationMode_in_machine
    :
      LeanRV64D.Functions.translationMode Privilege.Machine state =
      EStateM.Result.ok ( SATPMode.Bare ) state
    := by
      aesop

    @[simp high]
    lemma set_next_pc_equiv :
      LeanRV64D.Functions.set_next_pc pc =
      Sail.writeReg Register.nextPC pc
    := rfl

  end SimplerFunctions

  section Memory

    -- Pico address space size
    notation "Pico_address_space_size_64" => 2 ^ 63

    @[simp]
    lemma bare_is_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl

  end Memory

  section ControlFlow

    @[simp]
    lemma jump_to_equiv:
      LeanRV64D.Functions.jump_to target state =
        if (BitVec.ofBool target[0]) == 1#1 then EStateM.Result.error (Sail.Error.Assertion "extensions/I/base_insts.sail:59.25-59.26") state
          else match state.regs.get? Register.misa with
            | .none => EStateM.Result.error (Sail.Error.Unreachable) state
            | .some _ =>
              if (BitVec.ofBool target[1] == 1#1)
              then EStateM.Result.ok (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr target), (ExceptionType.E_Fetch_Addr_Align ()))) state
              else EStateM.Result.ok (ExecutionResult.Retire_Success ()) (write_reg_state state Register.nextPC target)
    := by
      simp [
        LeanRV64D.Functions.jump_to,
        LeanRV64D.Functions.currentlyEnabled
      ]
      by_cases h_bit_0 : BitVec.ofBool target[0] = 0#1 <;> simp [h_bit_0]
      . cases h_misa: state.regs.get? Register.misa with
        | none =>
          rw [← readReg_fail] at h_misa
          simp [h_misa]
        | some misa_val =>
          rw [← readReg_succ] at h_misa
          simp [h_misa]
          by_cases h_bit_1 : BitVec.ofBool target[1] = 1#1 <;> simp [h_bit_1]
          simp [writeReg_state_success]
      . grind

  end ControlFlow

  section Spec

    @[simp]
    noncomputable def execute_instruction
      (instr : instruction)
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    :=
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute instr
      ) state

    def RISC_V_assumptions
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (mstatus : RegisterType Register.mstatus)
      (pmaRegion : PMA_Region)
      (misa : RegisterType Register.misa)
      (mseccfg : RegisterType Register.mseccfg)
    : Prop :=
      -- Assumption A1.1: machine privilege
      Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state ∧
      -- Assumption A1.2: MPRV bit of the mstatus register not set
      (Sail.readReg Register.mstatus state = EStateM.Result.ok mstatus state ∧ BitVec.extractLsb 17 17 mstatus = 0#1) ∧
      -- A2.1 : Single PMA region
      Sail.readReg Register.pma_regions state = EStateM.Result.ok [ pmaRegion ] state ∧
      -- A2.2 : with base 0 and at least 2^29 bytes in size
      pmaRegion.base = 0 ∧
      Pico_address_space_size_64 ≤ pmaRegion.size.toNat ∧
      -- A2.3 : with all addresses readable and writable, and misaligned accesses treated as errors
      pmaRegion.attributes.readable ∧
      pmaRegion.attributes.writable ∧
      pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault ∧
      -- Assumption A3: no host-target interface
      Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok .none state ∧
      -- Assumption A4.1: misa register exists
      Sail.readReg Register.misa state = EStateM.Result.ok misa state ∧
      -- Assumption A4.2: mseccfg register exists
      Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state

    lemma RISC_V_assumptions_invariant_under_pc_increment
      (assumptions : RISC_V_assumptions s mstatus pmaRegion misa mseccfg)
    :
      RISC_V_assumptions (write_reg_state s Register.nextPC val) mstatus pmaRegion misa mseccfg
    := by
      obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := assumptions
      simp [RISC_V_assumptions]
      split_ands <;> (try assumption)
      . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) (by assumption) (by trivial)]
      . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_mprv.1 (by trivial)]
      . exact h_mprv.2
      . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_pma_regions (by trivial)]
      . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_htif (by trivial)]
      . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_misa (by trivial)]
      . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_mseccfg (by trivial)]

  end Spec

end RV64IM
