import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Execution
import Mathlib.Tactic.IntervalCases

/-! # Misaligned stores in Sail

    With misaligned access enabled (`plat_enable_misaligned_access`, and `misaligned_fault =
    NoFault` in `RISC_V_assumptions`), Sail's `vmem_write_addr` splits an access whose address
    is not a multiple of its width into naturally aligned pieces: `split_misaligned` returns
    `(width / 2^k, 2^k)`, where `k` is the number of trailing zero bits of the address
    (`sys/vmem_utils.sail`; `LeanRV64D/VmemUtils.lean`), and a loop with that many passes writes
    one piece per pass.

    This file gives the split for each width and offset class the store lemmas meet
    (`split_misaligned_W_K`), a lemma that replaces the loop by its last state once each pass is
    known (`untilFuelM_pieces`), and the tactic that proves the misaligned case of a store lemma
    with them. `Auxiliaries.lean` marks `split_misaligned`, `untilFuelM` and `untilFuelM.go`
    `simp`, so a proof that uses these lemmas removes them from its `simp` set. -/

namespace RV64IM

/-- An address `x % M` plus an offset that stays below `M` is `(x + k) % M`, the form Sail's
    misaligned pieces compute their addresses in. -/
theorem mod_add_eq_add_mod_of_lt {x k M : ℕ} (h : x % M + k < M) : x % M + k = (x + k) % M := by
  rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt h]

/-- Writing a register leaves memory as it was. -/
@[simp] theorem write_reg_state_mem (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r : Register) (v : RegisterType r) : (write_reg_state s r v).mem = s.mem := rfl

theorem bitVec_ctz_toNat_of_mod {x : BitVec w} {k : Nat} (h : x.toNat % 2 ^ (k + 1) = 2 ^ k) :
    x.ctz.toNat = k := by
  have hbit : ∀ i, i < k + 1 → x.getLsbD i = decide (k = i) := by
    intro i hi
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow] at this
    simp [BitVec.getLsbD, ← this, hi]
  have hk : x.getLsbD k = true := by simpa using hbit k (by omega)
  have hx : x ≠ 0#w := by intro h0; simp [h0] at hk
  have h1 := BitVec.getLsbD_true_ctz_of_ne_zero hx
  rcases Nat.lt_trichotomy x.ctz.toNat k with hlt | heq | hgt
  · have := hbit x.ctz.toNat (by omega); rw [h1] at this; simp at this; omega
  · exact heq
  · have := BitVec.getLsbD_false_of_lt_ctz hgt; simp [hk] at this

theorem sail_ctz_of_mod {x : BitVec w} {k : Nat} (h : x.toNat % 2 ^ (k + 1) = 2 ^ k) :
    Sail.BitVec.countTrailingZeros x = k := by
  simp only [Sail.BitVec.countTrailingZeros, Sail.BitVec.countLeadingZeros]
  exact bitVec_ctz_toNat_of_mod h


local macro "split_misaligned_tac" k:term : tactic => `(tactic| (
  simp [LeanRV64D.Functions.split_misaligned, LeanRV64D.Functions.is_aligned_vaddr,
    LeanRV64D.Functions.bits_of_virtaddr, LeanRV64D.Functions.allowed_misaligned,
    LeanRV64D.Functions.sys_misaligned_allowed_within_exp,
    LeanRV64D.Functions.sys_misaligned_byte_by_byte, sail_ctz_of_mod (k := $k) (by omega)]
  rw [if_neg (by omega)]
  rfl))


theorem split_misaligned_2_0 (v : BitVec 64) (h : v.toNat % 2 = 1) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    LeanRV64D.Functions.split_misaligned (virtaddr.Virtaddr v) 2 s = EStateM.Result.ok (2, 1) s := by
  split_misaligned_tac 0
theorem split_misaligned_4_0 (v : BitVec 64) (h : v.toNat % 2 = 1) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    LeanRV64D.Functions.split_misaligned (virtaddr.Virtaddr v) 4 s = EStateM.Result.ok (4, 1) s := by
  split_misaligned_tac 0
theorem split_misaligned_4_1 (v : BitVec 64) (h : v.toNat % 4 = 2) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    LeanRV64D.Functions.split_misaligned (virtaddr.Virtaddr v) 4 s = EStateM.Result.ok (2, 2) s := by
  split_misaligned_tac 1
theorem split_misaligned_8_0 (v : BitVec 64) (h : v.toNat % 2 = 1) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    LeanRV64D.Functions.split_misaligned (virtaddr.Virtaddr v) 8 s = EStateM.Result.ok (8, 1) s := by
  split_misaligned_tac 0
theorem split_misaligned_8_1 (v : BitVec 64) (h : v.toNat % 4 = 2) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    LeanRV64D.Functions.split_misaligned (virtaddr.Virtaddr v) 8 s = EStateM.Result.ok (4, 2) s := by
  split_misaligned_tac 1
theorem split_misaligned_8_2 (v : BitVec 64) (h : v.toNat % 8 = 4) (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    LeanRV64D.Functions.split_misaligned (virtaddr.Virtaddr v) 8 s = EStateM.Result.ok (2, 4) s := by
  split_misaligned_tac 2


/-! ## Sail's loop over the pieces

    `untilFuelM fuel cond init f` runs `f` at most `fuel` times, stopping early once `cond`
    holds. Sail's piece loop carries `(finished, i, write_success)` and its condition returns
    `finished`. The lemmas take the monad instance as an argument, with what they need of it as
    hypotheses, because `simp` has unfolded the instance by the time the loop is in the goal:
    its `bind` and `pure` are still `ExceptT`'s, which `rfl` shows, but the instance as a whole
    is no longer syntactically `ExceptT.instMonad`. -/

/-- A loop whose passes are known ends in the last of them. If pass `i` of the body takes loop
    variables `xs i` and state `ss i` to `xs (i + 1)` and `ss (i + 1)`, and the first component
    stays `false` strictly between the first and the last pass, then `d` passes from position
    `k` end at `xs n` and `ss n`. By induction on the fuel `d`. -/
theorem untilFuelM_go_steps {ε σ E β : Type} (inst : Monad (ExceptT E (EStateM ε σ)))
    (hbind : ∀ {α γ : Type} (x : ExceptT E (EStateM ε σ) α) (g : α → ExceptT E (EStateM ε σ) γ),
      @Bind.bind _ (@Monad.toBind _ inst) α γ x g = ExceptT.bind x g)
    (hpure : ∀ {α : Type} (a : α),
      @Pure.pure _ (@Applicative.toPure _ (@Monad.toApplicative _ inst)) α a = ExceptT.pure a)
    (cond : Bool × β → ExceptT E (EStateM ε σ) Bool)
    (hcond : ∀ x s, cond x s = EStateM.Result.ok (Except.ok x.1) s)
    (f : Bool × β → ExceptT E (EStateM ε σ) (Bool × β))
    (xs : Nat → Bool × β) (ss : Nat → σ) (n : Nat)
    (hstep : ∀ i, i < n →
      f (xs i) (ss i) = EStateM.Result.ok (Except.ok (xs (i + 1))) (ss (i + 1)))
    (hrun : ∀ i, 0 < i → i < n → (xs i).1 = false) :
    ∀ d k, k + d = n →
      @untilFuelM.go _ _ inst cond f (xs k) d (ss k) =
        EStateM.Result.ok (Except.ok (xs n)) (ss n) := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have : k = n := by omega
    subst this
    unfold untilFuelM.go
    rw [hpure]
    rfl
  | succ d ih =>
    intro k hk
    have h1 := hstep k (by omega)
    have h2 := hcond (xs (k + 1)) (ss (k + 1))
    have h3 := ih (k + 1) (by omega)
    unfold untilFuelM.go
    simp only [hbind, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind, h1, h2]
    by_cases hb : (xs (k + 1)).1 = true
    · rw [if_pos hb, hpure]
      have hkn : k + 1 = n := by
        by_contra hne
        have := hrun (k + 1) (by omega) (by omega)
        rw [this] at hb
        exact Bool.false_ne_true hb
      subst hkn
      rfl
    · rw [if_neg hb]
      exact h3

/-- Sail's loop over the `n` pieces of a split access, replaced by its result. If pass `i` of
    the body, started with `(false, i, true)` in state `ss i`, succeeds in state `ss (i + 1)`
    and moves the loop variables as Sail's loop does (`finished` on the last piece, the next
    index otherwise), then the loop started in `ss 0` returns `(true, n - 1, true)` in state
    `ss n`. -/
theorem untilFuelM_pieces {ε σ E : Type} (inst : Monad (ExceptT E (EStateM ε σ)))
    (hbind : ∀ {α γ : Type} (x : ExceptT E (EStateM ε σ) α) (g : α → ExceptT E (EStateM ε σ) γ),
      @Bind.bind _ (@Monad.toBind _ inst) α γ x g = ExceptT.bind x g)
    (hpure : ∀ {α : Type} (a : α),
      @Pure.pure _ (@Applicative.toPure _ (@Monad.toApplicative _ inst)) α a = ExceptT.pure a)
    (n : Nat) (hn : 0 < n)
    (cond : Bool × Nat × Bool → ExceptT E (EStateM ε σ) Bool)
    (hcond : ∀ x s, cond x s = EStateM.Result.ok (Except.ok x.1) s)
    (f : Bool × Nat × Bool → ExceptT E (EStateM ε σ) (Bool × Nat × Bool))
    (ss : Nat → σ) (s0 : σ) (hs0 : ss 0 = s0)
    (hstep : ∀ i, i < n → f (false, i, true) (ss i) =
      EStateM.Result.ok (Except.ok (decide (i + 1 = n), (if i + 1 = n then i else i + 1), true))
        (ss (i + 1))) :
    @untilFuelM _ _ inst n cond (false, 0, true) f s0 =
      EStateM.Result.ok (Except.ok (true, n - 1, true)) (ss n) := by
  subst hs0
  have h := untilFuelM_go_steps inst hbind hpure cond hcond f
    (fun i => (decide (i = n), (if i = n then n - 1 else i), true)) ss n
    (by
      intro i hi
      have hne : i ≠ n := by omega
      simp only [hne, decide_false, if_false]
      rw [hstep i hi]
      by_cases h : i + 1 = n
      · have : n - 1 = i := by omega
        simp [h, this]
      · simp [h])
    (by
      intro i _ hi
      have hne : i ≠ n := by omega
      simp [hne])
    n 0 (by omega)
  have h0 : (0 : Nat) ≠ n := by omega
  simp only [h0, decide_false, if_false, decide_true, if_true] at h
  exact h


/-! ## The states a split store passes through -/

/-- Memory after the low `k` bytes of `v` are written at `a`, lowest byte first. -/
def mem_store_bytes {w : Nat} (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec w) :
    Nat → Std.ExtHashMap Nat (BitVec 8)
  | 0 => mem
  | k + 1 => (mem_store_bytes mem a v k).insert (a + k) (v.extractLsb' (8 * k) 8)

/-- The state after the low `k` bytes of `v` are written at `a`: only memory differs. -/
def state_store_bytes {w : Nat}
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (a : Nat) (v : BitVec w)
    (k : Nat) : PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { s with mem := mem_store_bytes s.mem a v k }

section
variable {w : Nat} (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (a : Nat)
  (v : BitVec w) (k : Nat)

@[simp] theorem state_store_bytes_regs : (state_store_bytes s a v k).regs = s.regs := rfl
@[simp] theorem state_store_bytes_mem :
    (state_store_bytes s a v k).mem = mem_store_bytes s.mem a v k := rfl
@[simp] theorem state_store_bytes_tags : (state_store_bytes s a v k).tags = s.tags := rfl
@[simp] theorem state_store_bytes_choiceState :
    (state_store_bytes s a v k).choiceState = s.choiceState := rfl
@[simp] theorem state_store_bytes_cycleCount :
    (state_store_bytes s a v k).cycleCount = s.cycleCount := rfl
@[simp] theorem state_store_bytes_sailOutput :
    (state_store_bytes s a v k).sailOutput = s.sailOutput := rfl

end


/-! ## The misaligned case of a store lemma

    `misaligned_store_tac` runs in a `PureSpec.RV64.execute_*_pure_equiv` proof, on the branch
    where the address is not a multiple of the width, with these hypotheses in scope: `input`,
    `state`, `risc_v_assumptions`, `h_pc`, `h_r1`, `h_r2`, `h_range` (the access ends within
    `Pico_address_space_size_64`) and `next_gma`
    (`RISC_V_assumptions_invariant_under_pc_increment`). It keeps Sail's loop folded, replaces it
    with `untilFuelM_pieces`, where the state after `i` pieces is `state_store_bytes` of the
    first `i * b` bytes, and proves each pass on its own: the pass reads the register and
    memory-region facts, which a memory write leaves unchanged, and its address checks follow
    from `h_range` by `omega`. -/

set_option hygiene false in
/-- The common start: register facts in the form a memory write leaves unchanged. -/
macro "misaligned_setup" : tactic => `(tactic| (
  rw [readReg_succ] at h_pc
  have h_range' := h_range
  simp at h_range'
  rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r1)) (h_rd := by rfl)] at h_r1
  have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_r1 reg_of_fin_neq_nextPC
  simp at h_r1_val
  obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable,
    h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma
  have h_mstatus := readReg_succ.1 h_mprv.1
  have h_mprv2 := h_mprv.2
  rw [readReg_succ] at h_priv h_pma_regions h_htif h_misa h_mseccfg))

set_option hygiene false in
/-- One pass of the loop over the pieces of a split store: the body, run on the state after
    the earlier pieces, succeeds and writes this piece's bytes. The goal is one `hstep` instance
    of `untilFuelM_pieces` at a literal index. -/
macro "misaligned_store_piece" : tactic => `(tactic| (
  simp only []
  set_option maxRecDepth 16384 in repeat (first
    | simp (disch := omega) only [if_pos, if_neg,
        Nat.mod_eq_of_lt, mod_add_eq_add_mod_of_lt, Nat.add_assoc, Nat.reduceAdd]
    | simp [-LeanRV64D.Functions.split_misaligned, Sail.readReg, PreSail.readReg, h_mstatus, h_mprv2,
        h_priv, h_pma_regions, h_pma_base, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg,
        h_range'])
  simp [state_store_bytes, mem_store_bytes, BitVec.extractLsb, BitVec.extractLsb']
  repeat (first
    | omega
    | (apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow] <;> omega)
    | (show Std.ExtHashMap.insert _ _ _ = Std.ExtHashMap.insert _ _ _; congr 1))))

set_option hygiene false in
/-- The misaligned case of a store lemma. `split` is the `split_misaligned_W_K` lemma for the
    case, applied to its offset hypothesis; `pure` is the opcode's `execute_*_pure` and `modify`
    its `modify_memory_*`; `n` and `b` are the split, `n` pieces of `b` bytes. Each bullet must
    close its goal, so a pass that is not proved is an error at the call, with that pass as the
    goal shown. -/
macro "misaligned_store_tac" split:term "," pure:ident "," modify:ident "," n:num "," b:num : tactic => `(tactic| (
  misaligned_setup
  rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r2)) (h_rd := by rfl)] at h_r2
  have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_r2 reg_of_fin_neq_nextPC
  simp at h_r2_val
  simp [Sail.readReg, PreSail.readReg, writeReg_state_success, LeanRV64D.Functions.execute, h_pc]
  simp [-LeanRV64D.Functions.split_misaligned, LeanRV64D.Functions.execute_STORE,
    LeanRV64D.Functions.vmem_write, EStateM.map, h_r1_val, h_r2_val]
  simp [-LeanRV64D.Functions.split_misaligned, -untilFuelM, -untilFuelM.go,
    LeanRV64D.Functions.vmem_write_addr, ExceptT.run, $split:term]
  rw [untilFuelM_pieces (n := $n) (hn := by decide)
    (ss := fun i => state_store_bytes (write_reg_state state Register.nextPC (input.PC + 4#64))
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat input.r2_val (i * $b))]
  rotate_left
  · intros; rfl
  · intros; rfl
  · intro _ _; rfl
  · rfl
  · intro i hi
    interval_cases i <;> misaligned_store_piece
  simp [$pure:ident, EStateM.set, $modify:ident, state_store_bytes, mem_store_bytes,
    BitVec.extractLsb, BitVec.extractLsb']))

end RV64IM
