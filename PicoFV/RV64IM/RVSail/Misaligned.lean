import PicoFV.RV64IM.RVSail.Auxiliaries
import PicoFV.RV64IM.RVSail.Execution
import Mathlib.Tactic.IntervalCases

/-! # Misaligned loads and stores in Sail

    With misaligned access enabled (`plat_enable_misaligned_access`, and `misaligned_fault =
    NoFault` in `RISC_V_assumptions`), Sail's `vmem_read_addr` and `vmem_write_addr` split an
    access whose address is not a multiple of its width into naturally aligned pieces:
    `split_misaligned` returns `(width / 2^k, 2^k)`, where `k` is the number of trailing zero bits
    of the address (`sys/vmem_utils.sail`; `LeanRV64D/VmemUtils.lean`). These lemmas give that
    split for each width and offset class the load and store lemmas meet, so that a proof can
    rewrite with them before Sail's loop is unrolled. `Auxiliaries.lean` marks
    `split_misaligned` `simp`, so a proof that uses these lemmas removes it from its `simp`
    set. -/

namespace RV64IM

/-- An address `x % M` plus an offset that stays below `M` is `(x + k) % M`, the form Sail's
    misaligned pieces compute their addresses in. -/
theorem mod_add_eq_add_mod_of_lt {x k M : ℕ} (h : x % M + k < M) : x % M + k = (x + k) % M := by
  rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt h]

/-- Writing a register leaves memory as it was. -/
@[simp] theorem write_reg_state_mem (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r : Register) (v : RegisterType r) : (write_reg_state s r v).mem = s.mem := rfl

theorem BitVec_ctz_toNat_of_mod {x : BitVec w} {k : Nat} (h : x.toNat % 2 ^ (k + 1) = 2 ^ k) :
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
  exact BitVec_ctz_toNat_of_mod h


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


/-! ## The misaligned case of a load or store lemma

    Both tactics run in a `PureSpec.RV64.execute_*_pure_equiv` proof, on the branch where the
    address is not a multiple of the width, with these hypotheses in scope: `input`,
    `risc_v_assumptions`, `h_pc`, `h_r1`, `h_range` (the access ends within
    `Pico_address_space_size_64`), for a load `h_mem` (the bytes read), for a store `h_r2`, and
    `next_gma` (`RISC_V_assumptions_invariant_under_pc_increment`). `split` is the
    `split_misaligned_W_K` lemma for the case, applied to its offset hypothesis. They unroll Sail's
    loop over the pieces with the register and memory-region facts, discharge each piece's address
    checks with `omega`, and leave Sail's result equal to the aligned one. -/

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
/-- Unroll a misaligned load. `pure` is the opcode's `execute_*_pure`. -/
macro "misaligned_load_tac" split:term "," pure:ident : tactic => `(tactic| (
  misaligned_setup
  simp at h_mem
  simp [Sail.readReg, PreSail.readReg, writeReg_state_success, LeanRV64D.Functions.execute, h_pc]
  simp [-LeanRV64D.Functions.split_misaligned, LeanRV64D.Functions.execute_LOAD,
    LeanRV64D.Functions.vmem_read, EStateM.map, h_r1_val]
  simp [-LeanRV64D.Functions.split_misaligned, LeanRV64D.Functions.vmem_read_addr, ExceptT.run, $split:term,
    Sail.readReg, PreSail.readReg, h_mstatus, h_mprv2, h_priv, h_pma_regions, h_pma_base,
    h_pma_readable, h_pma_misaligned, h_htif, h_misa, h_mseccfg]
  simp (disch := omega) only [mod_add_eq_add_mod_of_lt, Nat.add_assoc, Nat.reduceAdd] at h_mem
  split_ifs at h_mem with h_rd
  · set_option maxRecDepth 16384 in repeat (first
      | simp (config := {maxSteps := 4000000}) (disch := omega) only [if_pos, if_neg,
          Nat.mod_eq_of_lt, mod_add_eq_add_mod_of_lt, Nat.add_assoc, Nat.reduceAdd]
      | simp (config := {maxSteps := 4000000}) (disch := simp [h_mem]) [-LeanRV64D.Functions.split_misaligned, Sail.readReg,
          PreSail.readReg, h_mstatus, h_mprv2, h_priv, h_pma_regions, h_pma_base, h_pma_readable,
          h_pma_misaligned, h_htif, h_misa, h_mseccfg, h_range', write_reg_state_mem,
          Std.ExtHashMap.getElem?_eq_some_getElem])
    simp [*, write_reg_state, $pure:ident, LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.wX, write_xreg]
  · set_option maxRecDepth 16384 in repeat (first
      | simp (config := {maxSteps := 4000000}) (disch := omega) only [if_pos, if_neg,
          Nat.mod_eq_of_lt, mod_add_eq_add_mod_of_lt, Nat.add_assoc, Nat.reduceAdd]
      | simp (config := {maxSteps := 4000000}) [-LeanRV64D.Functions.split_misaligned, Sail.readReg, PreSail.readReg, h_mstatus, h_mprv2,
          h_priv, h_pma_regions, h_pma_base, h_pma_readable, h_pma_misaligned, h_htif, h_misa,
          h_mseccfg, h_range', write_reg_state_mem, h_mem])
    -- Keep the specification's value whole, so that `congr` stops at the two values.
    generalize h_val : ($pure:ident input).rd_val = val
    simp [*, $pure:ident, wX_write_xreg_equiv]
    congr 3
    subst h_val
    simp only [$pure:ident]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
      BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
      BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ofNat]
    interval_cases i <;> simp (config := {decide := true})
    all_goals (repeat (first
      | rw [BitVec.getElem_append]
      | simp (config := {decide := true})))
    -- A wider load leaves goals whose mask bits are `Nat.testBit` of a literal, which neither
    -- `simp` nor `decide` reduces on its own: the byte the bit comes from is a variable, so the
    -- proposition is not closed. Unfolding `Nat.testBit` evaluates the literal side.
    all_goals (try simp [Nat.testBit])))

set_option hygiene false in
/-- Unroll a misaligned store. `pure` is the opcode's `execute_*_pure`, `modify` its
    `modify_memory_*`. -/
macro "misaligned_store_tac" split:term "," pure:ident "," modify:ident : tactic => `(tactic| (
  misaligned_setup
  rw [← rX_read_xreg_equiv (rd_idx := regidx.Regidx (BitVec.ofNat 5 ↑input.r2)) (h_rd := by rfl)] at h_r2
  have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_r2 reg_of_fin_neq_nextPC
  simp at h_r2_val
  simp [Sail.readReg, PreSail.readReg, writeReg_state_success, LeanRV64D.Functions.execute, h_pc]
  simp [-LeanRV64D.Functions.split_misaligned, LeanRV64D.Functions.execute_STORE,
    LeanRV64D.Functions.vmem_write, EStateM.map, h_r1_val, h_r2_val]
  simp [-LeanRV64D.Functions.split_misaligned, LeanRV64D.Functions.vmem_write_addr, ExceptT.run, $split:term,
    Sail.readReg, PreSail.readReg, h_mstatus, h_mprv2, h_priv, h_pma_regions, h_pma_base,
    h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg]
  -- As in the load tactic, the address-normalising lemmas belong in the cheap branch: Sail
  -- addresses the next piece as `(a % 2 ^ 64) + k`, and without them `omega` cannot see that
  -- the later pieces of an eight-piece store are still inside the region.
  set_option maxRecDepth 16384 in repeat (first
    | simp (config := {maxSteps := 4000000}) (disch := omega) only [if_pos, if_neg,
        Nat.mod_eq_of_lt, mod_add_eq_add_mod_of_lt, Nat.add_assoc, Nat.reduceAdd]
    | simp (config := {maxSteps := 4000000}) [-LeanRV64D.Functions.split_misaligned, Sail.readReg, PreSail.readReg, h_mstatus, h_mprv2,
        h_priv, h_pma_regions, h_pma_base, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg,
        h_range'])
  simp [$pure:ident, EStateM.set, $modify:ident, BitVec.extractLsb, BitVec.extractLsb', *]
  repeat (first
    | omega
    | (apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow] <;> omega)
    | (show Std.ExtHashMap.insert _ _ _ = Std.ExtHashMap.insert _ _ _; congr 1))))

end RV64IM
