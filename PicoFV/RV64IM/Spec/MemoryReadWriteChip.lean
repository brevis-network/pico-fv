import PicoFV.RV64IM.Spec.CodeRangeGadget
import PicoFV.RV64IM.Constraints.MemoryReadWriteChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryReadWriteChip — the Memory promise

What the chip proves about each row (`MemoryReadWriteChip::eval`,
`vm/src/chips/chips/riscv_memory/read_write/constraints.rs`, Pico v3.2.0
`fcfa504624657d0c417c43f1233d5d891f293ff9`; constraints and messages in
`Constraints/MemoryReadWriteChip.lean`).

- `spec_LB` … `spec_SD`, one per opcode: on a row whose flag for that instruction is 1, the
  memory dispatch the row receives from the CPU chip meets the Memory promise
  `MemoryBus.Spec` (`RVSail/Buses.lean`): a load's value has 16-bit pieces, the address
  `b + c` lies in `[2^16, 2^32)`, and a load's value is the sign or zero extension its opcode
  names when `op_a_0 = 0`.
- `wf_asrt`: every message the row receives at `-1` meets its promise: the memory dispatch the
  Memory promise, and the double word written back 16-bit pieces (`StateBusEntry`).
- `ext_asrt`: the row asserts nothing to the tables it looks up.
- `aligned_address`: the address of the double word the row reads and writes back,
  `[addr_word_0 - offset, addr_word_1, 0]`, is `b + c` with its three low bits cleared, its first
  two pieces below `2^16`, and the offset bits are those low bits.
- `store_misses_code_range`: on a store row the bytes written miss the code range the row looks
  up, through the `code_range` gadget (`CodeRangeGadget.Spec.gadget_spec`).

Each theorem assumes the row's constraints (`allHold`) and what its messages are promised
(`bus_row_all_ext_asm`, `bus_row_all_wf_asm`): from the CPU chip, as the sender of the memory
dispatch, that `b` and `c` have 16-bit pieces, so does a store's `a`, and `a = 0` when
`op_a_0 ≠ 0` (`MemoryBus.externals`); from the memory argument, that the double word read has
16-bit pieces; from the byte table, the range checks; from the Program table, that the code
range has 16-bit pieces. The per-opcode theorems also take the row's flag, and `aligned_address`
takes `is_memory = 1`, which says the row is real; `store_misses_code_range` takes the sum of
the store flags = 1.

Nothing here says which memory a load reads or a store writes: the Memory promise does not ask
it. `Spec/MemoryReadWriteChipDataFlow.lean` proves that apart, for every row
(`dataFlow_of_allHold`). The chip takes only accesses aligned to their width (constraints 20 to
22); the promise does not ask that either, since the unaligned chip receives the same message.
-/

namespace MemoryReadWriteChip.Spec

  open RV64IM_Interactions
  open MemoryReadWriteChip.ConstraintsAndBuses
  open MemoryReadWriteChip.Interactions
  open MemoryReadWriteChip.Interpretations

  /-! ### 64-bit words -/

  /-- A 64-bit value is the sign extension of its low `w` bits exactly when its number is the
      number of those bits, plus `2^64 - 2^w` when the top one of them is set. -/
  lemma eq_signExtend_truncate_iff {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 64) (x : BitVec 64) :
      x = BitVec.signExtend 64 (x.truncate w) ↔
        x.toNat = x.toNat % 2 ^ w +
          (if 2 ^ (w - 1) ≤ x.toNat % 2 ^ w then 2 ^ 64 - 2 ^ w else 0) := by
    have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hw
    have hlt : x.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have hw1 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [← BitVec.toNat_inj, BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
    simp only [BitVec.toNat_setWidth]
    by_cases h : 2 ^ (w - 1) ≤ x.toNat % 2 ^ w
    · simp only [h, decide_true, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [Nat.mod_eq_of_lt (by omega)]

  /-- A 64-bit value is the zero extension of its low `w` bits exactly when its number is below
      `2^w`. -/
  lemma eq_zeroExtend_truncate_iff {w : ℕ} (hw : w ≤ 64) (x : BitVec 64) :
      x = BitVec.zeroExtend 64 (x.truncate w) ↔ x.toNat < 2 ^ w := by
    have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hw
    have hlt : x.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    rw [← BitVec.toNat_inj]
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (a := x.toNat % 2 ^ w) (by omega)]
    constructor
    · intro h; rw [h]; exact hlt
    · intro h; rw [Nat.mod_eq_of_lt h]

  /-- The number of a word whose four pieces are 16-bit. -/
  lemma toNat_toBV_of_lt (a0 a1 a2 a3 : FKB)
      (h0 : a0.val < 65536) (h1 : a1.val < 65536) (h2 : a2.val < 65536) (h3 : a3.val < 65536) :
      (U64w.toBV #v[a0, a1, a2, a3]).toNat =
        a0.val + 65536 * a1.val + 4294967296 * a2.val + 281474976710656 * a3.val := by
    rw [U64w.toBV_toNat]
    simp [U64w.toNat, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3]
    ring

  /-! ### Field elements -/

  lemma bool_cases {x : FKB} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

  lemma val_le_one {x : FKB} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
    rcases h with h | h <;> subst h <;> decide

  lemma zero_of_val {x : FKB} (h : x.val = 0) : x = 0 := Fin.ext h

  /-- A 16-bit piece split into a low byte and the high byte `(x - lo) / 256`, both checked to
      be bytes, is their sum. `2122383361` is `256`'s inverse. -/
  lemma byte_split {x lo : FKB} (h_lo : lo.val < 256)
      (h_hi : ((x - lo) * 2122383361).val < 256) :
      x.val = lo.val + 256 * ((x - lo) * 2122383361).val := by
    have e : x = lo + 256 * ((x - lo) * 2122383361) := by
      rw [mul_comm, mul_assoc, show (2122383361 : FKB) * 256 = 1 from rfl]; ring
    conv_lhs => rw [e]
    rw [Fin.val_add, Fin.val_mul]
    simp only [show (256 : FKB).val = 256 from rfl]
    rw [Nat.mod_eq_of_lt (a := 256 * _) (by omega), Nat.mod_eq_of_lt (by omega)]

  /-! ### The row's flags -/

  /-- The row's eleven instruction flags, in column order. -/
  def flags [Field ExtF] (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) : List FKB :=
    let i := air.cols.values.instruction
    [i.is_lb row 0, i.is_lbu row 0, i.is_lh row 0, i.is_lhu row 0, i.is_lw row 0,
     i.is_lwu row 0, i.is_ld row 0, i.is_sb row 0, i.is_sh row 0, i.is_sw row 0, i.is_sd row 0]

  /-- The 45 constraints, one by one. -/
  lemma constraints_of_allHold
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row ∧
    constraint_3 air row ∧ constraint_4 air row ∧ constraint_5 air row ∧
    constraint_6 air row ∧ constraint_7 air row ∧
    constraint_8 air row ∧ constraint_9 air row ∧ constraint_10 air row ∧
    constraint_11 air row ∧ constraint_12 air row ∧ constraint_13 air row ∧
    constraint_14 air row ∧ constraint_15 air row ∧ constraint_16 air row ∧
    constraint_17 air row ∧ constraint_18 air row ∧ constraint_19 air row ∧
    constraint_20 air row ∧ constraint_21 air row ∧ constraint_22 air row ∧
    constraint_23 air row ∧ constraint_24 air row ∧ constraint_25 air row ∧
    constraint_26 air row ∧ constraint_27 air row ∧ constraint_28 air row ∧
    constraint_29 air row ∧ constraint_30 air row ∧ constraint_31 air row ∧
    constraint_32 air row ∧ constraint_33 air row ∧ constraint_34 air row ∧
    constraint_35 air row ∧ constraint_36 air row ∧ constraint_37 air row ∧
    constraint_38 air row ∧ constraint_39 air row ∧ constraint_40 air row ∧
    constraint_41 air row ∧ constraint_42 air row ∧ constraint_43 air row ∧
    constraint_44 air row
  := by
    simp only [allHold_iff_allHold_simplified, allHold_simplified, row_constraint_list,
      List.Forall] at h_constraints
    exact h_constraints.2

  /-- Each flag is 0 or 1 (constraints 0 to 10), and their sum is 0 or 1 (constraint 11), so the
      sum of their values is at most 1. -/
  lemma flag_vals
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    let i := air.cols.values.instruction
    (i.is_lb row 0).val + (i.is_lbu row 0).val + (i.is_lh row 0).val + (i.is_lhu row 0).val +
      (i.is_lw row 0).val + (i.is_lwu row 0).val + (i.is_ld row 0).val + (i.is_sb row 0).val +
      (i.is_sh row 0).val + (i.is_sw row 0).val + (i.is_sd row 0).val ≤ 1
  := by
    obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_0, constraint_1, constraint_2, constraint_3, constraint_4, constraint_5,
      constraint_6, constraint_7, constraint_8, constraint_9, constraint_10, constraint_11]
      at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
    have v0 := val_le_one (bool_cases c0)
    have v1 := val_le_one (bool_cases c1)
    have v2 := val_le_one (bool_cases c2)
    have v3 := val_le_one (bool_cases c3)
    have v4 := val_le_one (bool_cases c4)
    have v5 := val_le_one (bool_cases c5)
    have v6 := val_le_one (bool_cases c6)
    have v7 := val_le_one (bool_cases c7)
    have v8 := val_le_one (bool_cases c8)
    have v9 := val_le_one (bool_cases c9)
    have v10 := val_le_one (bool_cases c10)
    have vs := val_le_one (bool_cases c11)
    clear c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
    simp only [Fin.val_add] at vs
    repeat rw [Nat.mod_eq_of_lt (by omega)] at vs
    dsimp only
    omega

  /-- Eleven numbers whose sum is at most 1: all are 0, or exactly one is 1. -/
  lemma nat_one_hot (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : ℕ)
      (h : n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 ≤ 1) :
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
    simp only [List.cons.injEq, and_true]
    rcases Nat.lt_or_ge 0 n0 with h0 | h0
    · right; left; omega
    rcases Nat.lt_or_ge 0 n1 with h1 | h1
    · right; right; left; omega
    rcases Nat.lt_or_ge 0 n2 with h2 | h2
    · right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n3 with h3 | h3
    · right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n4 with h4 | h4
    · right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n5 with h5 | h5
    · right; right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n6 with h6 | h6
    · right; right; right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n7 with h7 | h7
    · right; right; right; right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n8 with h8 | h8
    · right; right; right; right; right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n9 with h9 | h9
    · right; right; right; right; right; right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n10 with h10 | h10
    · right; right; right; right; right; right; right; right; right; right; right; omega
    left; omega

  /-- On every row the flags are all 0, or exactly one is 1. -/
  lemma flag_cases
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    flags air row = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    flags air row = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    flags air row = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] ∨
    flags air row = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] ∨
    flags air row = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] ∨
    flags air row = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] ∨
    flags air row = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] ∨
    flags air row = [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] ∨
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] ∨
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] ∨
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  := by
    have h := nat_one_hot _ _ _ _ _ _ _ _ _ _ _ (flag_vals air row h_constraints)
    simp only [flags, List.cons.injEq, and_true, Fin.ext_iff, Fin.val_zero, Fin.val_one] at h ⊢
    exact h

  /-- On a row with `is_lb = 1` the other flags are 0. -/
  lemma flags_of_is_lb
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_lb row 0 = 1)
  :
    flags air row = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_lb row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lbu = 1` the other flags are 0. -/
  lemma flags_of_is_lbu
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_lbu row 0 = 1)
  :
    flags air row = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_lbu row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lh = 1` the other flags are 0. -/
  lemma flags_of_is_lh
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_lh row 0 = 1)
  :
    flags air row = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_lh row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lhu = 1` the other flags are 0. -/
  lemma flags_of_is_lhu
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_lhu row 0 = 1)
  :
    flags air row = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_lhu row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lw = 1` the other flags are 0. -/
  lemma flags_of_is_lw
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_lw row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_lw row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lwu = 1` the other flags are 0. -/
  lemma flags_of_is_lwu
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_lwu row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_lwu row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_ld = 1` the other flags are 0. -/
  lemma flags_of_is_ld
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_ld row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_ld row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sb = 1` the other flags are 0. -/
  lemma flags_of_is_sb
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_sb row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_sb row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sh = 1` the other flags are 0. -/
  lemma flags_of_is_sh
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_sh row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_sh row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sw = 1` the other flags are 0. -/
  lemma flags_of_is_sw
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_sw row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_sw row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sd = 1` the other flags are 0. -/
  lemma flags_of_is_sd
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h : air.cols.values.instruction.is_sd row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.values.instruction.is_sd row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-! ### What the buses give a real row -/

  /-- The flags' sum on a row: 1 on a real row, which receives the memory dispatch at `-1`. -/
  def is_memory [Field ExtF] (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) : FKB :=
    let i := air.cols.values.instruction
    i.is_lb row 0 + i.is_lbu row 0 + i.is_lh row 0 + i.is_lhu row 0 + i.is_lw row 0 +
      i.is_lwu row 0 + i.is_ld row 0 +
      (i.is_sb row 0 + i.is_sh row 0 + i.is_sw row 0 + i.is_sd row 0)

  /-- On a real row the address `b + c` is `addr_word_0 + 2^16 addr_word_1`, both pieces are
      16-bit, and the second is not 0. From the carry chain (constraints 12 to 15), the stack
      guard (16), the offset bits (17 to 19), the `U16Range` check of `addr_word_1` and the
      `BitRange(13)` check of the aligned low piece over 8, and the CPU's promise that `b` and
      `c` have 16-bit pieces. -/
  lemma address
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols.values
    (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat =
      (v.addr_word_0 row 0).val + 65536 * (v.addr_word_1 row 0).val ∧
    (v.addr_word_0 row 0).val < 65536 ∧ (v.addr_word_1 row 0).val < 65536 ∧
    0 < (v.addr_word_1 row 0).val
  := by
    simp only [is_memory] at h_mem
    simp [bus_row_all_ext_asm, bus_row_ext_asm, bus_row_code_range_ext_asm, bus_row,
        MemoryReadWriteChip.AbsBuses,
      MemoryBus.externals, h_mem] at h_ext_asm
    obtain ⟨ -, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, - ⟩ := h_ext_asm
    simp [bus_row_all_wf_asm, bus_row_wf_asm, bus_row_code_range_wf_asm, bus_row,
        MemoryReadWriteChip.AbsBuses, h_mem,
      RV64IM_Interactions.ByteBus.Spec] at h_wf_asm
    obtain ⟨ ⟨ h_aw1, h_br, - ⟩, - ⟩ := h_wf_asm
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, c12, c13, c14, c15, c16, c17, c18, c19, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_12, constraint_13, constraint_14, constraint_15, constraint_16,
      constraint_17, constraint_18, constraint_19] at c12 c13 c14 c15 c16 c17 c18 c19
    rw [h_mem] at c16
    dsimp only
    set b0 := air.cols.values.instruction.op_b_value_0 row 0
    set b1 := air.cols.values.instruction.op_b_value_1 row 0
    set b2 := air.cols.values.instruction.op_b_value_2 row 0
    set b3 := air.cols.values.instruction.op_b_value_3 row 0
    set c0 := air.cols.values.instruction.op_c_value_0 row 0
    set c1 := air.cols.values.instruction.op_c_value_1 row 0
    set c2 := air.cols.values.instruction.op_c_value_2 row 0
    set c3 := air.cols.values.instruction.op_c_value_3 row 0
    set a0 := air.cols.values.addr_word_0 row 0
    set a1 := air.cols.values.addr_word_1 row 0
    set o0 := air.cols.values.offset_bit_0 row 0
    set o1 := air.cols.values.offset_bit_1 row 0
    set o2 := air.cols.values.offset_bit_2 row 0
    set k1 := (0 + b0 + c0 - a0) * 2130673921 with hk1
    set k2 := (0 + b1 + c1 + k1 - a1) * 2130673921 with hk2
    set k3 := (0 + b2 + c2 + k2) * 2130673921 with hk3
    set k4 := (0 + b3 + c3 + k3) * 2130673921 with hk4
    set t := (a0 - (o0 + 2 * o1 + 4 * o2)) * 1864368129 with ht
    have inv16 : ∀ x : FKB, x * 2130673921 * 65536 = x := fun x => by
      rw [mul_assoc, show (2130673921 : FKB) * 65536 = 1 from rfl, mul_one]
    have e1 : b0 + c0 = a0 + 65536 * k1 := by rw [hk1, mul_comm 65536, inv16]; ring
    have e2 : b1 + c1 + k1 = a1 + 65536 * k2 := by rw [hk2, mul_comm 65536, inv16]; ring
    have e3 : b2 + c2 + k2 = 65536 * k3 := by rw [hk3, mul_comm 65536, inv16]; ring
    have e4 : b3 + c3 + k3 = 65536 * k4 := by rw [hk4, mul_comm 65536, inv16]; ring
    have e0 : a0 = o0 + 2 * o1 + 4 * o2 + 8 * t := by
      rw [ht, mul_comm 8, mul_assoc, show (1864368129 : FKB) * 8 = 1 from rfl]; ring
    have h_a1 : a1 ≠ 0 := by rintro h; rw [h, mul_zero] at c16; exact absurd c16 (by decide)
    have vk1 := val_le_one (bool_cases c12)
    have vk2 := val_le_one (bool_cases c13)
    have vk3 := val_le_one (bool_cases c14)
    have vk4 := val_le_one (bool_cases c15)
    have vo0 := val_le_one (bool_cases c17)
    have vo1 := val_le_one (bool_cases c18)
    have vo2 := val_le_one (bool_cases c19)
    have h_a1_pos : 0 < a1.val := Nat.pos_of_ne_zero (fun h => h_a1 (Fin.ext h))
    clear_value b0 b1 b2 b3 c0 c1 c2 c3 a0 a1 o0 o1 o2 k1 k2 k3 k4 t
    clear c12 c13 c14 c15 c16 c17 c18 c19 hk1 hk2 hk3 hk4 ht h_a1 inv16 h_mem
    have n0 := congrArg Fin.val e0
    have n1 := congrArg Fin.val e1
    have n2 := congrArg Fin.val e2
    have n3 := congrArg Fin.val e3
    have n4 := congrArg Fin.val e4
    clear e0 e1 e2 e3 e4
    simp only [Fin.val_add, Fin.val_mul] at n0 n1 n2 n3 n4
    norm_num at n0 n1 n2 n3 n4
    repeat rw [Nat.mod_eq_of_lt (by omega)] at n0
    have h_a0 : a0.val < 65536 := by omega
    repeat rw [Nat.mod_eq_of_lt (by omega)] at n1
    repeat rw [Nat.mod_eq_of_lt (by omega)] at n2
    repeat rw [Nat.mod_eq_of_lt (by omega)] at n3
    repeat rw [Nat.mod_eq_of_lt (by omega)] at n4
    refine ⟨ ?_, h_a0, h_aw1, h_a1_pos ⟩
    rw [BitVec.toNat_add, toNat_toBV_of_lt _ _ _ _ hb0 hb1 hb2 hb3,
      toNat_toBV_of_lt _ _ _ _ hc0 hc1 hc2 hc3]
    omega

  /-- What the buses give a real row. From the CPU, as the sender of the memory dispatch
      (`MemoryBus.externals`): `b` and `c` have 16-bit pieces, so does a store's `a`, and
      `a = 0` when `op_a_0 ≠ 0`. From the memory argument (`StateBusEntry`): the double word
      read has 16-bit pieces. From the byte table (`ByteBus.Spec`), for the checks the row's
      flags send: the sign-bit operand and the two byte splits are in range. The byte table's
      checks of the address are used by `address` and `aligned_address`. -/
  lemma bus_facts
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols.values
    let i := v.instruction
    ((i.op_b_value_0 row 0).val < 65536 ∧ (i.op_b_value_1 row 0).val < 65536 ∧
      (i.op_b_value_2 row 0).val < 65536 ∧ (i.op_b_value_3 row 0).val < 65536) ∧
    ((i.op_c_value_0 row 0).val < 65536 ∧ (i.op_c_value_1 row 0).val < 65536 ∧
      (i.op_c_value_2 row 0).val < 65536 ∧ (i.op_c_value_3 row 0).val < 65536) ∧
    (i.is_sb row 0 + i.is_sh row 0 + i.is_sw row 0 + i.is_sd row 0 = 1 →
      (i.op_a_value_0 row 0).val < 65536 ∧ (i.op_a_value_1 row 0).val < 65536 ∧
      (i.op_a_value_2 row 0).val < 65536 ∧ (i.op_a_value_3 row 0).val < 65536) ∧
    (i.op_a_0 row 0 ≠ 0 →
      i.op_a_value_0 row 0 = 0 ∧ i.op_a_value_1 row 0 = 0 ∧
      i.op_a_value_2 row 0 = 0 ∧ i.op_a_value_3 row 0 = 0) ∧
    ((v.memory_access.prev_value_0 row 0).val < 65536 ∧
      (v.memory_access.prev_value_1 row 0).val < 65536 ∧
      (v.memory_access.prev_value_2 row 0).val < 65536 ∧
      (v.memory_access.prev_value_3 row 0).val < 65536) ∧
    (i.is_lh row 0 + i.is_lw row 0 + i.is_lb row 0 = 1 →
      (2 * v.lhw_val row 0 - v.msb row 0 * 65536).val < 65536) ∧
    (i.is_sb row 0 = 1 →
      (v.register_low_byte row 0).val < 256 ∧
      ((i.op_a_value_0 row 0 - v.register_low_byte row 0) * 2122383361).val < 256) ∧
    (i.is_sb row 0 + i.is_lb row 0 + i.is_lbu row 0 = 1 →
      (v.mem_limb_low_byte row 0).val < 256 ∧
      ((v.selected_limb row 0 - v.mem_limb_low_byte row 0) * 2122383361).val < 256)
  := by
    have h_cases := flag_cases air row h_constraints
    simp only [is_memory] at h_mem
    simp [bus_row_all_ext_asm, bus_row_ext_asm, bus_row_code_range_ext_asm, bus_row,
      MemoryReadWriteChip.AbsBuses, MemoryBus.externals, h_mem] at h_ext_asm
    obtain ⟨ -, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, h_store, h_x0 ⟩ := h_ext_asm
    simp [bus_row_all_wf_asm, bus_row_wf_asm, bus_row_code_range_wf_asm, bus_row,
      MemoryReadWriteChip.AbsBuses, h_mem, RV64IM_Interactions.ByteBus.Spec] at h_wf_asm
    obtain ⟨ ⟨ -, -, -, -, h_msb, h_reg, h_mem_split, -, -, hp0, hp1, hp2, hp3 ⟩, - ⟩ :=
      h_wf_asm
    refine ⟨ ⟨ hb0, hb1, hb2, hb3 ⟩, ⟨ hc0, hc1, hc2, hc3 ⟩, fun hs => h_store ?_, h_x0,
      ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, h_reg, h_mem_split ⟩
    simp only [flags] at h_cases
    rcases h_cases with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
      simp [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, MemoryBus.isStore] at hs ⊢

  /-- On a real row the address `b + c` lies in `[2^16, 2^32)`. -/
  lemma address_bounds
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols.values
    let addr := (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat
    65536 ≤ addr ∧ addr < 2 ^ 32
  := by
    obtain ⟨ h_addr, h_a0, h_a1, h_a1_pos ⟩ :=
      address air row h_ext_asm h_wf_asm h_constraints h_mem
    dsimp only at h_addr ⊢
    rw [h_addr]
    omega

  /-- `selected_limb` is the piece of the double word read that `offset_bit_1` and
      `offset_bit_2` select (constraints 18, 19 and 24). -/
  lemma selected_limb_cases
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    let v := air.cols.values
    (v.offset_bit_1 row 0 = 0 ∧ v.offset_bit_2 row 0 = 0 ∧
      v.selected_limb row 0 = v.memory_access.prev_value_0 row 0) ∨
    (v.offset_bit_1 row 0 = 1 ∧ v.offset_bit_2 row 0 = 0 ∧
      v.selected_limb row 0 = v.memory_access.prev_value_1 row 0) ∨
    (v.offset_bit_1 row 0 = 0 ∧ v.offset_bit_2 row 0 = 1 ∧
      v.selected_limb row 0 = v.memory_access.prev_value_2 row 0) ∨
    (v.offset_bit_1 row 0 = 1 ∧ v.offset_bit_2 row 0 = 1 ∧
      v.selected_limb row 0 = v.memory_access.prev_value_3 row 0)
  := by
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c18, c19, -, -, -, -,
      c24, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_18, constraint_19, constraint_24, sub_eq_zero] at c18 c19 c24
    dsimp only
    rcases bool_cases c18 with h1 | h1 <;> rcases bool_cases c19 with h2 | h2 <;>
      rw [h1, h2] at c24 <;> norm_num at c24 <;> simp [h1, h2, c24]

  /-- The sign-bit check: with `x` 16-bit and `msb` 0 or 1, `2 x - 2^16 msb` is 16-bit exactly
      when `msb` is bit 15 of `x`. -/
  lemma msb_check {x msb : FKB} (h_x : x.val < 65536) (h_msb : msb = 0 ∨ msb = 1)
      (h : (2 * x - msb * 65536).val < 65536) :
      (msb = 0 ∧ x.val < 32768) ∨ (msb = 1 ∧ 32768 ≤ x.val) := by
    rcases h_msb with rfl | rfl
    · left; refine ⟨ rfl, ?_ ⟩
      simp only [zero_mul, sub_zero, Fin.val_mul] at h
      norm_num at h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · right; refine ⟨ rfl, ?_ ⟩
      by_contra hlt
      rw [Fin.sub_def] at h
      simp only [Fin.val_mul, one_mul] at h
      norm_num at h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega

  lemma val_add_of_lt {x y : FKB} (h : x.val + y.val < 2130706433) :
      (x + y).val = x.val + y.val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt h]

  lemma val_mul_of_lt {x y : FKB} (h : x.val * y.val < 2130706433) :
      (x * y).val = x.val * y.val := by
    rw [Fin.val_mul, Nat.mod_eq_of_lt h]

  /-- On a real row the double word the row reads and writes back starts at `b + c` with its three
      low bits cleared, and the three offset bits are those low bits: the memory access's address
      `[addr_word_0 - offset, addr_word_1, 0]` (`riscv_memory/read_write/constraints.rs:292-301,
      333-343` at v3.2.0) is the aligned form of the address the memory dispatch names, and its
      first two pieces (the third is 0) are below `2^16`. From `address`, the offset bits
      (constraints 17 to 19), the `BitRange(13)` check of the aligned low piece over 8
      (`riscv_memory/read_write/constraints.rs:303-309` at v3.2.0) and the `U16Range` check of
      `addr_word_1` (`riscv_memory/read_write/constraints.rs:259-266` at v3.2.0). -/
  lemma aligned_address
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols.values
    let addr := (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat
    let offset := v.offset_bit_0 row 0 + 2 * v.offset_bit_1 row 0 + 4 * v.offset_bit_2 row 0
    offset.val = addr % 8 ∧
    (v.addr_word_0 row 0 - offset).val < 65536 ∧ (v.addr_word_1 row 0).val < 65536 ∧
    (v.addr_word_0 row 0 - offset).val + 65536 * (v.addr_word_1 row 0).val = addr - addr % 8
  := by
    obtain ⟨ h_addr, -, -, - ⟩ := address air row h_ext_asm h_wf_asm h_constraints h_mem
    simp only [is_memory] at h_mem
    simp [bus_row_all_wf_asm, bus_row_wf_asm, bus_row_code_range_wf_asm, bus_row,
      MemoryReadWriteChip.AbsBuses, h_mem, RV64IM_Interactions.ByteBus.Spec] at h_wf_asm
    obtain ⟨ ⟨ h_aw1, h_br, - ⟩, - ⟩ := h_wf_asm
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_17, constraint_18, constraint_19] at c17 c18 c19
    dsimp only at h_addr ⊢
    rw [h_addr]
    set a0 := air.cols.values.addr_word_0 row 0
    set off := air.cols.values.offset_bit_0 row 0 + 2 * air.cols.values.offset_bit_1 row 0 +
      4 * air.cols.values.offset_bit_2 row 0 with h_off
    set t := (a0 - off) * 1864368129 with ht
    have e : a0 - off = 8 * t := by
      rw [ht, mul_comm 8, mul_assoc, show (1864368129 : FKB) * 8 = 1 from rfl, mul_one]
    have v0 := val_le_one (bool_cases c17)
    have v1 := val_le_one (bool_cases c18)
    have v2 := val_le_one (bool_cases c19)
    have h_off_val : off.val = (air.cols.values.offset_bit_0 row 0).val +
        2 * (air.cols.values.offset_bit_1 row 0).val +
        4 * (air.cols.values.offset_bit_2 row 0).val := by
      have h2 : (2 * air.cols.values.offset_bit_1 row 0).val =
          2 * (air.cols.values.offset_bit_1 row 0).val := by
        rw [val_mul_of_lt (by rw [show (2 : FKB).val = 2 from rfl]; omega)]; rfl
      have h4 : (4 * air.cols.values.offset_bit_2 row 0).val =
          4 * (air.cols.values.offset_bit_2 row 0).val := by
        rw [val_mul_of_lt (by rw [show (4 : FKB).val = 4 from rfl]; omega)]; rfl
      rw [h_off, val_add_of_lt (by rw [val_add_of_lt (by omega), h2, h4]; omega),
        val_add_of_lt (by omega), h2, h4]
    have h_t : (a0 - off).val = 8 * t.val := by
      rw [e, val_mul_of_lt (by rw [show (8 : FKB).val = 8 from rfl]; omega)]; rfl
    have h_a0_val : a0.val = off.val + 8 * t.val := by
      have e2 : a0 = off + 8 * t := by rw [← e]; ring
      have h8 : (8 * t).val = 8 * t.val := by
        rw [val_mul_of_lt (by rw [show (8 : FKB).val = 8 from rfl]; omega)]; rfl
      conv_lhs => rw [e2]
      rw [val_add_of_lt (by omega), h8]
    clear_value a0 off t
    clear e ht h_off c17 c18 c19 h_mem
    omega

  /-- A row whose `op_a_0` is not 0 and whose address lies in `[2^16, 2^32)`: the CPU sends
      `a = 0` (`MemoryBus.externals`), and the promise asks nothing more. -/
  lemma spec_of_x0 {k a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 op : FKB}
      (h_op : op ≠ 0) (h_a : a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0)
      (h_addr : 65536 ≤ (U64w.toBV #v[b0, b1, b2, b3] + U64w.toBV #v[c0, c1, c2, c3]).toNat ∧
        (U64w.toBV #v[b0, b1, b2, b3] + U64w.toBV #v[c0, c1, c2, c3]).toNat < 2 ^ 32) :
      MemoryBus.Spec k a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 op := by
    obtain ⟨ rfl, rfl, rfl, rfl ⟩ := h_a
    exact ⟨ fun _ => by decide, h_addr.1, h_addr.2, fun _ h => absurd h h_op,
      fun _ h => absurd h h_op, fun _ h => absurd h h_op, fun _ h => absurd h h_op,
      fun _ h => absurd h h_op, fun _ h => absurd h h_op ⟩

  /-- A store whose address lies in `[2^16, 2^32)`: the promise's other clauses are about
      loads. -/
  lemma spec_of_store {k a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 op : FKB}
      (hk : k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 47)
      (h_addr : 65536 ≤ (U64w.toBV #v[b0, b1, b2, b3] + U64w.toBV #v[c0, c1, c2, c3]).toNat ∧
        (U64w.toBV #v[b0, b1, b2, b3] + U64w.toBV #v[c0, c1, c2, c3]).toNat < 2 ^ 32) :
      MemoryBus.Spec k a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 op := by
    rcases hk with rfl | rfl | rfl | rfl <;>
      exact ⟨ fun h => absurd h (by decide), h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide) ⟩

  /-! ### The Memory promise, one opcode at a time -/

  /-- On a load of a byte, sign-extended row (`is_lb = 1`), the memory dispatch the row receives
      meets the Memory
      promise with opcode 10. -/
  theorem spec_LB
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lb : air.cols.values.instruction.is_lb row 0 = 1)
  :
    MemoryBus.Spec 10
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lb air row h_constraints h_is_lb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    have h_sel : (air.cols.values.selected_limb row 0).val < 65536 := by
      rcases selected_limb_cases air row h_constraints with
        ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ <;>
        rw [h] <;> assumption
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, c25, c26, c27, c28, c29, c30, c31, -, c33, c34, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_19, constraint_25, constraint_26, constraint_27,
      constraint_28, constraint_29, constraint_30, constraint_31, constraint_33, constraint_34,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c17 c19 c25 c26 c27 c28 c29 c30 c31 c33 c34
    obtain ⟨ h_lo, h_hi ⟩ := h_split (by simp [f0, f1, f7])
    have h_sb : (air.cols.values.selected_byte row 0).val < 256 := by
      rcases c17 with o | o <;> rw [o] at c25 <;> simp at c25 <;> rw [c25] <;> assumption
    have h_lhw : (air.cols.values.lhw_val row 0).val =
        256 * (air.cols.values.selected_byte row 0).val := by
      rw [c30, val_mul_of_lt (by simp; omega)]; rfl
    rcases msb_check (by omega) c31 (h_msb (by simp [f0, f2, f4])) with
        ⟨ hm, hl ⟩ | ⟨ hm, hl ⟩ <;>
      rw [hm] at c26 c27 c28 c29 <;> norm_num at c26 c27 c28 c29 <;> rw [c26, c27, c28, c29]
    · refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun _ _ => ?_, fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
      · exact ⟨ by omega, by decide, by decide, by decide ⟩
      · rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
          toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
        norm_num
        rw [if_neg (by omega)]
        omega
    · have hv : (air.cols.values.selected_byte row 0 + 65280).val =
          (air.cols.values.selected_byte row 0).val + 65280 := by
        rw [val_add_of_lt (by simp; omega)]; rfl
      refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun _ _ => ?_, fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
      · exact ⟨ by omega, by decide, by decide, by decide ⟩
      · rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
          toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide), hv]
        norm_num
        rw [if_pos (by omega)]
        omega

  /-- On a load of a byte, zero-extended row (`is_lbu = 1`), the memory dispatch the row receives
      meets the Memory
      promise with opcode 13. -/
  theorem spec_LBU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lbu : air.cols.values.instruction.is_lbu row 0 = 1)
  :
    MemoryBus.Spec 13
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lbu air row h_constraints h_is_lbu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    have h_sel : (air.cols.values.selected_limb row 0).val < 65536 := by
      rcases selected_limb_cases air row h_constraints with
        ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ <;>
        rw [h] <;> assumption
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, c25, c26, c27, c28, c29, c30, c31, -, c33, c34, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_19, constraint_25, constraint_26, constraint_27,
      constraint_28, constraint_29, constraint_30, constraint_31, constraint_33, constraint_34,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c17 c19 c25 c26 c27 c28 c29 c30 c31 c33 c34
    obtain ⟨ h_lo, h_hi ⟩ := h_split (by simp [f0, f1, f7])
    have h_sb : (air.cols.values.selected_byte row 0).val < 256 := by
      rcases c17 with o | o <;> rw [o] at c25 <;> simp at c25 <;> rw [c25] <;> assumption
    rw [c26, c27, c28, c29]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ _ => ?_,
        fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    · exact ⟨ by omega, by decide, by decide, by decide ⟩
    · rw [eq_zeroExtend_truncate_iff (by norm_num),
        toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
      norm_num
      omega

  /-- On a load of a half word, sign-extended row (`is_lh = 1`), the memory dispatch the row
      receives meets the Memory
      promise with opcode 11. -/
  theorem spec_LH
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lh : air.cols.values.instruction.is_lh row 0 = 1)
  :
    MemoryBus.Spec 11
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lh air row h_constraints h_is_lh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    have h_sel : (air.cols.values.selected_limb row 0).val < 65536 := by
      rcases selected_limb_cases air row h_constraints with
        ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ <;>
        rw [h] <;> assumption
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, c25, c26, c27, c28, c29, c30, c31, -, c33, c34, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_19, constraint_25, constraint_26, constraint_27,
      constraint_28, constraint_29, constraint_30, constraint_31, constraint_33, constraint_34,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c17 c19 c25 c26 c27 c28 c29 c30 c31 c33 c34
    rw [← c33] at h_sel
    rcases msb_check h_sel c31 (h_msb (by simp [f0, f2, f4])) with
        ⟨ hm, hl ⟩ | ⟨ hm, hl ⟩ <;>
      rw [hm] at c27 c28 c29 <;> norm_num at c27 c28 c29 <;> rw [c26, ← c33, c27, c28, c29]
    all_goals refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
      fun _ _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    all_goals first
      | exact ⟨ by omega, by decide, by decide, by decide ⟩
      | (rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
            toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
         norm_num
         first | (rw [if_neg (by omega)]; omega) | (rw [if_pos (by omega)]; omega))

  /-- On a load of a half word, zero-extended row (`is_lhu = 1`), the memory dispatch the row
      receives meets the Memory
      promise with opcode 14. -/
  theorem spec_LHU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lhu : air.cols.values.instruction.is_lhu row 0 = 1)
  :
    MemoryBus.Spec 14
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lhu air row h_constraints h_is_lhu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    have h_sel : (air.cols.values.selected_limb row 0).val < 65536 := by
      rcases selected_limb_cases air row h_constraints with
        ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ <;>
        rw [h] <;> assumption
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, c25, c26, c27, c28, c29, c30, c31, -, c33, c34, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_19, constraint_25, constraint_26, constraint_27,
      constraint_28, constraint_29, constraint_30, constraint_31, constraint_33, constraint_34,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c17 c19 c25 c26 c27 c28 c29 c30 c31 c33 c34
    rw [c26, c27, c28, c29]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun _ _ => ?_, fun h => absurd h (by decide) ⟩
    · exact ⟨ by omega, by decide, by decide, by decide ⟩
    · rw [eq_zeroExtend_truncate_iff (by norm_num),
        toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
      norm_num
      omega

  /-- On a load of a word, sign-extended row (`is_lw = 1`), the memory dispatch the row receives
      meets the Memory
      promise with opcode 12. -/
  theorem spec_LW
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lw : air.cols.values.instruction.is_lw row 0 = 1)
  :
    MemoryBus.Spec 12
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lw air row h_constraints h_is_lw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    have h_sel : (air.cols.values.selected_limb row 0).val < 65536 := by
      rcases selected_limb_cases air row h_constraints with
        ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ <;>
        rw [h] <;> assumption
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, c25, c26, c27, c28, c29, c30, c31, -, c33, c34, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_19, constraint_25, constraint_26, constraint_27,
      constraint_28, constraint_29, constraint_30, constraint_31, constraint_33, constraint_34,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c17 c19 c25 c26 c27 c28 c29 c30 c31 c33 c34
    have h_lhw : (air.cols.values.lhw_val row 0).val < 65536 := by
      rcases c19 with o | o <;> rw [o] at c34 <;> simp at c34 <;> rw [c34] <;> assumption
    rcases msb_check h_lhw c31 (h_msb (by simp [f0, f2, f4])) with
        ⟨ hm, hl ⟩ | ⟨ hm, hl ⟩ <;>
      rw [hm] at c28 c29 <;> norm_num at c28 c29 <;> rw [c26, c27, c28, c29]
    all_goals refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun _ _ => ?_, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    all_goals first
      | exact ⟨ by omega, by omega, by decide, by decide ⟩
      | (rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
            toNat_toBV_of_lt _ _ _ _ (by omega) (by omega) (by decide) (by decide)]
         norm_num
         first | (rw [if_neg (by omega)]; omega) | (rw [if_pos (by omega)]; omega))

  /-- On a load of a word, zero-extended row (`is_lwu = 1`), the memory dispatch the row receives
      meets the Memory
      promise with opcode 45. -/
  theorem spec_LWU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lwu : air.cols.values.instruction.is_lwu row 0 = 1)
  :
    MemoryBus.Spec 45
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lwu air row h_constraints h_is_lwu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    have h_sel : (air.cols.values.selected_limb row 0).val < 65536 := by
      rcases selected_limb_cases air row h_constraints with
        ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ | ⟨ -, -, h ⟩ <;>
        rw [h] <;> assumption
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, c25, c26, c27, c28, c29, c30, c31, -, c33, c34, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_19, constraint_25, constraint_26, constraint_27,
      constraint_28, constraint_29, constraint_30, constraint_31, constraint_33, constraint_34,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c17 c19 c25 c26 c27 c28 c29 c30 c31 c33 c34
    have h_lhw : (air.cols.values.lhw_val row 0).val < 65536 := by
      rcases c19 with o | o <;> rw [o] at c34 <;> simp at c34 <;> rw [c34] <;> assumption
    rw [c26, c27, c28, c29]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun _ _ => ?_ ⟩
    · exact ⟨ by omega, by omega, by decide, by decide ⟩
    · rw [eq_zeroExtend_truncate_iff (by norm_num),
        toNat_toBV_of_lt _ _ _ _ (by omega) (by omega) (by decide) (by decide)]
      norm_num
      omega

  /-- On a load of a double word row (`is_ld = 1`), the memory dispatch the row receives meets the
      Memory
      promise with opcode 46. -/
  theorem spec_LD
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_ld : air.cols.values.instruction.is_ld row 0 = 1)
  :
    MemoryBus.Spec 46
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_ld air row h_constraints h_is_ld
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.values.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, c26, c27, c28, c29, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_26, constraint_27, constraint_28, constraint_29,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c26 c27 c28 c29
    rw [c26, c27, c28, c29]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    exact ⟨ hp0, hp1, hp2, hp3 ⟩

  /-- On a store of a byte row (`is_sb = 1`), the memory dispatch the row receives meets the Memory
      promise with opcode 15. -/
  theorem spec_SB
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sb : air.cols.values.instruction.is_sb row 0 = 1)
  :
    MemoryBus.Spec 15
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sb air row h_constraints h_is_sb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-- On a store of a half word row (`is_sh = 1`), the memory dispatch the row receives meets the
      Memory
      promise with opcode 16. -/
  theorem spec_SH
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sh : air.cols.values.instruction.is_sh row 0 = 1)
  :
    MemoryBus.Spec 16
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sh air row h_constraints h_is_sh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-- On a store of a word row (`is_sw = 1`), the memory dispatch the row receives meets the Memory
      promise with opcode 17. -/
  theorem spec_SW
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sw : air.cols.values.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec 17
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sw air row h_constraints h_is_sw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-- On a store of a double word row (`is_sd = 1`), the memory dispatch the row receives meets the
      Memory
      promise with opcode 47. -/
  theorem spec_SD
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sd : air.cols.values.instruction.is_sd row 0 = 1)
  :
    MemoryBus.Spec 47
      (air.cols.values.instruction.op_a_value_0 row 0)
      (air.cols.values.instruction.op_a_value_1 row 0)
      (air.cols.values.instruction.op_a_value_2 row 0)
      (air.cols.values.instruction.op_a_value_3 row 0)
      (air.cols.values.instruction.op_b_value_0 row 0)
      (air.cols.values.instruction.op_b_value_1 row 0)
      (air.cols.values.instruction.op_b_value_2 row 0)
      (air.cols.values.instruction.op_b_value_3 row 0)
      (air.cols.values.instruction.op_c_value_0 row 0)
      (air.cols.values.instruction.op_c_value_1 row 0)
      (air.cols.values.instruction.op_c_value_2 row 0)
      (air.cols.values.instruction.op_c_value_3 row 0)
      (air.cols.values.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sd air row h_constraints h_is_sd
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-! ### The double word written back -/

  /-- A byte store's patched piece is 16-bit: with `offset_bit_0 = 0` it is the register's byte
      under the piece's high byte, otherwise the register's byte over the piece's low byte. -/
  lemma byte_store_lt {sel lo reg o0 x : FKB} (h_o0 : o0 = 0 ∨ o0 = 1)
      (h_lo : lo.val < 256) (h_hi : ((sel - lo) * 2122383361).val < 256) (h_reg : reg.val < 256)
      (hx : x = sel + ((1 - o0) * (reg - lo) + o0 * (reg * 256 - sel + lo))) :
      x.val < 65536 := by
    have inv : (2122383361 : FKB) * 256 = 1 := rfl
    have v256 : (256 : FKB).val = 256 := rfl
    rcases h_o0 with rfl | rfl
    · have e : x = reg + 256 * ((sel - lo) * 2122383361) := by
        rw [hx, mul_comm 256, mul_assoc, inv]; ring
      have hm : (256 * ((sel - lo) * 2122383361)).val = 256 * ((sel - lo) * 2122383361).val := by
        rw [val_mul_of_lt (by rw [v256]; omega), v256]
      rw [e, val_add_of_lt (by omega), hm]
      omega
    · have e : x = lo + reg * 256 := by rw [hx]; ring
      have hm : (reg * 256).val = reg.val * 256 := by
        rw [val_mul_of_lt (by rw [v256]; omega), v256]
      rw [e, val_add_of_lt (by omega), hm]
      omega

  /-- On a real row the double word written back has 16-bit pieces: a load writes back what it
      read, `SD` writes `a`, `SW` puts `a`'s low half over the selected half, `SH` puts `a`'s low
      piece over the selected piece, and `SB` puts the register's byte into it (constraints 36
      to 40). -/
  lemma write_value_lt
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols.values
    (v.memory_access.access.value_0 row 0).val < 65536 ∧
    (v.memory_access.access.value_1 row 0).val < 65536 ∧
    (v.memory_access.access.value_2 row 0).val < 65536 ∧
    (v.memory_access.access.value_3 row 0).val < 65536
  := by
    obtain ⟨ -, -, h_store, -, ⟨ hp0, hp1, hp2, hp3 ⟩, -, h_reg, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_sel := selected_limb_cases air row h_constraints
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, c19, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, c36, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_17, constraint_19, constraint_36, constraint_37, constraint_38,
      constraint_39, constraint_40, sub_eq_zero] at c17 c19 c36 c37 c38 c39 c40
    replace c17 := bool_cases c17
    replace c19 := bool_cases c19
    dsimp only at h_sel ⊢
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [flags, List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
      simp only [f7, f8, f9, f10] at c36 c37 c38 c39 c40 h_store
    all_goals simp only [f0, f7, f1] at h_reg h_split
    · simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at h_mem
    iterate 7
      · norm_num at c36
        rw [c36] at c37 c38 c39 c40
        norm_num at c37 c38 c39 c40
        rw [c37, c38, c39, c40]
        exact ⟨ hp0, hp1, hp2, hp3 ⟩
    · obtain ⟨ h_lo, h_hi ⟩ := h_split (by norm_num)
      obtain ⟨ h_r, - ⟩ := h_reg (by norm_num)
      norm_num at c36 c37 c38 c39 c40
      rcases h_sel with
          ⟨ o1, o2, hs ⟩ | ⟨ o1, o2, hs ⟩ | ⟨ o1, o2, hs ⟩ | ⟨ o1, o2, hs ⟩ <;>
        rw [o1, o2] at c37 c38 c39 c40 <;> norm_num at c37 c38 c39 c40 <;>
        rw [c37, c38, c39, c40] <;>
        refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;>
        first
          | assumption
          | exact byte_store_lt c17 h_lo h_hi h_r (by rw [c36, hs])
    · obtain ⟨ ha0, -, -, - ⟩ := h_store (by norm_num)
      norm_num at c36 c37 c38 c39 c40
      rcases h_sel with
          ⟨ o1, o2, hs ⟩ | ⟨ o1, o2, hs ⟩ | ⟨ o1, o2, hs ⟩ | ⟨ o1, o2, hs ⟩ <;>
        rw [o1, o2] at c37 c38 c39 c40 <;> norm_num at c37 c38 c39 c40 <;>
        rw [c37, c38, c39, c40] <;>
        refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;>
        first
          | assumption
          | (rw [c36, ← hs]; simpa using ha0)
    · obtain ⟨ ha0, ha1, -, - ⟩ := h_store (by norm_num)
      norm_num at c36
      rw [c36] at c37 c38 c39 c40
      rcases c19 with o2 | o2 <;> rw [o2] at c37 c38 c39 c40 <;> norm_num at c37 c38 c39 c40 <;>
        rw [c37, c38, c39, c40] <;> exact ⟨ by assumption, by assumption, by assumption,
          by assumption ⟩
    · obtain ⟨ ha0, ha1, ha2, ha3 ⟩ := h_store (by norm_num)
      norm_num at c36
      rw [c36] at c37 c38 c39 c40
      norm_num at c37 c38 c39 c40
      rw [c37, c38, c39, c40]
      exact ⟨ ha0, ha1, ha2, ha3 ⟩

  /-! ### The row's duties as a receiver and as a sender -/

  /-- The row owes the Memory promise to the memory dispatch it receives at `-1`, and 16-bit
      pieces to the double word it writes back at `-1`; every other message it sends at
      `+is_memory`, `+is_store` or another sum of flags, which is never `-1`. -/
  theorem wf_asrt
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    bus_row_all_wf_asrt (bus_row air row)
  := by
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      have h' := h <;>
      simp only [flags, List.cons.injEq, and_true] at h' <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h'
    · simp [bus_row_all_wf_asrt, bus_row_wf_asrt, bus_row_code_range_wf_asrt, bus_row,
        MemoryReadWriteChip.AbsBuses, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    all_goals
      have h_mem : is_memory air row = 1 := by
        simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
      have hv := write_value_lt air row h_ext_asm h_wf_asm h_constraints h_mem
      simp [bus_row_all_wf_asrt, bus_row_wf_asrt, bus_row_code_range_wf_asrt, bus_row,
        MemoryReadWriteChip.AbsBuses, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
      refine ⟨ hv, ?_ ⟩
    · exact spec_LB air row h_ext_asm h_wf_asm h_constraints f0
    · exact spec_LBU air row h_ext_asm h_wf_asm h_constraints f1
    · exact spec_LH air row h_ext_asm h_wf_asm h_constraints f2
    · exact spec_LHU air row h_ext_asm h_wf_asm h_constraints f3
    · exact spec_LW air row h_ext_asm h_wf_asm h_constraints f4
    · exact spec_LWU air row h_ext_asm h_wf_asm h_constraints f5
    · exact spec_LD air row h_ext_asm h_wf_asm h_constraints f6
    · exact spec_SB air row h_ext_asm h_wf_asm h_constraints f7
    · exact spec_SH air row h_ext_asm h_wf_asm h_constraints f8
    · exact spec_SW air row h_ext_asm h_wf_asm h_constraints f9
    · exact spec_SD air row h_ext_asm h_wf_asm h_constraints f10

  /-- The row asserts nothing to the tables it looks up, and the memory dispatch it receives is
      never at `+1`. -/
  theorem ext_asrt
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (_h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    bus_row_all_ext_asrt (bus_row air row)
  := by
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [flags, List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
      simp [bus_row_all_ext_asrt, bus_row_ext_asrt, bus_row_code_range_ext_asrt, bus_row,
        MemoryReadWriteChip.AbsBuses, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]

  /-! ### A store misses the code range -/

  /-- On a store row the bytes written, `[addr, addr + store_width)` with `addr = b + c`, miss
      the code range `[code_start, code_end)` the row looks up: they end at or below its start,
      or start at or above its end. The `code_range` gadget proves it
      (`CodeRangeGadget.Spec.gadget_spec`); the chip hands it `addr_word` and `store_width`
      (`riscv_memory/read_write/constraints.rs:94-108` at v3.2.0) and supplies its premises: the
      address's two pieces are 16-bit and equal `b + c` (`address`), and the width is at most 8.
      As in the gadget, the range is the one in the row's columns: the Program table's promise
      (`CodeRangeBus.Spec`) does not yet say it is the program's code range. -/
  theorem store_misses_code_range
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_store :
      air.cols.values.instruction.is_sb row 0 + air.cols.values.instruction.is_sh row 0 +
        air.cols.values.instruction.is_sw row 0 + air.cols.values.instruction.is_sd row 0 = 1)
  :
    let v := air.cols.values
    let addr := (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat
    addr + (v.store_width row 0).val ≤
        (v.code_range.code_start_0 row 0).val + 65536 * (v.code_range.code_start_1 row 0).val ∨
      (v.code_range.code_end_0 row 0).val + 65536 * (v.code_range.code_end_1 row 0).val ≤ addr
  := by
    have h_row : is_memory air row = 1 ∧ (air.cols.values.store_width row 0).val ≤ 8 := by
      rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp only [flags, List.cons.injEq, and_true] at h <;>
        obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
        simp [is_memory, Valid_MemoryChipValueCols.store_width, f0, f1, f2, f3, f4, f5, f6, f7,
          f8, f9, f10] at h_is_store ⊢
    obtain ⟨ h_mem, h_width ⟩ := h_row
    obtain ⟨ h_addr, h_a0, h_a1, - ⟩ := address air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_gadget := CodeRangeGadget.Spec.gadget_spec _ _ _ _ _ _ _ _ _ _ _ _
      (bus_row_all_wf_asm_code_range air row h_wf_asm) (allHold_code_range air row h_constraints)
      h_is_store ⟨ h_a0, h_a1 ⟩ (by omega)
    dsimp only at h_addr ⊢
    rw [h_addr]
    exact h_gadget

end MemoryReadWriteChip.Spec
