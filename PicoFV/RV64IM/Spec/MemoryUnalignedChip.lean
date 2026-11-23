import PicoFV.RV64IM.Spec.CodeRangeGadget
import PicoFV.RV64IM.Constraints.MemoryUnalignedChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryUnalignedChip — the Memory promise

What the chip proves about each row (`MemoryUnalignedChip::eval`,
`vm/src/chips/chips/riscv_memory/unaligned/constraints.rs`, Pico v3.1.6
`6aa644efeff9ddbec6beb538200f98f2a70f5d8e`; constraints and messages in
`Constraints/MemoryUnalignedChip.lean`).

- `spec_LB` … `spec_SD`, one per opcode: on a row whose flag for that instruction is 1, the
  memory dispatch the row receives from the CPU chip meets the Memory promise
  `V3.MemoryBus.Spec` (`RVSail/BusesV3.lean`): a load's value has 16-bit pieces, the address
  `b + c` lies in `[2^16, 2^32)`, and a load's value is the sign or zero extension its opcode
  names when `op_a_0 = 0`.
- `wf_asrt`: every message the row receives at `-1` meets its promise: the memory dispatch the
  Memory promise, and each dword written back 16-bit pieces (`StateBusEntry`).
- `ext_asrt`: the row asserts nothing to the tables it looks up.
- `aligned_address`: the dword the row reads first is the one holding the access's first byte,
  and on a row that crosses the second is the next one.
- `store_misses_code_range`: on a store row the bytes written miss the code range the row looks
  up, through the `code_range` gadget (`CodeRangeGadget.Spec.gadget_spec`).

Each theorem assumes the row's constraints (`allHold`) and what its messages are promised
(`bus_row_all_ext_asm`, `bus_row_all_wf_asm`): from the CPU chip, as the sender of the memory
dispatch, that `b` and `c` have 16-bit pieces, so does a store's `a`, and `a = 0` when
`op_a_0 ≠ 0` (`MemoryBus.externals`); from the memory argument, that each dword read has 16-bit
pieces; from the byte table, the range checks; from the Program table, that the code range has
16-bit pieces. The per-opcode theorems also take the row's flag.

A load reads the bytes from the address on: `seen_byte` and the pieces `seen_0` to `seen_3`,
each the offset's selection from the sixteen bytes of the two dwords (constraints 32 to 36).
The first dword's bytes are range-checked on every real row, the second dword's on a row that
crosses into it (`riscv_memory/unaligned/constraints.rs:188-199`). A load's value uses only the
bytes its width reads, and those lie in the second dword only when the row crosses
(constraint 26), so they are checked; the other `seen` pieces meet zero coefficients. The proofs
split on the one-hot offset (constraints 17 to 25) where they need the bytes.

Nothing here says which memory a load reads or a store writes: the Memory promise does not ask
it.
-/

namespace MemoryUnalignedChip.Interpretations

  open RV64IM_Interactions.V3
  open MemoryUnalignedChip.ConstraintsAndBuses
  open MemoryUnalignedChip.Interactions

  /-- The row's columns satisfy the `code_range` gadget's constraints, with the inputs the chip
      hands it: `is_store`, `addr_word` and `store_width`
      (`riscv_memory/unaligned/constraints.rs:311-322`). -/
  lemma allHold_code_range
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
  :
    let v := air.cols
    CodeRangeGadget.AbsConstraints
      (v.instruction.is_sb row 0 + v.instruction.is_sh row 0 + v.instruction.is_sw row 0 +
        v.instruction.is_sd row 0)
      (v.addr_word_0 row 0) (v.addr_word_1 row 0) (store_width air row)
      (v.code_range.code_start_0 row 0) (v.code_range.code_start_1 row 0)
      (v.code_range.code_end_0 row 0) (v.code_range.code_end_1 row 0)
      (v.code_range.below row 0) (v.code_range.borrow row 0)
      (v.code_range.distance_0 row 0) (v.code_range.distance_1 row 0)
  := by
    simp only [allHold_iff_allHold_simplified, allHold_simplified, row_constraint_list,
      List.Forall] at h_constraints
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      h55, h56, h57, h58 ⟩ := h_constraints
    simp only [constraint_55, constraint_56, constraint_57, constraint_58] at h55 h56 h57 h58
    refine ⟨ h55, h56, ?_, ?_ ⟩
    · unfold store_width; linear_combination h57
    · linear_combination h58

  /-- What the tables promise the row's messages covers what they promise the `code_range`
      gadget's three: the gadget's messages are among the row's. -/
  lemma bus_row_all_wf_asm_code_range
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
  :
    let v := air.cols
    bus_row_all_wf_asm
      (CodeRangeGadget.AbsBuses
        (v.instruction.is_sb row 0 + v.instruction.is_sh row 0 + v.instruction.is_sw row 0 +
          v.instruction.is_sd row 0)
        (v.code_range.code_start_0 row 0) (v.code_range.code_start_1 row 0)
        (v.code_range.code_end_0 row 0) (v.code_range.code_end_1 row 0)
        (v.code_range.distance_0 row 0) (v.code_range.distance_1 row 0))
  := by
    obtain ⟨ h_wf, h_cr ⟩ := h_wf_asm
    refine ⟨ ?_, h_cr ⟩
    simp only [bus_row_wf_asm, bus_row, AbsBuses, CodeRangeGadget.AbsBuses, List.map,
      List.append_nil, List.nil_append, List.forall_append, List.Forall] at h_wf ⊢
    tauto

end MemoryUnalignedChip.Interpretations

namespace MemoryUnalignedChip.Spec

  open RV64IM_Interactions.V3
  open MemoryUnalignedChip.ConstraintsAndBuses
  open MemoryUnalignedChip.Interactions
  open MemoryUnalignedChip.Interpretations

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

  /-! ### The row's flags -/

  /-- The row's eleven instruction flags, in column order. -/
  def flags [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) : List FKB :=
    let i := air.cols.instruction
    [i.is_lb row 0, i.is_lbu row 0, i.is_lh row 0, i.is_lhu row 0, i.is_lw row 0,
     i.is_lwu row 0, i.is_ld row 0, i.is_sb row 0, i.is_sh row 0, i.is_sw row 0, i.is_sd row 0]

  /-- The 59 constraints, one by one. -/
  lemma constraints_of_allHold
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
  :
    constraint_0 air row ∧ constraint_1 air row ∧ constraint_2 air row ∧ constraint_3 air row ∧
    constraint_4 air row ∧ constraint_5 air row ∧ constraint_6 air row ∧ constraint_7 air row ∧
    constraint_8 air row ∧ constraint_9 air row ∧ constraint_10 air row ∧ constraint_11 air row ∧
    constraint_12 air row ∧ constraint_13 air row ∧ constraint_14 air row ∧ constraint_15 air row ∧
    constraint_16 air row ∧ constraint_17 air row ∧ constraint_18 air row ∧ constraint_19 air row ∧
    constraint_20 air row ∧ constraint_21 air row ∧ constraint_22 air row ∧ constraint_23 air row ∧
    constraint_24 air row ∧ constraint_25 air row ∧ constraint_26 air row ∧ constraint_27 air row ∧
    constraint_28 air row ∧ constraint_29 air row ∧ constraint_30 air row ∧ constraint_31 air row ∧
    constraint_32 air row ∧ constraint_33 air row ∧ constraint_34 air row ∧ constraint_35 air row ∧
    constraint_36 air row ∧ constraint_37 air row ∧ constraint_38 air row ∧ constraint_39 air row ∧
    constraint_40 air row ∧ constraint_41 air row ∧ constraint_42 air row ∧ constraint_43 air row ∧
    constraint_44 air row ∧ constraint_45 air row ∧ constraint_46 air row ∧ constraint_47 air row ∧
    constraint_48 air row ∧ constraint_49 air row ∧ constraint_50 air row ∧ constraint_51 air row ∧
    constraint_52 air row ∧ constraint_53 air row ∧ constraint_54 air row ∧ constraint_55 air row ∧
    constraint_56 air row ∧ constraint_57 air row ∧ constraint_58 air row
  := by
    simp only [allHold_iff_allHold_simplified, allHold_simplified, row_constraint_list,
      List.Forall] at h_constraints
    exact h_constraints.2

  /-- Each flag is 0 or 1 (constraints 0 to 10), and their sum is 0 or 1 (constraint 11), so the
      sum of their values is at most 1. -/
  lemma flag_vals
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
  :
    let i := air.cols.instruction
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
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
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
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_lb row 0 = 1)
  :
    flags air row = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_lb row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lbu = 1` the other flags are 0. -/
  lemma flags_of_is_lbu
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_lbu row 0 = 1)
  :
    flags air row = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_lbu row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lh = 1` the other flags are 0. -/
  lemma flags_of_is_lh
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_lh row 0 = 1)
  :
    flags air row = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_lh row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lhu = 1` the other flags are 0. -/
  lemma flags_of_is_lhu
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_lhu row 0 = 1)
  :
    flags air row = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_lhu row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lw = 1` the other flags are 0. -/
  lemma flags_of_is_lw
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_lw row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_lw row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_lwu = 1` the other flags are 0. -/
  lemma flags_of_is_lwu
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_lwu row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_lwu row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_ld = 1` the other flags are 0. -/
  lemma flags_of_is_ld
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_ld row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_ld row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sb = 1` the other flags are 0. -/
  lemma flags_of_is_sb
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_sb row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_sb row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sh = 1` the other flags are 0. -/
  lemma flags_of_is_sh
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_sh row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_sh row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sw = 1` the other flags are 0. -/
  lemma flags_of_is_sw
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_sw row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_sw row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-- On a row with `is_sd = 1` the other flags are 0. -/
  lemma flags_of_is_sd
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h : air.cols.instruction.is_sd row 0 = 1)
  :
    flags air row = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  := by
    have h_vals := flag_vals air row h_constraints
    have h1 : (air.cols.instruction.is_sd row 0).val = 1 := by rw [h]; rfl
    simp only [flags, List.cons.injEq, and_true]
    simp only at h_vals
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    all_goals first
      | exact h
      | exact zero_of_val (by clear h_constraints h; omega)

  /-! ### What the buses give a real row -/

  /-- The flags' sum on a row: 1 on a real row, which receives the memory dispatch at `-1`. -/
  def is_memory [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) : FKB :=
    let i := air.cols.instruction
    i.is_lb row 0 + i.is_lbu row 0 + i.is_lh row 0 + i.is_lhu row 0 + i.is_lw row 0 +
      i.is_lwu row 0 + i.is_ld row 0 +
      (i.is_sb row 0 + i.is_sh row 0 + i.is_sw row 0 + i.is_sd row 0)

  /-- A 16-bit piece split into a low byte and the high byte, both in range. -/
  def bytes_ok (x lo : FKB) : Prop :=
    lo.val < 256 ∧ (high_byte x lo).val < 256

  /-- What the buses give a real row. From the CPU, as the sender of the memory dispatch
      (`MemoryBus.externals`): `b` and `c` have 16-bit pieces, so does a store's `a`, and
      `a = 0` when `op_a_0 ≠ 0`. From the memory argument (`StateBusEntry`): the first dword read
      has 16-bit pieces. From the byte table (`ByteBus.Spec`), for the checks the row's flags
      send: the sign-bit operand, and the byte splits of the first dword, of the second dword
      on a row that crosses, and of `a` on a store. -/
  lemma bus_facts
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
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
    ((v.first.prev_value_0 row 0).val < 65536 ∧ (v.first.prev_value_1 row 0).val < 65536 ∧
      (v.first.prev_value_2 row 0).val < 65536 ∧ (v.first.prev_value_3 row 0).val < 65536) ∧
    (i.is_lb row 0 + i.is_lh row 0 + i.is_lw row 0 = 1 →
      (2 * v.sign_src row 0 - v.msb row 0 * 65536).val < 65536) ∧
    (bytes_ok (v.first.prev_value_0 row 0) (v.first_bytes.low_bytes_0 row 0) ∧
      bytes_ok (v.first.prev_value_1 row 0) (v.first_bytes.low_bytes_1 row 0) ∧
      bytes_ok (v.first.prev_value_2 row 0) (v.first_bytes.low_bytes_2 row 0) ∧
      bytes_ok (v.first.prev_value_3 row 0) (v.first_bytes.low_bytes_3 row 0)) ∧
    (v.cross row 0 = 1 →
      bytes_ok (v.second.prev_value_0 row 0) (v.second_bytes.low_bytes_0 row 0) ∧
      bytes_ok (v.second.prev_value_1 row 0) (v.second_bytes.low_bytes_1 row 0) ∧
      bytes_ok (v.second.prev_value_2 row 0) (v.second_bytes.low_bytes_2 row 0) ∧
      bytes_ok (v.second.prev_value_3 row 0) (v.second_bytes.low_bytes_3 row 0)) ∧
    (i.is_sb row 0 + i.is_sh row 0 + i.is_sw row 0 + i.is_sd row 0 = 1 →
      bytes_ok (i.op_a_value_0 row 0) (v.value_bytes.low_bytes_0 row 0) ∧
      bytes_ok (i.op_a_value_1 row 0) (v.value_bytes.low_bytes_1 row 0) ∧
      bytes_ok (i.op_a_value_2 row 0) (v.value_bytes.low_bytes_2 row 0) ∧
      bytes_ok (i.op_a_value_3 row 0) (v.value_bytes.low_bytes_3 row 0))
  := by
    have h_cases := flag_cases air row h_constraints
    simp only [is_memory] at h_mem
    simp [bus_row_all_ext_asm, bus_row_ext_asm, bus_row_code_range_ext_asm, bus_row,
      MemoryUnalignedChip.AbsBuses, MemoryBus.externals, h_mem] at h_ext_asm
    obtain ⟨ -, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, h_store, h_x0 ⟩ := h_ext_asm
    simp [bus_row_all_wf_asm, bus_row_wf_asm, bus_row_code_range_wf_asm, bus_row,
      MemoryUnalignedChip.AbsBuses, h_mem, RV64IM_Interactions.ByteBus.Spec] at h_wf_asm
    obtain ⟨ ⟨ -, -, -, -, -, -, -, f0, f1, f2, f3, s0, s1, s2, s3, r0, r1, r2, r3, h_msb, -, -,
      ⟨ hp0, hp1, hp2, hp3 ⟩, -, - ⟩, - ⟩ := h_wf_asm
    refine ⟨ ⟨ hb0, hb1, hb2, hb3 ⟩, ⟨ hc0, hc1, hc2, hc3 ⟩, fun hs => h_store ?_, h_x0,
      ⟨ hp0, hp1, hp2, hp3 ⟩, h_msb, ⟨ f0, f1, f2, f3 ⟩,
      fun hc => ⟨ s0 hc, s1 hc, s2 hc, s3 hc ⟩, fun hs => ⟨ r0 hs, r1 hs, r2 hs, r3 hs ⟩ ⟩
    simp only [flags] at h_cases
    rcases h_cases with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
      simp [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, MemoryBus.isStore] at hs ⊢

  /-! ### The offset -/

  /-- The row's eight offset flags, in column order. -/
  def offsets [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) : List FKB :=
    let v := air.cols
    [v.offset_0 row 0, v.offset_1 row 0, v.offset_2 row 0, v.offset_3 row 0, v.offset_4 row 0,
     v.offset_5 row 0, v.offset_6 row 0, v.offset_7 row 0]

  /-- On a real row the offset flags' values sum to 1: each is 0 or 1 (constraints 17 to 24),
      and their sum is the flags' sum (constraint 25). -/
  lemma offset_vals
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    (v.offset_0 row 0).val + (v.offset_1 row 0).val + (v.offset_2 row 0).val +
      (v.offset_3 row 0).val + (v.offset_4 row 0).val + (v.offset_5 row 0).val +
      (v.offset_6 row 0).val + (v.offset_7 row 0).val = 1
  := by
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, c20, c21, c22,
      c23, c24, c25, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_17, constraint_18, constraint_19, constraint_20, constraint_21,
      constraint_22, constraint_23, constraint_24, constraint_25]
      at c17 c18 c19 c20 c21 c22 c23 c24 c25
    simp only [is_memory] at h_mem
    have hs : air.cols.offset_0 row 0 + air.cols.offset_1 row 0 + air.cols.offset_2 row 0 +
        air.cols.offset_3 row 0 + air.cols.offset_4 row 0 + air.cols.offset_5 row 0 +
        air.cols.offset_6 row 0 + air.cols.offset_7 row 0 = 1 := by
      linear_combination c25 + h_mem
    have v0 := val_le_one (bool_cases c17)
    have v1 := val_le_one (bool_cases c18)
    have v2 := val_le_one (bool_cases c19)
    have v3 := val_le_one (bool_cases c20)
    have v4 := val_le_one (bool_cases c21)
    have v5 := val_le_one (bool_cases c22)
    have v6 := val_le_one (bool_cases c23)
    have v7 := val_le_one (bool_cases c24)
    have hv := congrArg Fin.val hs
    clear c17 c18 c19 c20 c21 c22 c23 c24 c25 hs h_mem
    simp only [Fin.val_add] at hv
    repeat rw [Nat.mod_eq_of_lt (by omega)] at hv
    exact hv

  /-- Eight numbers whose sum is 1: exactly one is 1. -/
  lemma nat_one_hot8 (n0 n1 n2 n3 n4 n5 n6 n7 : ℕ)
      (h : n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 = 1) :
    [n0, n1, n2, n3, n4, n5, n6, n7] = [1, 0, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 1, 0, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 0, 1, 0, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 0, 0, 1, 0, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 0, 0, 0, 1, 0, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 0, 0, 0, 0, 1, 0, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 0, 0, 0, 0, 0, 1, 0] ∨
    [n0, n1, n2, n3, n4, n5, n6, n7] = [0, 0, 0, 0, 0, 0, 0, 1] := by
    simp only [List.cons.injEq, and_true]
    rcases Nat.lt_or_ge 0 n0 with h0 | h0
    · left; omega
    rcases Nat.lt_or_ge 0 n1 with h1 | h1
    · right; left; omega
    rcases Nat.lt_or_ge 0 n2 with h2 | h2
    · right; right; left; omega
    rcases Nat.lt_or_ge 0 n3 with h3 | h3
    · right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n4 with h4 | h4
    · right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n5 with h5 | h5
    · right; right; right; right; right; left; omega
    rcases Nat.lt_or_ge 0 n6 with h6 | h6
    · right; right; right; right; right; right; left; omega
    right; right; right; right; right; right; right; omega

  /-- On a real row exactly one offset flag is 1. -/
  lemma offset_cases
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    offsets air row = [1, 0, 0, 0, 0, 0, 0, 0] ∨ offsets air row = [0, 1, 0, 0, 0, 0, 0, 0] ∨
    offsets air row = [0, 0, 1, 0, 0, 0, 0, 0] ∨ offsets air row = [0, 0, 0, 1, 0, 0, 0, 0] ∨
    offsets air row = [0, 0, 0, 0, 1, 0, 0, 0] ∨ offsets air row = [0, 0, 0, 0, 0, 1, 0, 0] ∨
    offsets air row = [0, 0, 0, 0, 0, 0, 1, 0] ∨ offsets air row = [0, 0, 0, 0, 0, 0, 0, 1]
  := by
    have h := nat_one_hot8 _ _ _ _ _ _ _ _ (offset_vals air row h_constraints h_mem)
    simp only [offsets, List.cons.injEq, and_true, Fin.ext_iff, Fin.val_zero, Fin.val_one] at h ⊢
    exact h

  /-- On a real row the offset `Σ k · offset_k` is at most 7. -/
  lemma offset_value_le
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    (v.offset_1 row 0 + v.offset_2 row 0 * 2 + v.offset_3 row 0 * 3 + v.offset_4 row 0 * 4 +
      v.offset_5 row 0 * 5 + v.offset_6 row 0 * 6 + v.offset_7 row 0 * 7).val ≤ 7
  := by
    rcases offset_cases air row h_constraints h_mem with h | h | h | h | h | h | h | h <;>
      simp only [offsets, List.cons.injEq, and_true] at h <;>
      obtain ⟨ -, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
      simp only [o1, o2, o3, o4, o5, o6, o7] <;> decide

  lemma val_add_of_lt {x y : FKB} (h : x.val + y.val < 2130706433) :
      (x + y).val = x.val + y.val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt h]

  lemma val_mul_of_lt {x y : FKB} (h : x.val * y.val < 2130706433) :
      (x * y).val = x.val * y.val := by
    rw [Fin.val_mul, Nat.mod_eq_of_lt h]

  /-- On a real row the address `b + c` is `addr_word_0 + 2^16 addr_word_1`, both pieces are
      16-bit, and the second is not 0. From the carry chain (constraints 12 to 15), the guard on
      `addr_word_1` (16), the `U16Range` check of `addr_word_1`, the `BitRange(13)` check of
      `dword0 / 8` with the offset at most 7, and the CPU's promise that `b` and `c` have 16-bit
      pieces. -/
  lemma address
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat =
      (v.addr_word_0 row 0).val + 65536 * (v.addr_word_1 row 0).val ∧
    (v.addr_word_0 row 0).val < 65536 ∧ (v.addr_word_1 row 0).val < 65536 ∧
    0 < (v.addr_word_1 row 0).val
  := by
    have h_off := offset_value_le air row h_constraints h_mem
    simp only [is_memory] at h_mem
    simp [bus_row_all_ext_asm, bus_row_ext_asm, bus_row_code_range_ext_asm, bus_row,
        MemoryUnalignedChip.AbsBuses,
      MemoryBus.externals, h_mem] at h_ext_asm
    obtain ⟨ -, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, - ⟩ := h_ext_asm
    simp [bus_row_all_wf_asm, bus_row_wf_asm, bus_row_code_range_wf_asm, bus_row,
        MemoryUnalignedChip.AbsBuses, h_mem,
      RV64IM_Interactions.ByteBus.Spec] at h_wf_asm
    obtain ⟨ ⟨ h_aw1, h_br, - ⟩, - ⟩ := h_wf_asm
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, c12, c13, c14, c15, c16, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_12, constraint_13, constraint_14, constraint_15, constraint_16]
      at c12 c13 c14 c15 c16
    rw [h_mem] at c16
    dsimp only at h_off ⊢
    set b0 := air.cols.instruction.op_b_value_0 row 0
    set b1 := air.cols.instruction.op_b_value_1 row 0
    set b2 := air.cols.instruction.op_b_value_2 row 0
    set b3 := air.cols.instruction.op_b_value_3 row 0
    set c0 := air.cols.instruction.op_c_value_0 row 0
    set c1 := air.cols.instruction.op_c_value_1 row 0
    set c2 := air.cols.instruction.op_c_value_2 row 0
    set c3 := air.cols.instruction.op_c_value_3 row 0
    set a0 := air.cols.addr_word_0 row 0
    set a1 := air.cols.addr_word_1 row 0
    set off := air.cols.offset_1 row 0 + air.cols.offset_2 row 0 * 2 +
      air.cols.offset_3 row 0 * 3 + air.cols.offset_4 row 0 * 4 + air.cols.offset_5 row 0 * 5 +
      air.cols.offset_6 row 0 * 6 + air.cols.offset_7 row 0 * 7
    set k1 := (0 + b0 + c0 - a0) * 2130673921 with hk1
    set k2 := (0 + b1 + c1 + k1 - a1) * 2130673921 with hk2
    set k3 := (0 + b2 + c2 + k2) * 2130673921 with hk3
    set k4 := (0 + b3 + c3 + k3) * 2130673921 with hk4
    set t := (a0 - off) * 1864368129 with ht
    have inv16 : ∀ x : FKB, x * 2130673921 * 65536 = x := fun x => by
      rw [mul_assoc, show (2130673921 : FKB) * 65536 = 1 from rfl, mul_one]
    have e1 : b0 + c0 = a0 + 65536 * k1 := by rw [hk1, mul_comm 65536, inv16]; ring
    have e2 : b1 + c1 + k1 = a1 + 65536 * k2 := by rw [hk2, mul_comm 65536, inv16]; ring
    have e3 : b2 + c2 + k2 = 65536 * k3 := by rw [hk3, mul_comm 65536, inv16]; ring
    have e4 : b3 + c3 + k3 = 65536 * k4 := by rw [hk4, mul_comm 65536, inv16]; ring
    have e0 : a0 = off + 8 * t := by
      rw [ht, mul_comm 8, mul_assoc, show (1864368129 : FKB) * 8 = 1 from rfl]; ring
    have h_a1 : a1 ≠ 0 := by rintro h; rw [h, mul_zero] at c16; exact absurd c16 (by decide)
    have vk1 := val_le_one (bool_cases c12)
    have vk2 := val_le_one (bool_cases c13)
    have vk3 := val_le_one (bool_cases c14)
    have vk4 := val_le_one (bool_cases c15)
    have h_a1_pos : 0 < a1.val := Nat.pos_of_ne_zero (fun h => h_a1 (Fin.ext h))
    clear_value b0 b1 b2 b3 c0 c1 c2 c3 a0 a1 off k1 k2 k3 k4 t
    clear c12 c13 c14 c15 c16 hk1 hk2 hk3 hk4 ht h_a1 inv16 h_mem
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

  /-- On a real row the address `b + c` lies in `[2^16, 2^32)`. -/
  lemma address_bounds
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
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

  /-- On a real row the dword the row reads and writes back first is the one holding the
      access's first byte, and on a row that crosses the second is the next one: the offset
      `Σ k · offset_k` is the address's low three bits, the first State message's address
      `[dword0, addr_word_1, 0]` with `dword0 = addr_word_0 - offset` is `b + c` with those bits
      cleared, and the second's `[next0, next1, 0]` is 8 more
      (`riscv_memory/unaligned/constraints.rs:95-116, 130-153` at v3.1.6). From `address`, the
      one-hot offset (constraints 17 to 25), the `BitRange(13)` check of `dword0 / 8`, the
      pinning of `next_carry` (constraints 27 to 29) and the `U16Range` check of `next1`. -/
  lemma aligned_address
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    let addr := (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat
    let offset := v.offset_1 row 0 + v.offset_2 row 0 * 2 + v.offset_3 row 0 * 3 +
      v.offset_4 row 0 * 4 + v.offset_5 row 0 * 5 + v.offset_6 row 0 * 6 + v.offset_7 row 0 * 7
    let dword0 := v.addr_word_0 row 0 - offset
    offset.val = addr % 8 ∧
    dword0.val + 65536 * (v.addr_word_1 row 0).val = addr - addr % 8 ∧
    (v.cross row 0 = 1 →
      (dword0 + 8 - v.next_carry row 0 * 65536).val +
        65536 * (v.addr_word_1 row 0 + v.next_carry row 0).val = addr - addr % 8 + 8)
  := by
    obtain ⟨ h_addr, -, h_a1, - ⟩ := address air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_off := offset_value_le air row h_constraints h_mem
    simp only [is_memory] at h_mem
    simp [bus_row_all_wf_asm, bus_row_wf_asm, bus_row_code_range_wf_asm, bus_row,
      MemoryUnalignedChip.AbsBuses, h_mem, RV64IM_Interactions.ByteBus.Spec] at h_wf_asm
    obtain ⟨ ⟨ -, h_br, h_next1, - ⟩, - ⟩ := h_wf_asm
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      c27, c28, c29, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_27, constraint_28, constraint_29] at c27 c28 c29
    rw [h_mem] at c29
    dsimp only at h_addr h_off ⊢
    rw [h_addr]
    set a0 := air.cols.addr_word_0 row 0
    set a1 := air.cols.addr_word_1 row 0
    set nc := air.cols.next_carry row 0
    set off := air.cols.offset_1 row 0 + air.cols.offset_2 row 0 * 2 +
      air.cols.offset_3 row 0 * 3 + air.cols.offset_4 row 0 * 4 + air.cols.offset_5 row 0 * 5 +
      air.cols.offset_6 row 0 * 6 + air.cols.offset_7 row 0 * 7 with h_off_def
    have d28 : nc * (a0 - off - 65528) = 0 := by rw [h_off_def]; linear_combination c28
    have d29 : (a0 - off - 65528) * air.cols.next_carry_inv row 0 = 1 - nc := by
      rw [h_off_def]; linear_combination c29
    set t := (a0 - off) * 1864368129 with ht
    have e : a0 - off = 8 * t := by
      rw [ht, mul_comm 8, mul_assoc, show (1864368129 : FKB) * 8 = 1 from rfl, mul_one]
    have h_t : (a0 - off).val = 8 * t.val := by
      rw [e, val_mul_of_lt (by rw [show (8 : FKB).val = 8 from rfl]; omega)]; rfl
    have h_a0_val : a0.val = off.val + 8 * t.val := by
      have e2 : a0 = off + 8 * t := by rw [← e]; ring
      have h8 : (8 * t).val = 8 * t.val := by
        rw [val_mul_of_lt (by rw [show (8 : FKB).val = 8 from rfl]; omega)]; rfl
      conv_lhs => rw [e2]
      rw [val_add_of_lt (by omega), h8]
    refine ⟨ by omega, by omega, fun hc => ?_ ⟩
    have h_n1 := h_next1 hc
    rcases bool_cases c27 with hn | hn
    · have h_ne : a0 - off - 65528 ≠ 0 := by
        intro h; rw [h, zero_mul, hn, sub_zero] at d29; exact absurd d29 (by decide)
      have h_ne' : (a0 - off).val ≠ 65528 := by
        intro h; apply h_ne
        rw [sub_eq_zero]; exact Fin.ext (by rw [h]; rfl)
      have h8 : (a0 - off + 8).val = (a0 - off).val + 8 := by
        rw [val_add_of_lt (by rw [show (8 : FKB).val = 8 from rfl]; omega)]; rfl
      rw [hn, zero_mul, sub_zero, add_zero, h8]
      omega
    · have h_eq : a0 - off = 65528 := by
        rcases mul_eq_zero.mp d28 with h | h
        · rw [hn] at h; exact absurd h (by decide)
        · exact sub_eq_zero.mp h
      rw [hn] at h_n1 ⊢
      have h_a1' : (a1 + 1).val = a1.val + 1 := by
        rw [val_add_of_lt (by rw [show (1 : FKB).val = 1 from rfl]; omega)]; rfl
      rw [h_eq, h_a1', show (65528 + 8 - 1 * 65536 : FKB) = 0 from rfl]
      rw [h_eq] at h_t
      simp only [Fin.val_zero]
      have : (65528 : FKB).val = 65528 := rfl
      omega

  /-! ### What a load reads -/

  /-- Two bytes make a 16-bit piece. -/
  lemma limb_lt {x y : FKB} (hx : x.val < 256) (hy : y.val < 256) :
      (limb x y).val < 65536 := by
    show (x + y * 256 : FKB).val < 65536
    have v256 : (256 : FKB).val = 256 := rfl
    have hm : (y * 256).val = y.val * 256 := by
      rw [val_mul_of_lt (by rw [v256]; omega), v256]
    rw [val_add_of_lt (by rw [hm]; omega), hm]
    omega

  /-- On a real row the bytes a load reads are in range: `seen_byte` is a byte, and the pieces
      `seen_l` a load of each width uses are 16-bit. A piece reaches into the second dword only
      at the offsets where the access crosses (constraint 26 names them, per width), and there
      the second dword's bytes are checked. -/
  lemma seen_lt
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    (v.seen_byte row 0).val < 256 ∧
    (v.cross row 0 = v.offset_7 row 0 → (v.seen_0 row 0).val < 65536) ∧
    (v.cross row 0 = v.offset_5 row 0 + v.offset_6 row 0 + v.offset_7 row 0 →
      (v.seen_0 row 0).val < 65536 ∧ (v.seen_1 row 0).val < 65536) ∧
    (v.cross row 0 = v.offset_1 row 0 + v.offset_2 row 0 + v.offset_3 row 0 + v.offset_4 row 0 +
        v.offset_5 row 0 + v.offset_6 row 0 + v.offset_7 row 0 →
      (v.seen_0 row 0).val < 65536 ∧ (v.seen_1 row 0).val < 65536 ∧
      (v.seen_2 row 0).val < 65536 ∧ (v.seen_3 row 0).val < 65536)
  := by
    obtain ⟨ -, -, -, -, -, -, ⟨ ⟨ l0, h0 ⟩, ⟨ l1, h1 ⟩, ⟨ l2, h2 ⟩, ⟨ l3, h3 ⟩ ⟩, h_second, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_cases := offset_cases air row h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, c31, c32, c33, c34, c35, c36, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_31] at c31
    simp only [constraint_32, constraint_33, constraint_34, constraint_35, constraint_36,
      sub_eq_zero] at c32 c33 c34 c35 c36
    clear h_ext_asm h_wf_asm h_constraints
    dsimp only
    rw [c32, c33, c34, c35, c36]
    clear c32 c33 c34 c35 c36
    rcases bool_cases c31 with hx | hx
    · rw [hx]
      rcases h_cases with h | h | h | h | h | h | h | h <;>
        simp only [offsets, List.cons.injEq, and_true] at h <;>
        obtain ⟨ o0, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
        refine ⟨ ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_ ⟩ <;>
        simp only [o0, o1, o2, o3, o4, o5, o6, o7, zero_mul, one_mul, zero_add, add_zero] <;>
        (try simp only [o1, o2, o3, o4, o5, o6, o7, zero_add, add_zero] at hc) <;>
        (try refine ⟨ ?_, ?_, ?_, ?_ ⟩) <;>
        (try refine ⟨ ?_, ?_ ⟩) <;>
        first
          | (simp only [*]; done)
          | (simp at hc; done)
          | (apply limb_lt <;> (simp only [*]; done))
    · obtain ⟨ ⟨ m0, n0 ⟩, ⟨ m1, n1 ⟩, ⟨ m2, n2 ⟩, ⟨ m3, n3 ⟩ ⟩ := h_second hx
      rw [hx]
      rcases h_cases with h | h | h | h | h | h | h | h <;>
        simp only [offsets, List.cons.injEq, and_true] at h <;>
        obtain ⟨ o0, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
        refine ⟨ ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_ ⟩ <;>
        simp only [o0, o1, o2, o3, o4, o5, o6, o7, zero_mul, one_mul, zero_add, add_zero] <;>
        (try simp only [o1, o2, o3, o4, o5, o6, o7, zero_add, add_zero] at hc) <;>
        (try refine ⟨ ?_, ?_, ?_, ?_ ⟩) <;>
        (try refine ⟨ ?_, ?_ ⟩) <;>
        first
          | (simp only [*]; done)
          | (simp at hc; done)
          | (apply limb_lt <;> (simp only [*]; done))

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

  /-- On a load of a byte, sign-extended row (`is_lb = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 10. -/
  theorem spec_LB
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lb : air.cols.instruction.is_lb row 0 = 1)
  :
    MemoryBus.Spec 10
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lb air row h_constraints h_is_lb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ h_sb, - ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, -, c42, -, -, c45, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_37, constraint_38, constraint_39, constraint_40, constraint_42,
      constraint_45, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c37 c38 c39 c40 c42 c45
    have h_sign : (air.cols.sign_src row 0).val = 256 * (air.cols.seen_byte row 0).val := by
      rw [c42, val_mul_of_lt (by simp; omega)]; rfl
    rcases msb_check (by omega) c45 (h_msb (by simp [f0, f2, f4])) with
        ⟨ hm, hl ⟩ | ⟨ hm, hl ⟩ <;>
      rw [hm] at c37 c38 c39 c40 <;> norm_num at c37 c38 c39 c40 <;> rw [c37, c38, c39, c40]
    · refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun _ _ => ?_, fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
      · exact ⟨ by omega, by decide, by decide, by decide ⟩
      · rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
          toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
        norm_num
        rw [if_neg (by omega)]
        omega
    · have hv : (air.cols.seen_byte row 0 + 65280).val =
          (air.cols.seen_byte row 0).val + 65280 := by
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

  /-- On a load of a byte, zero-extended row (`is_lbu = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 13. -/
  theorem spec_LBU
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lbu : air.cols.instruction.is_lbu row 0 = 1)
  :
    MemoryBus.Spec 13
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lbu air row h_constraints h_is_lbu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ h_sb, - ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_37, constraint_38, constraint_39, constraint_40,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38 c39 c40
    rw [c37, c38, c39, c40]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ _ => ?_,
        fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    · exact ⟨ by omega, by decide, by decide, by decide ⟩
    · rw [eq_zeroExtend_truncate_iff (by norm_num),
        toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
      norm_num
      omega

  /-- On a load of a half word, sign-extended row (`is_lh = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 11. -/
  theorem spec_LH
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lh : air.cols.instruction.is_lh row 0 = 1)
  :
    MemoryBus.Spec 11
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lh air row h_constraints h_is_lh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
      -, -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, -, -, c43, -, c45, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_7 row 0 := by linear_combination c26
    obtain ⟨ -, h_s0, -, - ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_s := h_s0 hc
    simp [constraint_37, constraint_38, constraint_39, constraint_40, constraint_43,
      constraint_45, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c37 c38 c39 c40 c43 c45
    rw [← c43] at h_s
    rcases msb_check h_s c45 (h_msb (by simp [f0, f2, f4])) with
        ⟨ hm, hl ⟩ | ⟨ hm, hl ⟩ <;>
      rw [hm] at c38 c39 c40 <;> norm_num at c38 c39 c40 <;> rw [c37, ← c43, c38, c39, c40]
    all_goals refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
      fun _ _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    all_goals first
      | exact ⟨ by omega, by decide, by decide, by decide ⟩
      | (rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
            toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
         norm_num
         first | (rw [if_neg (by omega)]; omega) | (rw [if_pos (by omega)]; omega))

  /-- On a load of a half word, zero-extended row (`is_lhu = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 14. -/
  theorem spec_LHU
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lhu : air.cols.instruction.is_lhu row 0 = 1)
  :
    MemoryBus.Spec 14
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lhu air row h_constraints h_is_lhu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
      -, -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_7 row 0 := by linear_combination c26
    obtain ⟨ -, h_s0, -, - ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_s := h_s0 hc
    simp [constraint_37, constraint_38, constraint_39, constraint_40,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38 c39 c40
    rw [c37, c38, c39, c40]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun _ _ => ?_, fun h => absurd h (by decide) ⟩
    · exact ⟨ by omega, by decide, by decide, by decide ⟩
    · rw [eq_zeroExtend_truncate_iff (by norm_num),
        toNat_toBV_of_lt _ _ _ _ (by omega) (by decide) (by decide) (by decide)]
      norm_num
      omega

  /-- On a load of a word, sign-extended row (`is_lw = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 12. -/
  theorem spec_LW
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lw : air.cols.instruction.is_lw row 0 = 1)
  :
    MemoryBus.Spec 12
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lw air row h_constraints h_is_lw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
      -, -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, -, -, -, c44, c45, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 =
        air.cols.offset_5 row 0 + air.cols.offset_6 row 0 + air.cols.offset_7 row 0 := by
      linear_combination c26
    obtain ⟨ -, -, h_s01, - ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_s0, h_s1 ⟩ := h_s01 hc
    simp [constraint_37, constraint_38, constraint_39, constraint_40, constraint_44,
      constraint_45, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero]
      at c37 c38 c39 c40 c44 c45
    rw [← c44] at h_s1
    rcases msb_check h_s1 c45 (h_msb (by simp [f0, f2, f4])) with
        ⟨ hm, hl ⟩ | ⟨ hm, hl ⟩ <;>
      rw [hm] at c39 c40 <;> norm_num at c39 c40 <;> rw [c37, c38, ← c44, c39, c40]
    all_goals refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun _ _ => ?_, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩
    all_goals first
      | exact ⟨ by omega, by omega, by decide, by decide ⟩
      | (rw [eq_signExtend_truncate_iff (by norm_num) (by norm_num),
            toNat_toBV_of_lt _ _ _ _ (by omega) (by omega) (by decide) (by decide)]
         norm_num
         first | (rw [if_neg (by omega)]; omega) | (rw [if_pos (by omega)]; omega))

  /-- On a load of a word, zero-extended row (`is_lwu = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 45. -/
  theorem spec_LWU
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lwu : air.cols.instruction.is_lwu row 0 = 1)
  :
    MemoryBus.Spec 45
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_lwu air row h_constraints h_is_lwu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
      -, -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 =
        air.cols.offset_5 row 0 + air.cols.offset_6 row 0 + air.cols.offset_7 row 0 := by
      linear_combination c26
    obtain ⟨ -, -, h_s01, - ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_s0, h_s1 ⟩ := h_s01 hc
    simp [constraint_37, constraint_38, constraint_39, constraint_40,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38 c39 c40
    rw [c37, c38, c39, c40]
    refine ⟨ fun _ => ?_, h_addr.1, h_addr.2, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun _ _ => ?_ ⟩
    · exact ⟨ by omega, by omega, by decide, by decide ⟩
    · rw [eq_zeroExtend_truncate_iff (by norm_num),
        toNat_toBV_of_lt _ _ _ _ (by omega) (by omega) (by decide) (by decide)]
      norm_num
      omega

  /-- On a load of a double word row (`is_ld = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 46. -/
  theorem spec_LD
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_ld : air.cols.instruction.is_ld row 0 = 1)
  :
    MemoryBus.Spec 46
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_ld air row h_constraints h_is_ld
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_x0, -, h_msb, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    by_cases h0 : air.cols.instruction.op_a_0 row 0 = 0
    swap
    · exact spec_of_x0 h0 (h_x0 h0) h_addr
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
      -, -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 =
        air.cols.offset_1 row 0 + air.cols.offset_2 row 0 + air.cols.offset_3 row 0 +
          air.cols.offset_4 row 0 + air.cols.offset_5 row 0 + air.cols.offset_6 row 0 +
          air.cols.offset_7 row 0 := by
      linear_combination c26
    obtain ⟨ -, -, -, h_s ⟩ := seen_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_s0, h_s1, h_s2, h_s3 ⟩ := h_s hc
    simp [constraint_37, constraint_38, constraint_39, constraint_40,
      f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38 c39 c40
    rw [c37, c38, c39, c40]
    exact ⟨ fun _ => ⟨ h_s0, h_s1, h_s2, h_s3 ⟩, h_addr.1, h_addr.2,
      fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide) ⟩

  /-- On a store of a byte row (`is_sb = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 15. -/
  theorem spec_SB
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sb : air.cols.instruction.is_sb row 0 = 1)
  :
    MemoryBus.Spec 15
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sb air row h_constraints h_is_sb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-- On a store of a half word row (`is_sh = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 16. -/
  theorem spec_SH
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sh : air.cols.instruction.is_sh row 0 = 1)
  :
    MemoryBus.Spec 16
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sh air row h_constraints h_is_sh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-- On a store of a word row (`is_sw = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 17. -/
  theorem spec_SW
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sw : air.cols.instruction.is_sw row 0 = 1)
  :
    MemoryBus.Spec 17
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sw air row h_constraints h_is_sw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-- On a store of a double word row (`is_sd = 1`),
      the memory dispatch the row receives meets the Memory promise with opcode 47. -/
  theorem spec_SD
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sd : air.cols.instruction.is_sd row 0 = 1)
  :
    MemoryBus.Spec 47
      (air.cols.instruction.op_a_value_0 row 0)
      (air.cols.instruction.op_a_value_1 row 0)
      (air.cols.instruction.op_a_value_2 row 0)
      (air.cols.instruction.op_a_value_3 row 0)
      (air.cols.instruction.op_b_value_0 row 0)
      (air.cols.instruction.op_b_value_1 row 0)
      (air.cols.instruction.op_b_value_2 row 0)
      (air.cols.instruction.op_b_value_3 row 0)
      (air.cols.instruction.op_c_value_0 row 0)
      (air.cols.instruction.op_c_value_1 row 0)
      (air.cols.instruction.op_c_value_2 row 0)
      (air.cols.instruction.op_c_value_3 row 0)
      (air.cols.instruction.op_a_0 row 0)
  := by
    have hf := flags_of_is_sd air row h_constraints h_is_sd
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_addr := address_bounds air row h_ext_asm h_wf_asm h_constraints h_mem
    exact spec_of_store (by decide) h_addr

  /-! ### The dwords written back -/

  /-- On a real row each dword written back has 16-bit pieces: every byte written is a byte the
      row checked, of the dword before the access or, on a store, of `a` (constraints 47 to 54).
      The second dword is written back only on a row that crosses. -/
  lemma write_value_lt
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    ((v.first.access.value_0 row 0).val < 65536 ∧ (v.first.access.value_1 row 0).val < 65536 ∧
      (v.first.access.value_2 row 0).val < 65536 ∧ (v.first.access.value_3 row 0).val < 65536) ∧
    (v.cross row 0 = 1 →
      (v.second.access.value_0 row 0).val < 65536 ∧ (v.second.access.value_1 row 0).val < 65536 ∧
      (v.second.access.value_2 row 0).val < 65536 ∧ (v.second.access.value_3 row 0).val < 65536)
  := by
    obtain ⟨ -, -, -, -, -, -, ⟨ ⟨ l0, h0 ⟩, ⟨ l1, h1 ⟩, ⟨ l2, h2 ⟩, ⟨ l3, h3 ⟩ ⟩, h_second,
      h_value ⟩ := bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_offs := offset_cases air row h_constraints h_mem
    have h_flags := flag_cases air row h_constraints
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, c31, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c47, c48, c49, c50, c51,
      c52, c53, c54, - ⟩ :=
      constraints_of_allHold air row h_constraints
    clear h_ext_asm h_wf_asm h_constraints
    simp only [constraint_31] at c31
    simp only [constraint_47, constraint_48, constraint_49, constraint_50, constraint_51,
      constraint_52, constraint_53, constraint_54, sub_eq_zero]
      at c47 c48 c49 c50 c51 c52 c53 c54
    dsimp only
    rw [c47, c48, c49, c50, c51, c52, c53, c54]
    clear c47 c48 c49 c50 c51 c52 c53 c54
    simp only [is_memory] at h_mem
    rcases bool_cases c31 with hx | hx
    · refine ⟨ ?_, fun hc => absurd (hx.symm.trans hc) (by decide) ⟩
      rcases h_flags with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp only [flags, List.cons.injEq, and_true] at h <;>
        obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h
      · simp [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at h_mem
      iterate 7
        · simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, zero_mul, mul_zero, zero_add,
            add_zero]
          refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> apply limb_lt <;> (simp only [*]; done)
      all_goals
        obtain ⟨ ⟨ r0, s0 ⟩, ⟨ r1, s1 ⟩, ⟨ r2, s2 ⟩, ⟨ r3, s3 ⟩ ⟩ :=
          h_value (by simp [f7, f8, f9, f10])
        rcases h_offs with h | h | h | h | h | h | h | h <;>
          simp only [offsets, List.cons.injEq, and_true] at h <;>
          obtain ⟨ o0, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
          simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, o0, o1, o2, o3, o4, o5, o6, o7,
            zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, add_sub_cancel] <;>
          refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> apply limb_lt <;> (simp only [*]; done)
    · obtain ⟨ ⟨ m0, n0 ⟩, ⟨ m1, n1 ⟩, ⟨ m2, n2 ⟩, ⟨ m3, n3 ⟩ ⟩ := h_second hx
      refine ⟨ ?_, fun _ => ?_ ⟩
      all_goals
        rcases h_flags with h | h | h | h | h | h | h | h | h | h | h | h <;>
          simp only [flags, List.cons.injEq, and_true] at h <;>
          obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h
        · simp [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at h_mem
        iterate 7
          · simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, zero_mul, mul_zero, zero_add,
              add_zero]
            refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> apply limb_lt <;> (simp only [*]; done)
        all_goals
          obtain ⟨ ⟨ r0, s0 ⟩, ⟨ r1, s1 ⟩, ⟨ r2, s2 ⟩, ⟨ r3, s3 ⟩ ⟩ :=
            h_value (by simp [f7, f8, f9, f10])
          rcases h_offs with h | h | h | h | h | h | h | h <;>
            simp only [offsets, List.cons.injEq, and_true] at h <;>
            obtain ⟨ o0, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
            simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, o0, o1, o2, o3, o4, o5, o6, o7,
            zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, add_sub_cancel] <;>
            refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> apply limb_lt <;> (simp only [*]; done)

  /-! ### The row's duties as a receiver and as a sender -/

  /-- The row owes the Memory promise to the memory dispatch it receives at `-1`, and 16-bit
      pieces to each dword it writes back at `-1`; every other message it sends at `+is_memory`,
      `+cross`, `+is_store` or another sum of flags, which is never `-1`. -/
  theorem wf_asrt
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
  :
    bus_row_all_wf_asrt (bus_row air row)
  := by
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
      -, -, -, -, c31, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_26, constraint_31] at c26 c31
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      have h' := h <;>
      simp only [flags, List.cons.injEq, and_true] at h' <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h'
    · have hx : air.cols.cross row 0 = 0 := by
        simp only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10] at c26
        linear_combination c26
      simp [bus_row_all_wf_asrt, bus_row_wf_asrt, bus_row_code_range_wf_asrt, bus_row,
        MemoryUnalignedChip.AbsBuses, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, hx]
    all_goals
      have h_mem : is_memory air row = 1 := by
        simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
      obtain ⟨ hv, hv' ⟩ := write_value_lt air row h_ext_asm h_wf_asm h_constraints h_mem
      rcases bool_cases c31 with hx | hx <;>
        simp [bus_row_all_wf_asrt, bus_row_wf_asrt, bus_row_code_range_wf_asrt, bus_row,
          MemoryUnalignedChip.AbsBuses, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, hx] <;>
        first
          | refine ⟨ hv, hv' hx, ?_ ⟩
          | refine ⟨ hv, ?_ ⟩
    iterate 2 exact spec_LB air row h_ext_asm h_wf_asm h_constraints f0
    iterate 2 exact spec_LBU air row h_ext_asm h_wf_asm h_constraints f1
    iterate 2 exact spec_LH air row h_ext_asm h_wf_asm h_constraints f2
    iterate 2 exact spec_LHU air row h_ext_asm h_wf_asm h_constraints f3
    iterate 2 exact spec_LW air row h_ext_asm h_wf_asm h_constraints f4
    iterate 2 exact spec_LWU air row h_ext_asm h_wf_asm h_constraints f5
    iterate 2 exact spec_LD air row h_ext_asm h_wf_asm h_constraints f6
    iterate 2 exact spec_SB air row h_ext_asm h_wf_asm h_constraints f7
    iterate 2 exact spec_SH air row h_ext_asm h_wf_asm h_constraints f8
    iterate 2 exact spec_SW air row h_ext_asm h_wf_asm h_constraints f9
    iterate 2 exact spec_SD air row h_ext_asm h_wf_asm h_constraints f10

  /-- The row asserts nothing to the tables it looks up, and the memory dispatch it receives is
      never at `+1`. -/
  theorem ext_asrt
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (_h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
  :
    bus_row_all_ext_asrt (bus_row air row)
  := by
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [flags, List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
      simp [bus_row_all_ext_asrt, bus_row_ext_asrt, bus_row_code_range_ext_asrt, bus_row,
        MemoryUnalignedChip.AbsBuses, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]

  /-! ### A store misses the code range -/

  /-- On a store row the bytes written, `[addr, addr + store_width)` with `addr = b + c`, miss
      the code range `[code_start, code_end)` the row looks up: they end at or below its start,
      or start at or above its end. The `code_range` gadget proves it
      (`CodeRangeGadget.Spec.gadget_spec`); the chip hands it `addr_word` and `store_width`
      (`riscv_memory/unaligned/constraints.rs:311-322` at v3.1.6) and supplies its premises: the
      address's two pieces are 16-bit and equal `b + c` (`address`), and the width is at most 8.
      The bytes written may lie in two dwords; the range they cover is the same. As in the
      gadget, the range is the one in the row's columns: the Program table's promise
      (`CodeRangeBus.Spec`) does not yet say it is the program's code range. -/
  theorem store_misses_code_range
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_store :
      air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
        air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1)
  :
    let v := air.cols
    let addr := (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat
    addr + (store_width air row).val ≤
        (v.code_range.code_start_0 row 0).val + 65536 * (v.code_range.code_start_1 row 0).val ∨
      (v.code_range.code_end_0 row 0).val + 65536 * (v.code_range.code_end_1 row 0).val ≤ addr
  := by
    have h_row : is_memory air row = 1 ∧ (store_width air row).val ≤ 8 := by
      rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
        simp only [flags, List.cons.injEq, and_true] at h <;>
        obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h <;>
        simp [is_memory, store_width, f0, f1, f2, f3, f4, f5, f6, f7,
          f8, f9, f10] at h_is_store ⊢
    obtain ⟨ h_mem, h_width ⟩ := h_row
    obtain ⟨ h_addr, h_a0, h_a1, - ⟩ := address air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_gadget := CodeRangeGadget.Spec.gadget_spec _ _ _ _ _ _ _ _ _ _ _ _
      (bus_row_all_wf_asm_code_range air row h_wf_asm) (allHold_code_range air row h_constraints)
      h_is_store ⟨ h_a0, h_a1 ⟩ (by omega)
    dsimp only at h_addr ⊢
    rw [h_addr]
    exact h_gadget

end MemoryUnalignedChip.Spec
