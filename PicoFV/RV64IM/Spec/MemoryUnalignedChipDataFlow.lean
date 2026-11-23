import PicoFV.RV64IM.Spec.MemoryUnalignedChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryUnalignedChip — what a row does to memory

The data flow of a row of `MemoryUnalignedChip` (`MemoryUnalignedChip::eval`,
`vm/src/chips/chips/riscv_memory/unaligned/constraints.rs`, Pico v3.2.0
`fcfa504624657d0c417c43f1233d5d891f293ff9`; messages in `Constraints/MemoryUnalignedChip.lean`).

A real row sends the memory argument the read of the double word holding the access's first byte
and receives its write back, at the aligned address `A`, `b + c` with its three low bits cleared;
on a row whose access runs into the next double word (`cross = 1`) it does the same for the
double word at `A + 8` (`riscv_memory/unaligned/constraints.rs:155-176` at v3.2.0). It receives
the memory dispatch from the CPU chip. `V3.bus_operations` reads each State pair as a
double-word `ReadMem` and `WriteMem`, and the dispatch as one access of its opcode's width at
`b + c`: a `WriteMem` of `a` for a store, a `ReadMem` of `a` for a load, or a `ReadMemAny` for a
load into `x0`.

- `dataFlow_of_allHold`: on every row, in any Sail state that holds the double words the row
  reads, the dispatch's read holds too, so a load's value, taken at the load's width, is the bytes
  from `b + c` on of the one or two double words read
  (`riscv_memory/unaligned/constraints.rs:211-250` at v3.2.0); and the two operation lists leave
  the same state, so a store writes the double words back with the stored bytes in their place
  and a load writes them back unchanged (`riscv_memory/unaligned/constraints.rs:273-308` at
  v3.2.0). The sign or zero fill above a load's width is not read here: it is the Memory
  promise's (`spec_LB` to `spec_LWU`).

`dataFlow_of_allHold` assumes what the Memory promise's theorems assume
(`Spec/MemoryUnalignedChip.lean`): the row's constraints (`allHold`) and what its messages are
promised (`bus_row_all_ext_asm`, `bus_row_all_wf_asm`). That the double words read are the ones
memory holds is the memory argument's promise, which `dataFlow_of_allHold` takes as the
hypothesis of `DataFlow`. `bus_operations` does not read the messages' `chunk`, `clk` and
`prev_clk` fields, and nothing here is said about them.

The proof reads the row as bytes: `wnat` is the sixteen bytes of the two double words before the
access (`w` in `constraints.rs`), `rnat` the eight bytes of `op_a` (`r`), and `wrnat` the sixteen
after the access. A double word's bytes past the first are read only on a row that crosses,
which is where the second double word's byte splits are range-checked.
-/

namespace MemoryUnalignedChip.Spec

  open RV64IM_Interactions.V3
  open MemoryUnalignedChip.ConstraintsAndBuses
  open MemoryUnalignedChip.Interactions

  /-- The row's data flow in the Sail state `state`: if the reads among the row's messages to the
      memory argument hold in `state`, the read of the memory dispatch the row receives holds
      too, and the two lists of operations leave the same state. -/
  def DataFlow
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :
    Prop
  :=
    let dispatch_bus : RV64IM_Interactions.V3.BusRow := {
      Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory
    }
    let access_bus : RV64IM_Interactions.V3.BusRow := {
      Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := []
    }
    (RV64IM.operation_list_effect
        (RV64IM_Interactions.V3.bus_operations access_bus) state).hypotheses →
      (RV64IM.operation_list_effect
          (RV64IM_Interactions.V3.bus_operations dispatch_bus) state).hypotheses ∧
      (RV64IM.operation_list_effect
          (RV64IM_Interactions.V3.bus_operations dispatch_bus) state).state =
        (RV64IM.operation_list_effect
          (RV64IM_Interactions.V3.bus_operations access_bus) state).state

  private abbrev SailState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

  private abbrev Mem := Std.ExtHashMap ℕ (BitVec 8)

  private lemma eq_with_mem (s : SailState) (m : Mem) (h : m = s.mem) :
      s = { s with mem := m } := by
    subst h; rfl

  /-- The memory `WriteMem A .Double V` leaves: the eight bytes of `V` from `A` on. -/
  private def write8 (m : Mem) (A : ℕ) (V : BitVec 64) : Mem :=
    (((((((m.insert A (V.extractLsb 7 0)).insert (A + 1) (V.extractLsb 15 8)).insert (A + 2)
      (V.extractLsb 23 16)).insert (A + 3) (V.extractLsb 31 24)).insert (A + 4)
      (V.extractLsb 39 32)).insert (A + 5) (V.extractLsb 47 40)).insert (A + 6)
      (V.extractLsb 55 48)).insert (A + 7) (V.extractLsb 63 56)

  private lemma write8_get (m : Mem) (A k : ℕ) (V : BitVec 64) :
      (write8 m A V)[k]? =
        if A ≤ k ∧ k < A + 8 then some (V.extractLsb' (8 * (k - A)) 8) else m[k]? := by
    simp only [write8, Std.ExtHashMap.getElem?_insert, beq_iff_eq, BitVec.extractLsb]
    split_ifs <;> first | omega | (subst_vars; simp)

  /-! ### The access side -/

  /-- The read and write back of one double word at `A`. -/
  private lemma access2_effect (s : SailState) (A : ℕ) (P V : BitVec 64) (Bp Bv : ℕ → BitVec 8)
      (hP : ∀ i < 8, P.extractLsb' (8 * i) 8 = Bp i)
      (hV : ∀ i < 8, V.extractLsb' (8 * i) 8 = Bv i) :
      ((RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses ↔
        ∀ i < 8, s.mem[A + i]? = some (Bp i)) ∧
      ∃ M : Mem,
        (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if A ≤ k ∧ k < A + 8 then some (Bv (k - A)) else s.mem[k]? := by
    refine ⟨ ?_, write8 s.mem A V, rfl, fun k => ?_ ⟩
    · have p0 := hP 0 (by omega); have p1 := hP 1 (by omega); have p2 := hP 2 (by omega)
      have p3 := hP 3 (by omega); have p4 := hP 4 (by omega); have p5 := hP 5 (by omega)
      have p6 := hP 6 (by omega); have p7 := hP 7 (by omega)
      simp only [Nat.reduceMul] at p0 p1 p2 p3 p4 p5 p6 p7
      simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect,
        BitVec.extractLsb, true_and, Nat.reduceSub, Nat.reduceAdd, p0, p1, p2, p3, p4, p5, p6, p7]
      constructor
      · rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ i hi
        interval_cases i <;> assumption
      · intro h
        exact ⟨ h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
          h 5 (by omega), h 6 (by omega), h 7 (by omega) ⟩
    · rw [write8_get]
      split_ifs with hk
      · rw [hV _ (by omega)]
      · rfl

  /-- The reads and write backs of two double words, at `A` and `A + 8`. -/
  private lemma access4_effect (s : SailState) (A : ℕ) (P1 V1 P2 V2 : BitVec 64)
      (Bp Bv : ℕ → BitVec 8)
      (hP1 : ∀ i < 8, P1.extractLsb' (8 * i) 8 = Bp i)
      (hV1 : ∀ i < 8, V1.extractLsb' (8 * i) 8 = Bv i)
      (hP2 : ∀ i < 8, P2.extractLsb' (8 * i) 8 = Bp (8 + i))
      (hV2 : ∀ i < 8, V2.extractLsb' (8 * i) 8 = Bv (8 + i)) :
      ((RV64IM.operation_list_effect [.ReadMem A .Double P1, .WriteMem A .Double V1,
          .ReadMem (A + 8) .Double P2, .WriteMem (A + 8) .Double V2] s).hypotheses ↔
        ∀ i < 16, s.mem[A + i]? = some (Bp i)) ∧
      ∃ M : Mem,
        (RV64IM.operation_list_effect [.ReadMem A .Double P1, .WriteMem A .Double V1,
          .ReadMem (A + 8) .Double P2, .WriteMem (A + 8) .Double V2] s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if A ≤ k ∧ k < A + 16 then some (Bv (k - A)) else s.mem[k]? := by
    refine ⟨ ?_, write8 (write8 s.mem A V1) (A + 8) V2, rfl, fun k => ?_ ⟩
    · have p0 := hP1 0 (by omega); have p1 := hP1 1 (by omega); have p2 := hP1 2 (by omega)
      have p3 := hP1 3 (by omega); have p4 := hP1 4 (by omega); have p5 := hP1 5 (by omega)
      have p6 := hP1 6 (by omega); have p7 := hP1 7 (by omega)
      have q0 := hP2 0 (by omega); have q1 := hP2 1 (by omega); have q2 := hP2 2 (by omega)
      have q3 := hP2 3 (by omega); have q4 := hP2 4 (by omega); have q5 := hP2 5 (by omega)
      have q6 := hP2 6 (by omega); have q7 := hP2 7 (by omega)
      simp only [Nat.reduceMul] at p0 p1 p2 p3 p4 p5 p6 p7
      simp only [Nat.reduceMul, Nat.reduceAdd] at q0 q1 q2 q3 q4 q5 q6 q7
      simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect,
        BitVec.extractLsb, true_and, Nat.reduceSub, Nat.reduceAdd, p0, p1, p2, p3, p4, p5, p6, p7,
        q0, q1, q2, q3, q4, q5, q6, q7, Std.ExtHashMap.getElem?_insert, beq_iff_eq, Nat.add_assoc,
        Nat.reduceEqDiff, ↓reduceIte, Nat.left_eq_add, OfNat.ofNat_ne_zero]
      constructor
      · rintro ⟨ ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩, h8, h9, h10, h11, h12, h13, h14, h15 ⟩ i hi
        interval_cases i <;> assumption
      · intro h
        exact ⟨ ⟨ h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
          h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega) ⟩, h 8 (by omega),
          h 9 (by omega), h 10 (by omega), h 11 (by omega), h 12 (by omega), h 13 (by omega),
          h 14 (by omega), h 15 (by omega) ⟩
    · rw [write8_get, write8_get]
      split_ifs with h2 h1 h0 <;> first | omega | rfl | skip
      · rw [hV2 _ (by omega), show 8 + (k - (A + 8)) = k - A by omega]
      · rw [hV1 _ (by omega)]

  /-! ### The dispatch side -/

  private lemma read_byte_effect (s : SailState) (addr : ℕ) (x : BitVec 8) :
      ((RV64IM.operation_list_effect [.ReadMem addr .Byte x] s).hypotheses ↔
        ∀ j < 1, s.mem[addr + j]? = some (x.extractLsb' (8 * j) 8)) ∧
      (RV64IM.operation_list_effect [.ReadMem addr .Byte x] s).state =
        .ok (.Retire_Success ()) s := by
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, true_and]
    refine ⟨ ⟨ fun h j hj => ?_, fun h => by simpa using h 0 (by omega) ⟩, trivial ⟩
    interval_cases j; simpa using h

  private lemma read_half_effect (s : SailState) (addr : ℕ) (x : BitVec 16) :
      ((RV64IM.operation_list_effect [.ReadMem addr .Half x] s).hypotheses ↔
        ∀ j < 2, s.mem[addr + j]? = some (x.extractLsb' (8 * j) 8)) ∧
      (RV64IM.operation_list_effect [.ReadMem addr .Half x] s).state =
        .ok (.Retire_Success ()) s := by
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, true_and,
      BitVec.extractLsb, Nat.reduceSub, Nat.reduceAdd]
    refine ⟨ ⟨ fun ⟨ h0, h1 ⟩ j hj => ?_,
      fun h => ⟨ by simpa using h 0 (by omega), h 1 (by omega) ⟩ ⟩, trivial ⟩
    interval_cases j <;> simpa

  private lemma read_word_effect (s : SailState) (addr : ℕ) (x : BitVec 32) :
      ((RV64IM.operation_list_effect [.ReadMem addr .Word x] s).hypotheses ↔
        ∀ j < 4, s.mem[addr + j]? = some (x.extractLsb' (8 * j) 8)) ∧
      (RV64IM.operation_list_effect [.ReadMem addr .Word x] s).state =
        .ok (.Retire_Success ()) s := by
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, true_and,
      BitVec.extractLsb, Nat.reduceSub, Nat.reduceAdd]
    refine ⟨ ⟨ fun ⟨ h0, h1, h2, h3 ⟩ j hj => ?_,
      fun h => ⟨ by simpa using h 0 (by omega), h 1 (by omega), h 2 (by omega),
        h 3 (by omega) ⟩ ⟩, trivial ⟩
    interval_cases j <;> simpa

  private lemma read_double_effect (s : SailState) (addr : ℕ) (x : BitVec 64) :
      ((RV64IM.operation_list_effect [.ReadMem addr .Double x] s).hypotheses ↔
        ∀ j < 8, s.mem[addr + j]? = some (x.extractLsb' (8 * j) 8)) ∧
      (RV64IM.operation_list_effect [.ReadMem addr .Double x] s).state =
        .ok (.Retire_Success ()) s := by
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, true_and,
      BitVec.extractLsb, Nat.reduceSub, Nat.reduceAdd]
    refine ⟨ ⟨ fun ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ j hj => ?_,
      fun h => ⟨ by simpa using h 0 (by omega), h 1 (by omega), h 2 (by omega),
        h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega) ⟩ ⟩,
      trivial ⟩
    interval_cases j <;> simpa

  private lemma read_any_effect (s : SailState) (addr : ℕ) (w : RV64IM.MemoryWidth) :
      ((RV64IM.operation_list_effect [.ReadMemAny addr w] s).hypotheses ↔
        ∀ j < RV64IM.width_of_mem_width w / 8, (s.mem[addr + j]?).isSome) ∧
      (RV64IM.operation_list_effect [.ReadMemAny addr w] s).state =
        .ok (.Retire_Success ()) s := by
    cases w <;>
      simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, true_and,
        RV64IM.width_of_mem_width, Nat.reduceDiv] <;>
      refine ⟨ ⟨ fun h j hj => ?_, fun h => ?_ ⟩, trivial ⟩
    all_goals first
      | (interval_cases j <;> simp_all)
      | (first
          | exact h 0 (by omega)
          | exact ⟨ by simpa using h 0 (by omega), h 1 (by omega) ⟩
          | exact ⟨ by simpa using h 0 (by omega), h 1 (by omega), h 2 (by omega),
              h 3 (by omega) ⟩
          | exact ⟨ by simpa using h 0 (by omega), h 1 (by omega), h 2 (by omega),
              h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega) ⟩)

  private lemma write_byte_effect (s : SailState) (addr : ℕ) (y : BitVec 8) :
      ((RV64IM.operation_list_effect [.WriteMem addr .Byte y] s).hypotheses ↔ True) ∧
      ∃ M : Mem,
        (RV64IM.operation_list_effect [.WriteMem addr .Byte y] s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if addr ≤ k ∧ k < addr + 1 then some (y.extractLsb' (8 * (k - addr)) 8)
          else s.mem[k]? := by
    refine ⟨ by simp [RV64IM.operation_list_effect, RV64IM.operation_effect], _, rfl, fun k => ?_ ⟩
    simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    split_ifs <;> first | omega | (subst_vars; simp)

  private lemma write_half_effect (s : SailState) (addr : ℕ) (y : BitVec 16) :
      ((RV64IM.operation_list_effect [.WriteMem addr .Half y] s).hypotheses ↔ True) ∧
      ∃ M : Mem,
        (RV64IM.operation_list_effect [.WriteMem addr .Half y] s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if addr ≤ k ∧ k < addr + 2 then some (y.extractLsb' (8 * (k - addr)) 8)
          else s.mem[k]? := by
    refine ⟨ by simp [RV64IM.operation_list_effect, RV64IM.operation_effect], _, rfl, fun k => ?_ ⟩
    simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq, BitVec.extractLsb]
    split_ifs <;> first | omega | (subst_vars; simp)

  private lemma write_word_effect (s : SailState) (addr : ℕ) (y : BitVec 32) :
      ((RV64IM.operation_list_effect [.WriteMem addr .Word y] s).hypotheses ↔ True) ∧
      ∃ M : Mem,
        (RV64IM.operation_list_effect [.WriteMem addr .Word y] s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if addr ≤ k ∧ k < addr + 4 then some (y.extractLsb' (8 * (k - addr)) 8)
          else s.mem[k]? := by
    refine ⟨ by simp [RV64IM.operation_list_effect, RV64IM.operation_effect], _, rfl, fun k => ?_ ⟩
    simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq, BitVec.extractLsb]
    split_ifs <;> first | omega | (subst_vars; simp)

  private lemma write_double_effect (s : SailState) (addr : ℕ) (y : BitVec 64) :
      ((RV64IM.operation_list_effect [.WriteMem addr .Double y] s).hypotheses ↔ True) ∧
      ∃ M : Mem,
        (RV64IM.operation_list_effect [.WriteMem addr .Double y] s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if addr ≤ k ∧ k < addr + 8 then some (y.extractLsb' (8 * (k - addr)) 8)
          else s.mem[k]? :=
    ⟨ by simp [RV64IM.operation_list_effect, RV64IM.operation_effect], write8 s.mem addr y, rfl,
      fun k => write8_get _ _ _ _ ⟩

  /-! ### Both sides together -/

  /-- What the access side reads and the memory it leaves: the bytes `Bp` from `A` on, and the
      bytes `Bv` written back over them. -/
  private def AccessEffect (ops : List RV64IM.Operation) (s : SailState) (A N : ℕ)
      (Bp Bv : ℕ → BitVec 8) : Prop :=
    ((RV64IM.operation_list_effect ops s).hypotheses ↔ ∀ i < N, s.mem[A + i]? = some (Bp i)) ∧
    ∃ M : Mem, (RV64IM.operation_list_effect ops s).state =
        .ok (.Retire_Success ()) { s with mem := M } ∧
      ∀ k, M[k]? = if A ≤ k ∧ k < A + N then some (Bv (k - A)) else s.mem[k]?

  /-- A load: the bytes read are the access's from the offset on, and the access writes back
      what it read. -/
  private lemma flow_load (s : SailState) (ops_acc ops_disp : List RV64IM.Operation)
      (addr A off n N : ℕ) (Bp Bv xb : ℕ → BitVec 8)
      (h_acc : AccessEffect ops_acc s A N Bp Bv)
      (h_disp : ((RV64IM.operation_list_effect ops_disp s).hypotheses ↔
          ∀ j < n, s.mem[addr + j]? = some (xb j)) ∧
        (RV64IM.operation_list_effect ops_disp s).state = .ok (.Retire_Success ()) s)
      (h_addr : addr = A + off) (h_n : off + n ≤ N) (h_x : ∀ j < n, xb j = Bp (off + j))
      (h_v : ∀ i < N, Bv i = Bp i) :
      (RV64IM.operation_list_effect ops_acc s).hypotheses →
        (RV64IM.operation_list_effect ops_disp s).hypotheses ∧
        (RV64IM.operation_list_effect ops_disp s).state =
          (RV64IM.operation_list_effect ops_acc s).state := by
    obtain ⟨ h_hyp, M, h_st, h_M ⟩ := h_acc
    intro h
    rw [h_hyp] at h
    refine ⟨ h_disp.1.2 (fun j hj => ?_), ?_ ⟩
    · rw [h_x j hj, h_addr, Nat.add_assoc]; exact h _ (by omega)
    · rw [h_disp.2, h_st]
      congr 1
      apply eq_with_mem
      ext k : 1
      rw [h_M]
      split_ifs with hk
      · obtain ⟨ i, rfl ⟩ : ∃ i, k = A + i := ⟨ k - A, by omega ⟩
        rw [h i (by omega), Nat.add_sub_cancel_left, h_v i (by omega)]
      · rfl

  /-- A load into `x0`: the bytes read are among the access's, which it writes back as read. -/
  private lemma flow_any (s : SailState) (ops_acc ops_disp : List RV64IM.Operation)
      (addr A off n N : ℕ) (Bp Bv : ℕ → BitVec 8)
      (h_acc : AccessEffect ops_acc s A N Bp Bv)
      (h_disp : ((RV64IM.operation_list_effect ops_disp s).hypotheses ↔
          ∀ j < n, (s.mem[addr + j]?).isSome) ∧
        (RV64IM.operation_list_effect ops_disp s).state = .ok (.Retire_Success ()) s)
      (h_addr : addr = A + off) (h_n : off + n ≤ N) (h_v : ∀ i < N, Bv i = Bp i) :
      (RV64IM.operation_list_effect ops_acc s).hypotheses →
        (RV64IM.operation_list_effect ops_disp s).hypotheses ∧
        (RV64IM.operation_list_effect ops_disp s).state =
          (RV64IM.operation_list_effect ops_acc s).state := by
    obtain ⟨ h_hyp, M, h_st, h_M ⟩ := h_acc
    intro h
    rw [h_hyp] at h
    refine ⟨ h_disp.1.2 (fun j hj => ?_), ?_ ⟩
    · rw [h_addr, Nat.add_assoc, h _ (by omega)]; rfl
    · rw [h_disp.2, h_st]
      congr 1
      apply eq_with_mem
      ext k : 1
      rw [h_M]
      split_ifs with hk
      · obtain ⟨ i, rfl ⟩ : ∃ i, k = A + i := ⟨ k - A, by omega ⟩
        rw [h i (by omega), Nat.add_sub_cancel_left, h_v i (by omega)]
      · rfl

  /-- A store: the access writes back the bytes it read with the stored ones in their place. -/
  private lemma flow_store (s : SailState) (ops_acc ops_disp : List RV64IM.Operation)
      (addr A off n N : ℕ) (Bp Bv yb : ℕ → BitVec 8)
      (h_acc : AccessEffect ops_acc s A N Bp Bv)
      (h_disp : ((RV64IM.operation_list_effect ops_disp s).hypotheses ↔ True) ∧
        ∃ M : Mem, (RV64IM.operation_list_effect ops_disp s).state =
            .ok (.Retire_Success ()) { s with mem := M } ∧
          ∀ k, M[k]? = if addr ≤ k ∧ k < addr + n then some (yb (k - addr)) else s.mem[k]?)
      (h_addr : addr = A + off) (h_n : off + n ≤ N)
      (h_v : ∀ i < N, Bv i = if off ≤ i ∧ i < off + n then yb (i - off) else Bp i) :
      (RV64IM.operation_list_effect ops_acc s).hypotheses →
        (RV64IM.operation_list_effect ops_disp s).hypotheses ∧
        (RV64IM.operation_list_effect ops_disp s).state =
          (RV64IM.operation_list_effect ops_acc s).state := by
    obtain ⟨ h_hyp, M, h_st, h_M ⟩ := h_acc
    obtain ⟨ h_dh, Md, h_dst, h_Md ⟩ := h_disp
    intro h
    rw [h_hyp] at h
    refine ⟨ h_dh.2 trivial, ?_ ⟩
    rw [h_dst, h_st]
    congr 2
    ext k : 1
    rw [h_M, h_Md]
    subst h_addr
    split_ifs with h1 h2 h2
    · rw [h_v (k - A) (by omega), if_pos (by omega), show k - A - off = k - (A + off) by omega]
    · omega
    · obtain ⟨ i, rfl ⟩ : ∃ i, k = A + i := ⟨ k - A, by omega ⟩
      rw [h i (by omega), Nat.add_sub_cancel_left, h_v i (by omega), if_neg (by omega)]
    · rfl

  /-! ### The row's bytes -/

  /-- The address `b + c` the memory dispatch names. -/
  private def dispatch_addr [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      ℕ :=
    let i := air.cols.instruction
    (U64w.toBV #v[i.op_b_value_0 row 0, i.op_b_value_1 row 0, i.op_b_value_2 row 0,
        i.op_b_value_3 row 0] +
      U64w.toBV #v[i.op_c_value_0 row 0, i.op_c_value_1 row 0, i.op_c_value_2 row 0,
        i.op_c_value_3 row 0]).toNat

  /-- The sixteen bytes of the two double words before the access, `w` in `constraints.rs`, as
      numbers: each piece's low byte and its high byte `(x - lo) / 256`. -/
  private def wnat [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) (i : ℕ) : ℕ :=
    let v := air.cols
    [(v.first_bytes.low_bytes_0 row 0).val,
     (high_byte (v.first.prev_value_0 row 0) (v.first_bytes.low_bytes_0 row 0)).val,
     (v.first_bytes.low_bytes_1 row 0).val,
     (high_byte (v.first.prev_value_1 row 0) (v.first_bytes.low_bytes_1 row 0)).val,
     (v.first_bytes.low_bytes_2 row 0).val,
     (high_byte (v.first.prev_value_2 row 0) (v.first_bytes.low_bytes_2 row 0)).val,
     (v.first_bytes.low_bytes_3 row 0).val,
     (high_byte (v.first.prev_value_3 row 0) (v.first_bytes.low_bytes_3 row 0)).val,
     (v.second_bytes.low_bytes_0 row 0).val,
     (high_byte (v.second.prev_value_0 row 0) (v.second_bytes.low_bytes_0 row 0)).val,
     (v.second_bytes.low_bytes_1 row 0).val,
     (high_byte (v.second.prev_value_1 row 0) (v.second_bytes.low_bytes_1 row 0)).val,
     (v.second_bytes.low_bytes_2 row 0).val,
     (high_byte (v.second.prev_value_2 row 0) (v.second_bytes.low_bytes_2 row 0)).val,
     (v.second_bytes.low_bytes_3 row 0).val,
     (high_byte (v.second.prev_value_3 row 0) (v.second_bytes.low_bytes_3 row 0)).val].getD i 0

  /-- `wnat` byte by byte. -/
  private lemma wnat_eqs [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      let v := air.cols
      wnat air row 0 = (v.first_bytes.low_bytes_0 row 0).val ∧
      wnat air row 1 = (high_byte (v.first.prev_value_0 row 0) (v.first_bytes.low_bytes_0 row 0)).val ∧
      wnat air row 2 = (v.first_bytes.low_bytes_1 row 0).val ∧
      wnat air row 3 = (high_byte (v.first.prev_value_1 row 0) (v.first_bytes.low_bytes_1 row 0)).val ∧
      wnat air row 4 = (v.first_bytes.low_bytes_2 row 0).val ∧
      wnat air row 5 = (high_byte (v.first.prev_value_2 row 0) (v.first_bytes.low_bytes_2 row 0)).val ∧
      wnat air row 6 = (v.first_bytes.low_bytes_3 row 0).val ∧
      wnat air row 7 = (high_byte (v.first.prev_value_3 row 0) (v.first_bytes.low_bytes_3 row 0)).val ∧
      wnat air row 8 = (v.second_bytes.low_bytes_0 row 0).val ∧
      wnat air row 9 = (high_byte (v.second.prev_value_0 row 0) (v.second_bytes.low_bytes_0 row 0)).val ∧
      wnat air row 10 = (v.second_bytes.low_bytes_1 row 0).val ∧
      wnat air row 11 = (high_byte (v.second.prev_value_1 row 0) (v.second_bytes.low_bytes_1 row 0)).val ∧
      wnat air row 12 = (v.second_bytes.low_bytes_2 row 0).val ∧
      wnat air row 13 = (high_byte (v.second.prev_value_2 row 0) (v.second_bytes.low_bytes_2 row 0)).val ∧
      wnat air row 14 = (v.second_bytes.low_bytes_3 row 0).val ∧
      wnat air row 15 = (high_byte (v.second.prev_value_3 row 0) (v.second_bytes.low_bytes_3 row 0)).val := by
    simp only [wnat, List.getD_cons_succ, List.getD_cons_zero, and_self]

  /-- Two bytes make a 16-bit piece, as numbers. -/
  private lemma limb_val {x y : FKB} (hx : x.val < 256) (hy : y.val < 256) :
      (x + y * 256).val = x.val + 256 * y.val := by
    have v256 : (256 : FKB).val = 256 := rfl
    have hm : (y * 256).val = y.val * 256 := by
      rw [val_mul_of_lt (by rw [v256]; omega), v256]
    rw [val_add_of_lt (by rw [hm]; omega), hm]
    ring

  /-- On a real row the window's bytes are bytes: the first double word's always, the second's
      on a row that crosses. -/
  private lemma wnat_lt
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    (∀ i < 8, wnat air row i < 256) ∧ (air.cols.cross row 0 = 1 → ∀ i < 16, wnat air row i < 256)
  := by
    obtain ⟨ -, -, -, -, -, -, ⟨ ⟨ l0, h0 ⟩, ⟨ l1, h1 ⟩, ⟨ l2, h2 ⟩, ⟨ l3, h3 ⟩ ⟩, h_second, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 ⟩ := wnat_eqs air row
    refine ⟨ fun i hi => ?_, fun hc i hi => ?_ ⟩
    · interval_cases i <;> simp only [w0, w1, w2, w3, w4, w5, w6, w7] <;> with_reducible assumption
    · obtain ⟨ ⟨ m0, n0 ⟩, ⟨ m1, n1 ⟩, ⟨ m2, n2 ⟩, ⟨ m3, n3 ⟩ ⟩ := h_second hc
      interval_cases i <;>
        simp only [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] <;>
        with_reducible assumption


  /-- On a real row, with `off` the address's low three bits: `seen_byte` is the window's byte
      `off`, each `seen_l` its bytes `off + 2l` and `off + 2l + 1` where those lie in the first
      double word or the row crosses (constraints 32 to 36), and the three sums of offset flags
      that constraint 26 uses say whether the offset is 7, at least 5, at least 1. -/
  private lemma seen_vals
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols
    let off := dispatch_addr air row % 8
    (v.seen_byte row 0).val = wnat air row off ∧
    ((off + 2 ≤ 8 ∨ v.cross row 0 = 1) →
      (v.seen_0 row 0).val = wnat air row off + 256 * wnat air row (off + 1)) ∧
    ((off + 4 ≤ 8 ∨ v.cross row 0 = 1) →
      (v.seen_1 row 0).val = wnat air row (off + 2) + 256 * wnat air row (off + 3)) ∧
    ((off + 6 ≤ 8 ∨ v.cross row 0 = 1) →
      (v.seen_2 row 0).val = wnat air row (off + 4) + 256 * wnat air row (off + 5)) ∧
    ((off + 8 ≤ 8 ∨ v.cross row 0 = 1) →
      (v.seen_3 row 0).val = wnat air row (off + 6) + 256 * wnat air row (off + 7)) ∧
    v.offset_7 row 0 = (if 7 ≤ off then 1 else 0) ∧
    v.offset_5 row 0 + v.offset_6 row 0 + v.offset_7 row 0 = (if 5 ≤ off then 1 else 0) ∧
    v.offset_1 row 0 + v.offset_2 row 0 + v.offset_3 row 0 + v.offset_4 row 0 +
      v.offset_5 row 0 + v.offset_6 row 0 + v.offset_7 row 0 = (if 1 ≤ off then 1 else 0)
  := by
    obtain ⟨ -, -, -, -, -, -, ⟨ ⟨ l0, h0 ⟩, ⟨ l1, h1 ⟩, ⟨ l2, h2 ⟩, ⟨ l3, h3 ⟩ ⟩, h_second, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_off := (aligned_address air row h_ext_asm h_wf_asm h_constraints h_mem).1
    have h_cases := offset_cases air row h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, c32, c33, c34, c35, c36, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_32, constraint_33, constraint_34, constraint_35, constraint_36,
      sub_eq_zero] at c32 c33 c34 c35 c36
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 ⟩ :=
      wnat_eqs air row
    clear h_ext_asm h_wf_asm h_constraints h_mem
    dsimp only at h_off w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
    change _ = dispatch_addr air row % 8 at h_off
    generalize dispatch_addr air row % 8 = off at h_off ⊢
    rcases h_cases with h | h | h | h | h | h | h | h <;>
      simp only [offsets, List.cons.injEq, and_true] at h <;>
      obtain ⟨ o0, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
      simp only [o0, o1, o2, o3, o4, o5, o6, o7, zero_mul, one_mul, zero_add, add_zero]
        at c32 c33 c34 c35 c36 h_off ⊢ <;>
      norm_num at h_off <;>
      subst h_off <;>
      simp only [Nat.reduceAdd, Nat.reduceLeDiff, true_or, false_or, true_implies, ↓reduceIte,
        w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, and_true] <;>
      repeat' apply And.intro
    all_goals
      (try intro hc)
      first
        | (rw [c36])
        | (rw [c32]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
        | (rw [c33]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
        | (rw [c34]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
        | (rw [c35]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
        | (obtain ⟨ ⟨ m0, n0 ⟩, ⟨ m1, n1 ⟩, ⟨ m2, n2 ⟩, ⟨ m3, n3 ⟩ ⟩ := h_second hc
           first
            | (rw [c32]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
            | (rw [c33]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
            | (rw [c34]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
            | (rw [c35]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption)))

  /-- The eight bytes of `op_a`, `r` in `constraints.rs`, as numbers. -/
  private def rnat [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) (i : ℕ) : ℕ :=
    let v := air.cols
    [(v.value_bytes.low_bytes_0 row 0).val,
     (high_byte (v.instruction.op_a_value_0 row 0) (v.value_bytes.low_bytes_0 row 0)).val,
     (v.value_bytes.low_bytes_1 row 0).val,
     (high_byte (v.instruction.op_a_value_1 row 0) (v.value_bytes.low_bytes_1 row 0)).val,
     (v.value_bytes.low_bytes_2 row 0).val,
     (high_byte (v.instruction.op_a_value_2 row 0) (v.value_bytes.low_bytes_2 row 0)).val,
     (v.value_bytes.low_bytes_3 row 0).val,
     (high_byte (v.instruction.op_a_value_3 row 0) (v.value_bytes.low_bytes_3 row 0)).val].getD i 0

  /-- `rnat` byte by byte. -/
  private lemma rnat_eqs [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      let v := air.cols
      rnat air row 0 = (v.value_bytes.low_bytes_0 row 0).val ∧
      rnat air row 1 =
        (high_byte (v.instruction.op_a_value_0 row 0) (v.value_bytes.low_bytes_0 row 0)).val ∧
      rnat air row 2 = (v.value_bytes.low_bytes_1 row 0).val ∧
      rnat air row 3 =
        (high_byte (v.instruction.op_a_value_1 row 0) (v.value_bytes.low_bytes_1 row 0)).val ∧
      rnat air row 4 = (v.value_bytes.low_bytes_2 row 0).val ∧
      rnat air row 5 =
        (high_byte (v.instruction.op_a_value_2 row 0) (v.value_bytes.low_bytes_2 row 0)).val ∧
      rnat air row 6 = (v.value_bytes.low_bytes_3 row 0).val ∧
      rnat air row 7 =
        (high_byte (v.instruction.op_a_value_3 row 0) (v.value_bytes.low_bytes_3 row 0)).val := by
    simp only [rnat, List.getD_cons_succ, List.getD_cons_zero, and_self]

  /-- The store flags of a row that stores `n` bytes, `n = 0` for a load. -/
  private def StoreWidth [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ)
      (n : ℕ) : Prop :=
    let i := air.cols.instruction
    (n = 0 ∧ i.is_sb row 0 = 0 ∧ i.is_sh row 0 = 0 ∧ i.is_sw row 0 = 0 ∧ i.is_sd row 0 = 0) ∨
    (n = 1 ∧ i.is_sb row 0 = 1 ∧ i.is_sh row 0 = 0 ∧ i.is_sw row 0 = 0 ∧ i.is_sd row 0 = 0) ∨
    (n = 2 ∧ i.is_sb row 0 = 0 ∧ i.is_sh row 0 = 1 ∧ i.is_sw row 0 = 0 ∧ i.is_sd row 0 = 0) ∨
    (n = 4 ∧ i.is_sb row 0 = 0 ∧ i.is_sh row 0 = 0 ∧ i.is_sw row 0 = 1 ∧ i.is_sd row 0 = 0) ∨
    (n = 8 ∧ i.is_sb row 0 = 0 ∧ i.is_sh row 0 = 0 ∧ i.is_sw row 0 = 0 ∧ i.is_sd row 0 = 1)

  /-- The window after the access: byte `i` is byte `i - off` of `op_a` where a store of `n`
      bytes covers it, and keeps its value elsewhere. -/
  private def wrnat [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) (n i : ℕ) :
      ℕ :=
    if dispatch_addr air row % 8 ≤ i ∧ i < dispatch_addr air row % 8 + n then
      rnat air row (i - dispatch_addr air row % 8)
    else wnat air row i

  /-- On a real row that stores `n` bytes (`n = 0` on a load), the pieces of each double word
      written back are the window's bytes after the access (constraints 47 to 54); the second
      double word's on a row that crosses. -/
  private lemma written_vals
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (n : ℕ)
    (h_n : StoreWidth air row n)
  :
    let v := air.cols
    (v.first.access.value_0 row 0).val = wrnat air row n 0 + 256 * wrnat air row n 1 ∧
    (v.first.access.value_1 row 0).val = wrnat air row n 2 + 256 * wrnat air row n 3 ∧
    (v.first.access.value_2 row 0).val = wrnat air row n 4 + 256 * wrnat air row n 5 ∧
    (v.first.access.value_3 row 0).val = wrnat air row n 6 + 256 * wrnat air row n 7 ∧
    (v.cross row 0 = 1 →
      (v.second.access.value_0 row 0).val = wrnat air row n 8 + 256 * wrnat air row n 9 ∧
      (v.second.access.value_1 row 0).val = wrnat air row n 10 + 256 * wrnat air row n 11 ∧
      (v.second.access.value_2 row 0).val = wrnat air row n 12 + 256 * wrnat air row n 13 ∧
      (v.second.access.value_3 row 0).val = wrnat air row n 14 + 256 * wrnat air row n 15)
  := by
    obtain ⟨ -, -, -, -, -, -, ⟨ ⟨ l0, h0 ⟩, ⟨ l1, h1 ⟩, ⟨ l2, h2 ⟩, ⟨ l3, h3 ⟩ ⟩, h_second,
      h_value ⟩ := bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    have h_off := (aligned_address air row h_ext_asm h_wf_asm h_constraints h_mem).1
    have h_cases := offset_cases air row h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c47, c48, c49, c50, c51,
      c52, c53, c54, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_47, constraint_48, constraint_49, constraint_50, constraint_51,
      constraint_52, constraint_53, constraint_54, sub_eq_zero]
      at c47 c48 c49 c50 c51 c52 c53 c54
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 ⟩ :=
      wnat_eqs air row
    obtain ⟨ r0, r1, r2, r3, r4, r5, r6, r7 ⟩ := rnat_eqs air row
    clear h_ext_asm h_wf_asm h_constraints h_mem
    unfold wrnat
    try dsimp only at h_off w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 ⊢
    try dsimp only at r0 r1 r2 r3 r4 r5 r6 r7
    change _ = dispatch_addr air row % 8 at h_off
    generalize dispatch_addr air row % 8 = off at h_off ⊢
    unfold StoreWidth at h_n
    rcases h_n with ⟨ rfl, f7, f8, f9, f10 ⟩ | ⟨ rfl, f7, f8, f9, f10 ⟩ | ⟨ rfl, f7, f8, f9, f10 ⟩ |
        ⟨ rfl, f7, f8, f9, f10 ⟩ | ⟨ rfl, f7, f8, f9, f10 ⟩ <;>
      simp only [f7, f8, f9, f10] at h_value <;>
      norm_num at h_value <;>
      (try obtain ⟨ ⟨ s0, t0 ⟩, ⟨ s1, t1 ⟩, ⟨ s2, t2 ⟩, ⟨ s3, t3 ⟩ ⟩ := h_value) <;>
      rcases h_cases with h | h | h | h | h | h | h | h <;>
      simp only [offsets, List.cons.injEq, and_true] at h <;>
      obtain ⟨ o0, o1, o2, o3, o4, o5, o6, o7 ⟩ := h <;>
      simp only [f7, f8, f9, f10, o0, o1, o2, o3, o4, o5, o6, o7, zero_mul, mul_zero, one_mul,
        mul_one, zero_add, add_zero, add_sub_cancel] at c47 c48 c49 c50 c51 c52 c53 c54 <;>
      simp only [o1, o2, o3, o4, o5, o6, o7, zero_mul, one_mul, zero_add, add_zero] at h_off <;>
      norm_num at h_off <;>
      subst h_off <;>
      simp (config := { decide := true }) only [Nat.reduceSub, ↓reduceIte,
        w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
        r0, r1, r2, r3, r4, r5, r6, r7] <;>
      refine ⟨ ?_, ?_, ?_, ?_, fun hc => ?_ ⟩
    all_goals first
      | (rw [c47]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
      | (rw [c49]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
      | (rw [c51]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
      | (rw [c53]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))
      | (obtain ⟨ ⟨ m0, n0 ⟩, ⟨ m1, n1 ⟩, ⟨ m2, n2 ⟩, ⟨ m3, n3 ⟩ ⟩ := h_second hc
         refine ⟨ ?_, ?_, ?_, ?_ ⟩
         · rw [c48]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption)
         · rw [c50]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption)
         · rw [c52]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption)
         · rw [c54]; with_reducible exact limb_val (by with_reducible assumption) (by with_reducible assumption))

  /-- A 16-bit piece split into a low byte and the high byte `(x - lo) / 256`, both bytes, is
      their sum. -/
  private lemma byte_split {x lo : FKB} (h_lo : lo.val < 256) (h_hi : (high_byte x lo).val < 256) :
      x.val = lo.val + 256 * (high_byte x lo).val := by
    have e : x = lo + high_byte x lo * 256 := by
      simp only [high_byte]
      rw [mul_assoc, show (2122383361 : FKB) * 256 = 1 from rfl]; ring
    conv_lhs => rw [e]
    rw [limb_val h_lo h_hi]

  /-- The bytes of a double word whose pieces are the byte pairs of `b` from `k` on. -/
  private lemma toBV_byte_eq (p0 p1 p2 p3 : FKB) (b : ℕ → ℕ) (k : ℕ)
      (hb : ∀ i < 8, b (k + i) < 256)
      (h0 : p0.val = b (k + 0) + 256 * b (k + 1)) (h1 : p1.val = b (k + 2) + 256 * b (k + 3))
      (h2 : p2.val = b (k + 4) + 256 * b (k + 5)) (h3 : p3.val = b (k + 6) + 256 * b (k + 7)) :
      ∀ i < 8, (U64w.toBV #v[p0, p1, p2, p3]).extractLsb' (8 * i) 8 = BitVec.ofNat 8 (b (k + i)) := by
    have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
    have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
    have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
    simp only [Nat.add_zero] at b0 h0
    intro i hi
    interval_cases i <;> apply BitVec.eq_of_toNat_eq <;>
      simp [U64w.toBV_toNat, U64w.toNat, Nat.shiftRight_eq_div_pow] <;> omega

  /-- On a real row the window's bytes after the access are bytes. -/
  private lemma wrnat_lt
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (n : ℕ)
    (h_n : StoreWidth air row n)
  :
    (∀ i < 8, wrnat air row n i < 256) ∧
    (air.cols.cross row 0 = 1 → ∀ i < 16, wrnat air row n i < 256)
  := by
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, h_value ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    have hn8 : n ≤ 8 := by
      unfold StoreWidth at h_n
      rcases h_n with ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ <;> omega
    have hr : 0 < n → ∀ j < 8, rnat air row j < 256 := by
      intro hn j hj
      have hs : air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
          air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1 := by
        unfold StoreWidth at h_n
        rcases h_n with ⟨ rfl, f7, f8, f9, f10 ⟩ | ⟨ rfl, f7, f8, f9, f10 ⟩ |
            ⟨ rfl, f7, f8, f9, f10 ⟩ | ⟨ rfl, f7, f8, f9, f10 ⟩ | ⟨ rfl, f7, f8, f9, f10 ⟩ <;>
          omega
      obtain ⟨ ⟨ s0, t0 ⟩, ⟨ s1, t1 ⟩, ⟨ s2, t2 ⟩, ⟨ s3, t3 ⟩ ⟩ := h_value hs
      obtain ⟨ r0, r1, r2, r3, r4, r5, r6, r7 ⟩ := rnat_eqs air row
      interval_cases j <;> simp only [r0, r1, r2, r3, r4, r5, r6, r7] <;> with_reducible assumption
    unfold wrnat
    refine ⟨ fun i hi => ?_, fun hc i hi => ?_ ⟩ <;> split_ifs with h
    · exact hr (by omega) _ (by omega)
    · exact hw8 i hi
    · exact hr (by omega) _ (by omega)
    · exact hw16 hc i hi

  /-- The double word before the first access and after it, and the same for the second. -/
  private abbrev P1 [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      BitVec 64 :=
    U64w.toBV #v[air.cols.first.prev_value_0 row 0, air.cols.first.prev_value_1 row 0,
      air.cols.first.prev_value_2 row 0, air.cols.first.prev_value_3 row 0]

  private abbrev V1 [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      BitVec 64 :=
    U64w.toBV #v[air.cols.first.access.value_0 row 0, air.cols.first.access.value_1 row 0,
      air.cols.first.access.value_2 row 0, air.cols.first.access.value_3 row 0]

  private abbrev P2 [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      BitVec 64 :=
    U64w.toBV #v[air.cols.second.prev_value_0 row 0, air.cols.second.prev_value_1 row 0,
      air.cols.second.prev_value_2 row 0, air.cols.second.prev_value_3 row 0]

  private abbrev V2 [Field ExtF] (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      BitVec 64 :=
    U64w.toBV #v[air.cols.second.access.value_0 row 0, air.cols.second.access.value_1 row 0,
      air.cols.second.access.value_2 row 0, air.cols.second.access.value_3 row 0]

  /-- On a real row the State messages are the double-word read and write back at the aligned
      address `A`, and on a row that crosses those at `A + 8`. Each address is at least `2^16`,
      so `bus_operations` reads it as memory, not as a register. -/
  private lemma access_ops
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    (air.cols.cross row 0 = 0 ∧
      RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] } =
        [ .ReadMem (dispatch_addr air row - dispatch_addr air row % 8) .Double (P1 air row),
          .WriteMem (dispatch_addr air row - dispatch_addr air row % 8) .Double (V1 air row) ]) ∨
    (air.cols.cross row 0 = 1 ∧
      RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] } =
        [ .ReadMem (dispatch_addr air row - dispatch_addr air row % 8) .Double (P1 air row),
          .WriteMem (dispatch_addr air row - dispatch_addr air row % 8) .Double (V1 air row),
          .ReadMem (dispatch_addr air row - dispatch_addr air row % 8 + 8) .Double (P2 air row),
          .WriteMem (dispatch_addr air row - dispatch_addr air row % 8 + 8) .Double
            (V2 air row) ])
  := by
    obtain ⟨ -, -, -, h_al, h_next ⟩ :=
      aligned_address air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_pos ⟩ := address air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, c31, - ⟩ := constraints_of_allHold air row h_constraints
    simp only [constraint_31] at c31
    simp only [is_memory] at h_mem
    try dsimp only at h_al h_next
    change _ = dispatch_addr air row - dispatch_addr air row % 8 at h_al
    rcases bool_cases c31 with hx | hx
    · left
      refine ⟨ hx, ?_ ⟩
      rw [← h_al]
      have h_ge : ¬ ((air.cols.addr_word_0 row 0 - (air.cols.offset_1 row 0 +
          air.cols.offset_2 row 0 * 2 + air.cols.offset_3 row 0 * 3 + air.cols.offset_4 row 0 * 4 +
          air.cols.offset_5 row 0 * 5 + air.cols.offset_6 row 0 * 6 +
          air.cols.offset_7 row 0 * 7)).val + 65536 * (air.cols.addr_word_1 row 0).val < 32) := by
        omega
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses, h_mem,
        hx, h_ge]
    · right
      obtain ⟨ -, -, h_n ⟩ := h_next hx
      change _ = dispatch_addr air row - dispatch_addr air row % 8 + 8 at h_n
      refine ⟨ hx, ?_ ⟩
      have h_ge : ¬ ((air.cols.addr_word_0 row 0 - (air.cols.offset_1 row 0 +
          air.cols.offset_2 row 0 * 2 + air.cols.offset_3 row 0 * 3 + air.cols.offset_4 row 0 * 4 +
          air.cols.offset_5 row 0 * 5 + air.cols.offset_6 row 0 * 6 +
          air.cols.offset_7 row 0 * 7)).val + 65536 * (air.cols.addr_word_1 row 0).val < 32) := by
        omega
      have h_ge2 : ¬ ((air.cols.addr_word_0 row 0 - (air.cols.offset_1 row 0 +
          air.cols.offset_2 row 0 * 2 + air.cols.offset_3 row 0 * 3 + air.cols.offset_4 row 0 * 4 +
          air.cols.offset_5 row 0 * 5 + air.cols.offset_6 row 0 * 6 +
          air.cols.offset_7 row 0 * 7) + 8 - air.cols.next_carry row 0 * 65536).val +
          65536 * (air.cols.addr_word_1 row 0 + air.cols.next_carry row 0).val < 32) := by
        omega
      rw [← h_n, ← h_al]
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses, h_mem,
        hx, h_ge, h_ge2]

  /-- What the State messages do on a real row that stores `n` bytes (`n = 0` on a load): they
      read the window's bytes from the aligned address on and write back the window after the
      access, over one double word or, on a row that crosses, two. -/
  private lemma access_effect
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (s : SailState)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (n : ℕ)
    (h_n : StoreWidth air row n)
  :
    (air.cols.cross row 0 = 0 ∧
      AccessEffect (RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
        s (dispatch_addr air row - dispatch_addr air row % 8) 8
        (fun i => BitVec.ofNat 8 (wnat air row i)) (fun i => BitVec.ofNat 8 (wrnat air row n i))) ∨
    (air.cols.cross row 0 = 1 ∧
      AccessEffect (RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
        s (dispatch_addr air row - dispatch_addr air row % 8) 16
        (fun i => BitVec.ofNat 8 (wnat air row i)) (fun i => BitVec.ofNat 8 (wrnat air row n i)))
  := by
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ hv8, hv16 ⟩ := wrnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem n h_n
    obtain ⟨ e0, e1, e2, e3, h_sec ⟩ :=
      written_vals air row h_ext_asm h_wf_asm h_constraints h_mem n h_n
    obtain ⟨ -, -, -, -, -, -, ⟨ ⟨ l0, h0 ⟩, ⟨ l1, h1 ⟩, ⟨ l2, h2 ⟩, ⟨ l3, h3 ⟩ ⟩, h_second, - ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 ⟩ :=
      wnat_eqs air row
    have hP1 : ∀ i < 8, (P1 air row).extractLsb' (8 * i) 8 = BitVec.ofNat 8 (wnat air row i) := by
      intro i hi
      have h := toBV_byte_eq _ _ _ _ (wnat air row) 0 (fun j hj => hw8 _ (by omega))
        (by simp only [Nat.add_zero, Nat.zero_add, w0, w1]; exact byte_split l0 h0)
        (by simp only [Nat.zero_add, w2, w3]; exact byte_split l1 h1)
        (by simp only [Nat.zero_add, w4, w5]; exact byte_split l2 h2)
        (by simp only [Nat.zero_add, w6, w7]; exact byte_split l3 h3) i hi
      rwa [Nat.zero_add] at h
    have hV1 : ∀ i < 8,
        (V1 air row).extractLsb' (8 * i) 8 = BitVec.ofNat 8 (wrnat air row n i) := by
      intro i hi
      have h := toBV_byte_eq _ _ _ _ (wrnat air row n) 0 (fun j hj => hv8 _ (by omega))
        (by simp only [Nat.add_zero, Nat.zero_add]; exact e0)
        (by simp only [Nat.zero_add]; exact e1)
        (by simp only [Nat.zero_add]; exact e2)
        (by simp only [Nat.zero_add]; exact e3) i hi
      rwa [Nat.zero_add] at h
    rcases access_ops air row h_ext_asm h_wf_asm h_constraints h_mem with
      ⟨ hx, hops ⟩ | ⟨ hx, hops ⟩
    · left
      refine ⟨ hx, ?_ ⟩
      rw [hops]
      exact access2_effect s _ _ _ _ _ hP1 hV1
    · right
      refine ⟨ hx, ?_ ⟩
      obtain ⟨ ⟨ m0, n0 ⟩, ⟨ m1, n1 ⟩, ⟨ m2, n2 ⟩, ⟨ m3, n3 ⟩ ⟩ := h_second hx
      obtain ⟨ e4, e5, e6, e7 ⟩ := h_sec hx
      have hP2 : ∀ i < 8,
          (P2 air row).extractLsb' (8 * i) 8 = BitVec.ofNat 8 (wnat air row (8 + i)) :=
        toBV_byte_eq _ _ _ _ (wnat air row) 8 (fun j hj => hw16 hx _ (by omega))
          (by simp only [Nat.reduceAdd, w8, w9]; exact byte_split m0 n0)
          (by simp only [Nat.reduceAdd, w10, w11]; exact byte_split m1 n1)
          (by simp only [Nat.reduceAdd, w12, w13]; exact byte_split m2 n2)
          (by simp only [Nat.reduceAdd, w14, w15]; exact byte_split m3 n3)
      have hV2 : ∀ i < 8,
          (V2 air row).extractLsb' (8 * i) 8 = BitVec.ofNat 8 (wrnat air row n (8 + i)) :=
        toBV_byte_eq _ _ _ _ (wrnat air row n) 8 (fun j hj => hv16 hx _ (by omega))
          (by simp only [Nat.reduceAdd]; exact e4)
          (by simp only [Nat.reduceAdd]; exact e5)
          (by simp only [Nat.reduceAdd]; exact e6)
          (by simp only [Nat.reduceAdd]; exact e7)
      rw [hops]
      exact access4_effect s _ _ _ _ _ _ _ hP1 hV1 hP2 hV2

  /-! ### The row's data flow, per direction -/

  /-- A load row: the dispatch reads `w` bytes `xb`, the window's from the offset on. -/
  private lemma row_load
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (s : SailState)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (w : ℕ) (ops : List RV64IM.Operation) (xb : ℕ → BitVec 8)
    (h_disp : ((RV64IM.operation_list_effect ops s).hypotheses ↔
        ∀ j < w, s.mem[dispatch_addr air row + j]? = some (xb j)) ∧
      (RV64IM.operation_list_effect ops s).state = .ok (.Retire_Success ()) s)
    (h_w : w ≤ 8)
    (h_fit : air.cols.cross row 0 = 0 → dispatch_addr air row % 8 + w ≤ 8)
    (h_x : ∀ j < w, xb j = BitVec.ofNat 8 (wnat air row (dispatch_addr air row % 8 + j)))
    (h_load : StoreWidth air row 0)
  :
    (RV64IM.operation_list_effect (RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
        s).hypotheses →
      (RV64IM.operation_list_effect ops s).hypotheses ∧
      (RV64IM.operation_list_effect ops s).state =
        (RV64IM.operation_list_effect (RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
          s).state
  := by
    have h_v : ∀ i, BitVec.ofNat 8 (wrnat air row 0 i) = BitVec.ofNat 8 (wnat air row i) := by
      intro i; unfold wrnat; rw [if_neg (by omega)]
    have h_addr : dispatch_addr air row =
        dispatch_addr air row - dispatch_addr air row % 8 + dispatch_addr air row % 8 := by omega
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    rcases access_effect air row s h_ext_asm h_wf_asm h_constraints h_mem 0 h_load with
      ⟨ hx, h_acc ⟩ | ⟨ hx, h_acc ⟩
    · exact flow_load s _ ops _ _ _ w 8 _ _ xb h_acc h_disp h_addr (h_fit hx) h_x
        (fun i _ => h_v i)
    · exact flow_load s _ ops _ _ _ w 16 _ _ xb h_acc h_disp h_addr (by omega) h_x
        (fun i _ => h_v i)

  /-- A load into `x0`: the dispatch reads `w` bytes, whatever they are. -/
  private lemma row_any
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (s : SailState)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (w : ℕ) (ops : List RV64IM.Operation)
    (h_disp : ((RV64IM.operation_list_effect ops s).hypotheses ↔
        ∀ j < w, (s.mem[dispatch_addr air row + j]?).isSome) ∧
      (RV64IM.operation_list_effect ops s).state = .ok (.Retire_Success ()) s)
    (h_w : w ≤ 8)
    (h_fit : air.cols.cross row 0 = 0 → dispatch_addr air row % 8 + w ≤ 8)
    (h_load : StoreWidth air row 0)
  :
    (RV64IM.operation_list_effect (RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
        s).hypotheses →
      (RV64IM.operation_list_effect ops s).hypotheses ∧
      (RV64IM.operation_list_effect ops s).state =
        (RV64IM.operation_list_effect (RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
          s).state
  := by
    have h_v : ∀ i, BitVec.ofNat 8 (wrnat air row 0 i) = BitVec.ofNat 8 (wnat air row i) := by
      intro i; unfold wrnat; rw [if_neg (by omega)]
    have h_addr : dispatch_addr air row =
        dispatch_addr air row - dispatch_addr air row % 8 + dispatch_addr air row % 8 := by omega
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    rcases access_effect air row s h_ext_asm h_wf_asm h_constraints h_mem 0 h_load with
      ⟨ hx, h_acc ⟩ | ⟨ hx, h_acc ⟩
    · exact flow_any s _ ops _ _ _ w 8 _ _ h_acc h_disp h_addr (h_fit hx) (fun i _ => h_v i)
    · exact flow_any s _ ops _ _ _ w 16 _ _ h_acc h_disp h_addr (by omega) (fun i _ => h_v i)

  /-- A store row of `n` bytes: the dispatch writes `yb`, the bytes of `op_a`. -/
  private lemma row_store
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (s : SailState)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (n : ℕ) (h_n : StoreWidth air row n) (ops : List RV64IM.Operation) (yb : ℕ → BitVec 8)
    (h_disp : ((RV64IM.operation_list_effect ops s).hypotheses ↔ True) ∧
      ∃ M : Mem, (RV64IM.operation_list_effect ops s).state =
          .ok (.Retire_Success ()) { s with mem := M } ∧
        ∀ k, M[k]? = if dispatch_addr air row ≤ k ∧ k < dispatch_addr air row + n then
          some (yb (k - dispatch_addr air row)) else s.mem[k]?)
    (h_fit : air.cols.cross row 0 = 0 → dispatch_addr air row % 8 + n ≤ 8)
    (h_y : ∀ j < n, yb j = BitVec.ofNat 8 (rnat air row j))
  :
    (RV64IM.operation_list_effect (RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
        s).hypotheses →
      (RV64IM.operation_list_effect ops s).hypotheses ∧
      (RV64IM.operation_list_effect ops s).state =
        (RV64IM.operation_list_effect (RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] })
          s).state
  := by
    have hn8 : n ≤ 8 := by
      unfold StoreWidth at h_n
      rcases h_n with ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ | ⟨ rfl, - ⟩ <;> omega
    have h_v : ∀ i, BitVec.ofNat 8 (wrnat air row n i) =
        if dispatch_addr air row % 8 ≤ i ∧ i < dispatch_addr air row % 8 + n then
          yb (i - dispatch_addr air row % 8) else BitVec.ofNat 8 (wnat air row i) := by
      intro i; unfold wrnat
      split_ifs with h
      · rw [h_y _ (by omega)]
      · rfl
    have h_addr : dispatch_addr air row =
        dispatch_addr air row - dispatch_addr air row % 8 + dispatch_addr air row % 8 := by omega
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    rcases access_effect air row s h_ext_asm h_wf_asm h_constraints h_mem n h_n with
      ⟨ hx, h_acc ⟩ | ⟨ hx, h_acc ⟩
    · exact flow_store s _ ops _ _ _ n 8 _ _ yb h_acc h_disp h_addr (h_fit hx) (fun i _ => h_v i)
    · exact flow_store s _ ops _ _ _ n 16 _ _ yb h_acc h_disp h_addr (by omega) (fun i _ => h_v i)

  /-! ### The bytes of a dispatch's value -/

  private lemma byte_bytes (a : FKB) (b : ℕ → ℕ) (k : ℕ) (hb : b (k + 0) < 256)
      (h : a.val % 256 = b (k + 0)) :
      ∀ j < 1, (BitVec.ofNat 8 a.val).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (b (k + j)) := by
    intro j hj
    interval_cases j
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.add_zero] at hb h ⊢
    simp; omega

  private lemma half_bytes (a : FKB) (b : ℕ → ℕ) (k : ℕ) (hb : ∀ j < 2, b (k + j) < 256)
      (h : a.val = b (k + 0) + 256 * b (k + 1)) :
      ∀ j < 2, (BitVec.ofNat 16 a.val).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (b (k + j)) := by
    have b0 := hb 0 (by omega); have b1 := hb 1 (by omega)
    simp only [Nat.add_zero] at b0 h
    intro j hj
    interval_cases j <;> apply BitVec.eq_of_toNat_eq <;>
      simp [Nat.shiftRight_eq_div_pow] <;> omega

  private lemma word_bytes (a0 a1 : FKB) (b : ℕ → ℕ) (k : ℕ) (hb : ∀ j < 4, b (k + j) < 256)
      (h0 : a0.val = b (k + 0) + 256 * b (k + 1)) (h1 : a1.val = b (k + 2) + 256 * b (k + 3)) :
      ∀ j < 4, (BitVec.ofNat 16 a1.val ++ BitVec.ofNat 16 a0.val).extractLsb' (8 * j) 8 =
        BitVec.ofNat 8 (b (k + j)) := by
    have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
    have b3 := hb 3 (by omega)
    simp only [Nat.add_zero] at b0 h0
    rw [show (BitVec.ofNat 16 a1.val ++ BitVec.ofNat 16 a0.val : BitVec 32) =
      U32w.toBV #v[BitVec.ofNat 16 a0.val, BitVec.ofNat 16 a1.val] from rfl]
    intro j hj
    interval_cases j <;> apply BitVec.eq_of_toNat_eq <;>
      simp [U32w.toBV_toNat, U32w.toNat, Nat.shiftRight_eq_div_pow] <;> omega

  /-- On a store row `op_a`'s pieces are its byte pairs, `rnat`, and those are bytes. -/
  private lemma rnat_split
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
    (h_store : air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
      air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1)
  :
    let i := air.cols.instruction
    (i.op_a_value_0 row 0).val = rnat air row 0 + 256 * rnat air row 1 ∧
    (i.op_a_value_1 row 0).val = rnat air row 2 + 256 * rnat air row 3 ∧
    (i.op_a_value_2 row 0).val = rnat air row 4 + 256 * rnat air row 5 ∧
    (i.op_a_value_3 row 0).val = rnat air row 6 + 256 * rnat air row 7 ∧
    ∀ j < 8, rnat air row j < 256
  := by
    obtain ⟨ -, -, -, -, -, -, -, -, h_value ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ ⟨ s0, t0 ⟩, ⟨ s1, t1 ⟩, ⟨ s2, t2 ⟩, ⟨ s3, t3 ⟩ ⟩ := h_value h_store
    obtain ⟨ r0, r1, r2, r3, r4, r5, r6, r7 ⟩ := rnat_eqs air row
    dsimp only
    rw [r0, r1, r2, r3, r4, r5, r6, r7]
    refine ⟨ byte_split s0 t0, byte_split s1 t1, byte_split s2 t2, byte_split s3 t3,
      fun j hj => ?_ ⟩
    interval_cases j <;> simp only [r0, r1, r2, r3, r4, r5, r6, r7] <;> with_reducible assumption

  /-- Whether a row of width `w` crosses: `cross` is 1 exactly when the offset is at least
      `t = 9 - w` (constraint 26). -/
  private lemma cross_cases {c : FKB} {off w t : ℕ} (hc : c = if t ≤ off then 1 else 0)
      (ht : t + w = 9) :
      (off + w ≤ 8 ∨ c = 1) ∧ (c = 0 → off + w ≤ 8) := by
    split_ifs at hc with h
    · exact ⟨ Or.inr hc, fun h0 => absurd (hc.symm.trans h0) (by decide) ⟩
    · exact ⟨ Or.inl (by omega), fun _ => by omega ⟩

  /-! ### One opcode at a time -/

  private theorem dataFlow_LB
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lb : air.cols.instruction.is_lb row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lb air row h_constraints h_is_lb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    obtain ⟨ hw8, - ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_sb, - ⟩ := seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, -, -, -, c41, -, -, -, c45, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    simp only [constraint_45] at c45
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Byte
              (BitVec.ofNat 8 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      refine row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 1 _
        (fun j => (BitVec.ofNat 8 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb'
          (8 * j) 8)
        (read_byte_effect state _ _) (by norm_num) (fun _ => by omega)
        (byte_bytes _ (wnat air row) _ (hw8 _ (by omega)) ?_) h_load
      have hsb : (air.cols.seen_byte row 0).val < 256 := by rw [h_sb]; exact hw8 _ h_off
      show _ = wnat air row (dispatch_addr air row % 8)
      rw [← h_sb]
      rcases bool_cases c45 with m | m <;> rw [m] at c37 <;> simp at c37 <;> rw [c37]
      · omega
      · rw [val_add_of_lt (by rw [show (65280 : FKB).val = 65280 from rfl]; omega),
          show (65280 : FKB).val = 65280 from rfl]
        omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Byte ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 1 _
        (read_any_effect state _ .Byte) (by norm_num) (fun _ => by omega) h_load




  private theorem dataFlow_LBU
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lbu : air.cols.instruction.is_lbu row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lbu air row h_constraints h_is_lbu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    obtain ⟨ hw8, - ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_sb, - ⟩ := seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, -, -, -, c41, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Byte (BitVec.ofNat 8 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      refine row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 1 _
        (fun j => (BitVec.ofNat 8 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb'
          (8 * j) 8)
        (read_byte_effect state _ _) (by norm_num) (fun _ => by omega)
        (byte_bytes _ (wnat air row) _ (hw8 _ (by omega)) ?_) h_load
      have hsb : (air.cols.seen_byte row 0).val < 256 := by rw [h_sb]; exact hw8 _ h_off
      show _ = wnat air row (dispatch_addr air row % 8)
      rw [← h_sb, c37]
      omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Byte ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 1 _
        (read_any_effect state _ .Byte) (by norm_num) (fun _ => by omega) h_load

  private theorem dataFlow_LH
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lh : air.cols.instruction.is_lh row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lh air row h_constraints h_is_lh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o7] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 2) (t := 7) hc (by norm_num)
    have hb : ∀ j < 2, wnat air row (dispatch_addr air row % 8 + j) < 256 := by
      intro j hj
      rcases h_cond with h | h
      · exact hw8 _ (by omega)
      · exact hw16 h _ (by omega)
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, -, -, -, c41, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Half
              (BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 2 _
        (fun j => (BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
        (read_half_effect state _ _) (by norm_num) h_fit
        (half_bytes _ (wnat air row) _ hb (by rw [c37]; exact h_s0 (h_cond.imp_left (by omega)))) h_load
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Half ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 2 _
        (read_any_effect state _ .Half) (by norm_num) h_fit h_load

  private theorem dataFlow_LHU
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lhu : air.cols.instruction.is_lhu row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lhu air row h_constraints h_is_lhu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o7] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 2) (t := 7) hc (by norm_num)
    have hb : ∀ j < 2, wnat air row (dispatch_addr air row % 8 + j) < 256 := by
      intro j hj
      rcases h_cond with h | h
      · exact hw8 _ (by omega)
      · exact hw16 h _ (by omega)
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, -, -, -, c41, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Half
              (BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 2 _
        (fun j => (BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
        (read_half_effect state _ _) (by norm_num) h_fit
        (half_bytes _ (wnat air row) _ hb (by rw [c37]; exact h_s0 (h_cond.imp_left (by omega)))) h_load
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Half ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 2 _
        (read_any_effect state _ .Half) (by norm_num) h_fit h_load

  private theorem dataFlow_LW
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lw : air.cols.instruction.is_lw row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lw air row h_constraints h_is_lw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_5 row 0 + air.cols.offset_6 row 0 + air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o5] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 4) (t := 5) hc (by norm_num)
    have hb : ∀ j < 4, wnat air row (dispatch_addr air row % 8 + j) < 256 := by
      intro j hj
      rcases h_cond with h | h
      · exact hw8 _ (by omega)
      · exact hw16 h _ (by omega)
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, c38, -, -, c41, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, constraint_38, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Word
              (BitVec.ofNat 16 (air.cols.instruction.op_a_value_1 row 0).val ++
              BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 4 _
        (fun j => (BitVec.ofNat 16 (air.cols.instruction.op_a_value_1 row 0).val ++
              BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
        (read_word_effect state _ _) (by norm_num) h_fit
        (word_bytes _ _ (wnat air row) _ hb (by rw [c37]; exact h_s0 (h_cond.imp_left (by omega)))
          (by rw [c38]; exact h_s1 (h_cond.imp_left (by omega)))) h_load
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Word ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 4 _
        (read_any_effect state _ .Word) (by norm_num) h_fit h_load

  private theorem dataFlow_LWU
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_lwu : air.cols.instruction.is_lwu row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lwu air row h_constraints h_is_lwu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_5 row 0 + air.cols.offset_6 row 0 + air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o5] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 4) (t := 5) hc (by norm_num)
    have hb : ∀ j < 4, wnat air row (dispatch_addr air row % 8 + j) < 256 := by
      intro j hj
      rcases h_cond with h | h
      · exact hw8 _ (by omega)
      · exact hw16 h _ (by omega)
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, c38, -, -, c41, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, constraint_38, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Word
              (BitVec.ofNat 16 (air.cols.instruction.op_a_value_1 row 0).val ++
              BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 4 _
        (fun j => (BitVec.ofNat 16 (air.cols.instruction.op_a_value_1 row 0).val ++
              BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
        (read_word_effect state _ _) (by norm_num) h_fit
        (word_bytes _ _ (wnat air row) _ hb (by rw [c37]; exact h_s0 (h_cond.imp_left (by omega)))
          (by rw [c38]; exact h_s1 (h_cond.imp_left (by omega)))) h_load
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Word ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 4 _
        (read_any_effect state _ .Word) (by norm_num) h_fit h_load

  private theorem dataFlow_LD
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_ld : air.cols.instruction.is_ld row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_ld air row h_constraints h_is_ld
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_load : StoreWidth air row 0 := Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_1 row 0 + air.cols.offset_2 row 0 + air.cols.offset_3 row 0 +
        air.cols.offset_4 row 0 + air.cols.offset_5 row 0 + air.cols.offset_6 row 0 +
        air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o1] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 8) (t := 1) hc (by norm_num)
    have hb : ∀ j < 8, wnat air row (dispatch_addr air row % 8 + j) < 256 := by
      intro j hj
      rcases h_cond with h | h
      · exact hw8 _ (by omega)
      · exact hw16 h _ (by omega)
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, c37, c38, c39, c40, c41, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_41] at c41
    unfold DataFlow
    dsimp only
    rcases bool_cases c41 with h0 | h0
    · simp [constraint_37, constraint_38, constraint_39, constraint_40, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0, sub_eq_zero] at c37 c38 c39 c40
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Double
              (U64w.toBV #v[air.cols.instruction.op_a_value_0 row 0,
              air.cols.instruction.op_a_value_1 row 0,
              air.cols.instruction.op_a_value_2 row 0,
              air.cols.instruction.op_a_value_3 row 0]) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_load air row state h_ext_asm h_wf_asm h_constraints h_mem 8 _
        (fun j => (U64w.toBV #v[air.cols.instruction.op_a_value_0 row 0,
              air.cols.instruction.op_a_value_1 row 0,
              air.cols.instruction.op_a_value_2 row 0,
              air.cols.instruction.op_a_value_3 row 0]).extractLsb' (8 * j) 8)
        (read_double_effect state _ _) (by norm_num) h_fit
        (toBV_byte_eq _ _ _ _ (wnat air row) _ hb
          (by rw [c37]; exact h_s0 (h_cond.imp_left (by omega)))
          (by rw [c38]; exact h_s1 (h_cond.imp_left (by omega)))
          (by rw [c39]; exact h_s2 (h_cond.imp_left (by omega)))
          (by rw [c40]; exact h_s3 (h_cond.imp_left (by omega)))) h_load
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Double ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, h0]
      rw [h_disp]
      exact row_any air row state h_ext_asm h_wf_asm h_constraints h_mem 8 _
        (read_any_effect state _ .Double) (by norm_num) h_fit h_load

  private theorem dataFlow_SB
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sb : air.cols.instruction.is_sb row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sb air row h_constraints h_is_sb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_st : StoreWidth air row 1 := Or.inr (Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩)
    have h_store : air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
        air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1 := by
      rw [f7, f8, f9, f10]; norm_num
    obtain ⟨ ha0, ha1, ha2, ha3, hr ⟩ :=
      rnat_split air row h_ext_asm h_wf_asm h_constraints h_mem h_store
    have h_fit : air.cols.cross row 0 = 0 → dispatch_addr air row % 8 + 1 ≤ 8 := fun _ => by omega
    unfold DataFlow
    dsimp only
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Byte
            (BitVec.ofNat 8 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    rw [h_disp]
    exact row_store air row state h_ext_asm h_wf_asm h_constraints h_mem 1 h_st _
      (fun j => (BitVec.ofNat 8 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
      (write_byte_effect state _ _) h_fit
      (fun j hj => (byte_bytes _ (rnat air row) 0 (hr 0 (by omega)) (by show _ = rnat air row 0; have := hr 0 (by omega); rw [ha0]; omega) j hj).trans (by rw [Nat.zero_add]))

  private theorem dataFlow_SH
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sh : air.cols.instruction.is_sh row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sh air row h_constraints h_is_sh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_st : StoreWidth air row 2 := Or.inr (Or.inr (Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩))
    have h_store : air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
        air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1 := by
      rw [f7, f8, f9, f10]; norm_num
    obtain ⟨ ha0, ha1, ha2, ha3, hr ⟩ :=
      rnat_split air row h_ext_asm h_wf_asm h_constraints h_mem h_store
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o7] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 2) (t := 7) hc (by norm_num)
    unfold DataFlow
    dsimp only
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Half
            (BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    rw [h_disp]
    exact row_store air row state h_ext_asm h_wf_asm h_constraints h_mem 2 h_st _
      (fun j => (BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
      (write_half_effect state _ _) h_fit
      (fun j hj => (half_bytes _ (rnat air row) 0 (fun j hj => hr _ (by omega)) ha0 j hj).trans (by rw [Nat.zero_add]))

  private theorem dataFlow_SW
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sw : air.cols.instruction.is_sw row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sw air row h_constraints h_is_sw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_st : StoreWidth air row 4 := Or.inr (Or.inr (Or.inr (Or.inl ⟨ rfl, f7, f8, f9, f10 ⟩)))
    have h_store : air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
        air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1 := by
      rw [f7, f8, f9, f10]; norm_num
    obtain ⟨ ha0, ha1, ha2, ha3, hr ⟩ :=
      rnat_split air row h_ext_asm h_wf_asm h_constraints h_mem h_store
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_5 row 0 + air.cols.offset_6 row 0 + air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o5] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 4) (t := 5) hc (by norm_num)
    unfold DataFlow
    dsimp only
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Word
            (BitVec.ofNat 16 (air.cols.instruction.op_a_value_1 row 0).val ++
            BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    rw [h_disp]
    exact row_store air row state h_ext_asm h_wf_asm h_constraints h_mem 4 h_st _
      (fun j => (BitVec.ofNat 16 (air.cols.instruction.op_a_value_1 row 0).val ++
            BitVec.ofNat 16 (air.cols.instruction.op_a_value_0 row 0).val).extractLsb' (8 * j) 8)
      (write_word_effect state _ _) h_fit
      (fun j hj => (word_bytes _ _ (rnat air row) 0 (fun j hj => hr _ (by omega)) ha0 ha1 j hj).trans (by rw [Nat.zero_add]))

  private theorem dataFlow_SD
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
    (h_is_sd : air.cols.instruction.is_sd row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sd air row h_constraints h_is_sd
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := Nat.mod_lt (dispatch_addr air row) (by norm_num : 8 > 0)
    have h_st : StoreWidth air row 8 := Or.inr (Or.inr (Or.inr (Or.inr ⟨ rfl, f7, f8, f9, f10 ⟩)))
    have h_store : air.cols.instruction.is_sb row 0 + air.cols.instruction.is_sh row 0 +
        air.cols.instruction.is_sw row 0 + air.cols.instruction.is_sd row 0 = 1 := by
      rw [f7, f8, f9, f10]; norm_num
    obtain ⟨ ha0, ha1, ha2, ha3, hr ⟩ :=
      rnat_split air row h_ext_asm h_wf_asm h_constraints h_mem h_store
    obtain ⟨ hw8, hw16 ⟩ := wnat_lt air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, h_s0, h_s1, h_s2, h_s3, h_o7, h_o5, h_o1 ⟩ :=
      seen_vals air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
    have hc : air.cols.cross row 0 = air.cols.offset_1 row 0 + air.cols.offset_2 row 0 + air.cols.offset_3 row 0 +
        air.cols.offset_4 row 0 + air.cols.offset_5 row 0 + air.cols.offset_6 row 0 +
        air.cols.offset_7 row 0 := by linear_combination c26
    rw [h_o1] at hc
    obtain ⟨ h_cond, h_fit ⟩ := cross_cases (w := 8) (t := 1) hc (by norm_num)
    unfold DataFlow
    dsimp only
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Double
            (U64w.toBV #v[air.cols.instruction.op_a_value_0 row 0,
            air.cols.instruction.op_a_value_1 row 0,
            air.cols.instruction.op_a_value_2 row 0,
            air.cols.instruction.op_a_value_3 row 0]) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    rw [h_disp]
    exact row_store air row state h_ext_asm h_wf_asm h_constraints h_mem 8 h_st _
      (fun j => (U64w.toBV #v[air.cols.instruction.op_a_value_0 row 0,
            air.cols.instruction.op_a_value_1 row 0,
            air.cols.instruction.op_a_value_2 row 0,
            air.cols.instruction.op_a_value_3 row 0]).extractLsb' (8 * j) 8)
      (write_double_effect state _ _) h_fit
      (fun j hj => (toBV_byte_eq _ _ _ _ (rnat air row) 0 (fun j hj => hr _ (by omega)) ha0 ha1 ha2 ha3 j hj).trans (by rw [Nat.zero_add]))

  /-! ### Every row -/

  /-- On every row that satisfies the constraints, given what its messages are promised, the
      row's data flow holds in every Sail state. A row with no flag set sends its messages at
      multiplicity 0, with `cross = 0` (constraint 26), and its dispatch with opcode 0, which
      `bus_operations` reads as no operation. -/
  theorem dataFlow_of_allHold
    [Field ExtF]
    (air : Valid_MemoryUnalignedChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryUnalignedChip.Extraction.allHold air row)
  :
    DataFlow air row state
  := by
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [flags, List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h
    · obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c26,
        - ⟩ := constraints_of_allHold air row h_constraints
      have hx : air.cols.cross row 0 = 0 := by
        simp only [constraint_26, f2, f3, f4, f5, f6, f8, f9, f10] at c26
        linear_combination c26
      unfold DataFlow
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryUnalignedChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, RV64IM.operation_list_effect, f0, f1, f2, f3,
        f4, f5, f6, f7, f8, f9, f10, hx]
    · exact dataFlow_LB air row state h_ext_asm h_wf_asm h_constraints f0
    · exact dataFlow_LBU air row state h_ext_asm h_wf_asm h_constraints f1
    · exact dataFlow_LH air row state h_ext_asm h_wf_asm h_constraints f2
    · exact dataFlow_LHU air row state h_ext_asm h_wf_asm h_constraints f3
    · exact dataFlow_LW air row state h_ext_asm h_wf_asm h_constraints f4
    · exact dataFlow_LWU air row state h_ext_asm h_wf_asm h_constraints f5
    · exact dataFlow_LD air row state h_ext_asm h_wf_asm h_constraints f6
    · exact dataFlow_SB air row state h_ext_asm h_wf_asm h_constraints f7
    · exact dataFlow_SH air row state h_ext_asm h_wf_asm h_constraints f8
    · exact dataFlow_SW air row state h_ext_asm h_wf_asm h_constraints f9
    · exact dataFlow_SD air row state h_ext_asm h_wf_asm h_constraints f10

end MemoryUnalignedChip.Spec


