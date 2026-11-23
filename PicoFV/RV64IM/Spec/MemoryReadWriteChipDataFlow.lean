import PicoFV.RV64IM.Spec.MemoryReadWriteChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryReadWriteChip — what a row does to memory

The data flow of a row of `MemoryReadWriteChip` (`MemoryReadWriteChip::eval`,
`vm/src/chips/chips/riscv_memory/read_write/constraints.rs`, Pico v3.2.0
`fcfa504624657d0c417c43f1233d5d891f293ff9`; messages in `Constraints/MemoryReadWriteChip.lean`).

A real row sends the memory argument the read of the double word at the aligned address
(`looking`, multiplicity 1) and receives its write back (`looked`, multiplicity -1)
(`machine/builder/riscv_memory.rs:194-208` at v3.2.0), and receives the memory dispatch from the
CPU chip (`riscv_memory/read_write/constraints.rs:63-84` at v3.2.0). `V3.bus_operations` reads
the pair as a double-word `ReadMem` and `WriteMem` at the aligned address, and the dispatch as an
access of its opcode's width at `b + c`: a `WriteMem` of `a` for a store, a `ReadMem` of `a` for
a load, or a `ReadMemAny` for a load into `x0`.

- `dataFlow_of_allHold`: on every row, in any Sail state that holds the double word the row
  reads, the dispatch's read holds too, so a load's value, taken at the load's width, is the
  bytes of that double word at `b + c` (`riscv_memory/read_write/constraints.rs:423-442` at
  v3.2.0); and the two operation lists leave the same state, so a store writes the double word
  back with the stored bytes patched in and a load writes it back unchanged
  (`riscv_memory/read_write/constraints.rs:565-595` at v3.2.0). The sign or zero fill above a
  load's width is not read here: it is the Memory promise's (`spec_LB` to `spec_LWU`).

`dataFlow_of_allHold` assumes what the Memory promise's theorems assume
(`Spec/MemoryReadWriteChip.lean`): the row's constraints (`allHold`) and what its messages are
promised (`bus_row_all_ext_asm`, `bus_row_all_wf_asm`). That the double word read is the one
memory holds is the memory argument's promise, which `dataFlow_of_allHold` takes as the
hypothesis of `DataFlow`. `bus_operations` does not read the messages' `chunk`, `clk` and
`prev_clk` fields, and nothing here is said about them.
-/

namespace MemoryReadWriteChip.Spec

  open RV64IM_Interactions.V3
  open MemoryReadWriteChip.ConstraintsAndBuses
  open MemoryReadWriteChip.Interactions

  /-- The row's data flow in the Sail state `state`: if the reads among the row's messages to the
      memory argument hold in `state`, the read of the memory dispatch the row receives holds
      too, and the two lists of operations leave the same state. -/
  def DataFlow
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
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

  /-! ### Bytes -/

  /-- The eight bytes of a double word made of four pieces, each read modulo `2^16`. -/
  private lemma toBV_bytes (p0 p1 p2 p3 : FKB) :
      BitVec.extractLsb' 0 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 p0.val ∧
      BitVec.extractLsb' 8 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 (p0.val / 256) ∧
      BitVec.extractLsb' 16 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 p1.val ∧
      BitVec.extractLsb' 24 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 (p1.val / 256) ∧
      BitVec.extractLsb' 32 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 p2.val ∧
      BitVec.extractLsb' 40 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 (p2.val / 256) ∧
      BitVec.extractLsb' 48 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 p3.val ∧
      BitVec.extractLsb' 56 8 (U64w.toBV #v[p0, p1, p2, p3]) = BitVec.ofNat 8 (p3.val / 256) := by
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;>
      apply BitVec.eq_of_toNat_eq <;>
      simp [U64w.toBV_toNat, U64w.toNat, Nat.shiftRight_eq_div_pow] <;> omega

  /-- The two bytes of a halfword. -/
  private lemma half_bytes (n : ℕ) :
      BitVec.extractLsb' 0 8 (BitVec.ofNat 16 n) = BitVec.ofNat 8 n ∧
      BitVec.extractLsb' 8 8 (BitVec.ofNat 16 n) = BitVec.ofNat 8 (n / 256) := by
    refine ⟨ ?_, ?_ ⟩
    · apply BitVec.eq_of_toNat_eq; simp
    · apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega

  /-- The four bytes of a word made of two halfwords. -/
  private lemma word_bytes (n0 n1 : ℕ) :
      BitVec.extractLsb' 0 8 (BitVec.ofNat 16 n1 ++ BitVec.ofNat 16 n0) = BitVec.ofNat 8 n0 ∧
      BitVec.extractLsb' 8 8 (BitVec.ofNat 16 n1 ++ BitVec.ofNat 16 n0) =
        BitVec.ofNat 8 (n0 / 256) ∧
      BitVec.extractLsb' 16 8 (BitVec.ofNat 16 n1 ++ BitVec.ofNat 16 n0) = BitVec.ofNat 8 n1 ∧
      BitVec.extractLsb' 24 8 (BitVec.ofNat 16 n1 ++ BitVec.ofNat 16 n0) =
        BitVec.ofNat 8 (n1 / 256) := by
    rw [show (BitVec.ofNat 16 n1 ++ BitVec.ofNat 16 n0 : BitVec 32) =
      U32w.toBV #v[BitVec.ofNat 16 n0, BitVec.ofNat 16 n1] from rfl]
    refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;>
      apply BitVec.eq_of_toNat_eq <;>
      simp [U32w.toBV_toNat, U32w.toNat, Nat.shiftRight_eq_div_pow] <;> omega

  /-- The offset `o0 + 2 o1 + 4 o2` for each value of the three offset bits. -/
  private lemma offset_lits :
      ((0 : FKB) + 2 * 0 + 4 * 0).val = 0 ∧ ((1 : FKB) + 2 * 0 + 4 * 0).val = 1 ∧
      ((0 : FKB) + 2 * 1 + 4 * 0).val = 2 ∧ ((1 : FKB) + 2 * 1 + 4 * 0).val = 3 ∧
      ((0 : FKB) + 2 * 0 + 4 * 1).val = 4 ∧ ((1 : FKB) + 2 * 0 + 4 * 1).val = 5 ∧
      ((0 : FKB) + 2 * 1 + 4 * 1).val = 6 ∧ ((1 : FKB) + 2 * 1 + 4 * 1).val = 7 :=
    ⟨ rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl ⟩

  /-- A 16-bit piece is its low byte plus 256 times `(x - lo) / 256`; `2122383361` is `256`'s
      inverse. -/
  private lemma split_eq (x lo : FKB) : x = lo + 256 * ((x - lo) * 2122383361) := by
    rw [mul_comm 256, mul_assoc, show (2122383361 : FKB) * 256 = 1 from rfl]; ring

  /-- The piece an SB row writes when it patches the low byte of `x = lo + 256 h` with `r`. -/
  private lemma patch_low {x lo r h : FKB} (e : x = lo + 256 * h) (h_h : h.val < 256)
      (h_r : r.val < 256) : (x + (r - lo)).val = r.val + 256 * h.val := by
    have e2 : x + (r - lo) = r + 256 * h := by rw [e]; ring
    have h256 : (256 : FKB).val = 256 := rfl
    have hm : (256 * h).val = 256 * h.val := by rw [val_mul_of_lt (by rw [h256]; omega), h256]
    rw [e2, val_add_of_lt (by rw [hm]; omega), hm]

  /-- The piece an SB row writes when it patches the high byte of `x`, whose low byte is `lo`,
      with `r`. -/
  private lemma patch_high {x lo r : FKB} (h_lo : lo.val < 256) (h_r : r.val < 256) :
      (x + (r * 256 - x + lo)).val = lo.val + 256 * r.val := by
    have e2 : x + (r * 256 - x + lo) = lo + 256 * r := by ring
    have h256 : (256 : FKB).val = 256 := rfl
    have hm : (256 * r).val = 256 * r.val := by rw [val_mul_of_lt (by rw [h256]; omega), h256]
    rw [e2, val_add_of_lt (by rw [hm]; omega), hm]

  /-! ### The operations of an access and of a dispatch

  Each lemma below states, for one width and direction, that the double-word read and write of
  the access and the dispatch's operation agree as `DataFlow` asks, given how the bytes of the
  three values relate. `A` is the aligned address and `off` the offset of the dispatch in the
  double word. -/

  private lemma eq_with_mem (s : SailState) (m : Std.ExtHashMap ℕ (BitVec 8)) (h : m = s.mem) :
      s = { s with mem := m } := by
    subst h; rfl

  private lemma load_byte_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64) (x : BitVec 8)
      (h_addr : addr = A + off) (h_off : off < 8) (h_V : V = P)
      (h_x : x = BitVec.extractLsb' (8 * off) 8 P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.ReadMem addr .Byte x] s).hypotheses ∧
        (RV64IM.operation_list_effect [.ReadMem addr .Byte x] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr; subst V; subst x
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    refine ⟨ ?_, ?_ ⟩
    · interval_cases off <;> simpa
    · congr 1
      apply eq_with_mem
      ext k : 1
      simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
      split_ifs <;> first | omega | simp_all

  private lemma load_half_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64) (x : BitVec 16)
      (h_addr : addr = A + off) (h_off : off + 2 ≤ 8) (h_V : V = P)
      (h_x0 : BitVec.extractLsb' 0 8 x = BitVec.extractLsb' (8 * off) 8 P)
      (h_x1 : BitVec.extractLsb' 8 8 x = BitVec.extractLsb' (8 * (off + 1)) 8 P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.ReadMem addr .Half x] s).hypotheses ∧
        (RV64IM.operation_list_effect [.ReadMem addr .Half x] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr; subst V
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    refine ⟨ ?_, ?_ ⟩
    · have hb : off ≤ 8 := by omega
      interval_cases off <;> first | omega | simp_all
    · congr 1
      apply eq_with_mem
      ext k : 1
      simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
      split_ifs <;> first | omega | simp_all

  private lemma load_word_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64) (x : BitVec 32)
      (h_addr : addr = A + off) (h_off : off + 4 ≤ 8) (h_V : V = P)
      (h_x0 : BitVec.extractLsb' 0 8 x = BitVec.extractLsb' (8 * off) 8 P)
      (h_x1 : BitVec.extractLsb' 8 8 x = BitVec.extractLsb' (8 * (off + 1)) 8 P)
      (h_x2 : BitVec.extractLsb' 16 8 x = BitVec.extractLsb' (8 * (off + 2)) 8 P)
      (h_x3 : BitVec.extractLsb' 24 8 x = BitVec.extractLsb' (8 * (off + 3)) 8 P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.ReadMem addr .Word x] s).hypotheses ∧
        (RV64IM.operation_list_effect [.ReadMem addr .Word x] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr; subst V
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    refine ⟨ ?_, ?_ ⟩
    · have hb : off ≤ 8 := by omega
      interval_cases off <;> first | omega | simp_all
    · congr 1
      apply eq_with_mem
      ext k : 1
      simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
      split_ifs <;> first | omega | simp_all

  private lemma load_double_flow (s : SailState) (A addr : ℕ) (P V : BitVec 64) (x : BitVec 64)
      (h_addr : addr = A) (h_V : V = P) (h_x : x = P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.ReadMem addr .Double x] s).hypotheses ∧
        (RV64IM.operation_list_effect [.ReadMem addr .Double x] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr; subst V; subst x
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    refine ⟨ ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩, ?_ ⟩
    congr 1
    apply eq_with_mem
    ext k : 1
    simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    split_ifs <;> first | omega | simp_all

  private lemma load_any_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64)
      (w : RV64IM.MemoryWidth) (h_addr : addr = A + off)
      (h_off : off + RV64IM.width_of_mem_width w / 8 ≤ 8) (h_V : V = P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.ReadMemAny addr w] s).hypotheses ∧
        (RV64IM.operation_list_effect [.ReadMemAny addr w] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr; subst V
    cases w <;> simp only [RV64IM.width_of_mem_width, Nat.reduceDiv] at h_off <;>
      simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect,
        BitVec.extractLsb, true_and] <;>
      rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ <;>
      refine ⟨ ?_, ?_ ⟩
    all_goals first
      | (congr 1
         apply eq_with_mem
         ext k : 1
         simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
         split_ifs <;> first | omega | simp_all)
      | (have hb : off ≤ 8 := by omega
         interval_cases off <;> first | omega | simp_all)

  private lemma store_byte_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64) (y : BitVec 8)
      (h_addr : addr = A + off) (h_off : off < 8)
      (h_V : ∀ i < 8, BitVec.extractLsb' (8 * i) 8 V =
        if i = off then y else BitVec.extractLsb' (8 * i) 8 P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.WriteMem addr .Byte y] s).hypotheses ∧
        (RV64IM.operation_list_effect [.WriteMem addr .Byte y] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr
    have v0 := h_V 0 (by omega)
    have v1 := h_V 1 (by omega)
    have v2 := h_V 2 (by omega)
    have v3 := h_V 3 (by omega)
    have v4 := h_V 4 (by omega)
    have v5 := h_V 5 (by omega)
    have v6 := h_V 6 (by omega)
    have v7 := h_V 7 (by omega)
    clear h_V
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    congr 2
    ext k : 1
    have hb : off ≤ 8 := by omega
    interval_cases off <;> simp at v0 v1 v2 v3 v4 v5 v6 v7 <;>
      simp only [Std.ExtHashMap.getElem?_insert, Nat.sub_zero, Nat.reduceSub, Nat.reduceAdd,
        v0, v1, v2, v3, v4, v5, v6, v7, beq_iff_eq] <;>
      split_ifs <;> first | omega | simp_all

  private lemma store_half_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64) (y : BitVec 16)
      (h_addr : addr = A + off) (h_off : off + 2 ≤ 8)
      (h_V : ∀ i < 8, BitVec.extractLsb' (8 * i) 8 V =
        if i = off then BitVec.extractLsb' 0 8 y
        else if i = off + 1 then BitVec.extractLsb' 8 8 y
        else BitVec.extractLsb' (8 * i) 8 P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.WriteMem addr .Half y] s).hypotheses ∧
        (RV64IM.operation_list_effect [.WriteMem addr .Half y] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr
    have v0 := h_V 0 (by omega)
    have v1 := h_V 1 (by omega)
    have v2 := h_V 2 (by omega)
    have v3 := h_V 3 (by omega)
    have v4 := h_V 4 (by omega)
    have v5 := h_V 5 (by omega)
    have v6 := h_V 6 (by omega)
    have v7 := h_V 7 (by omega)
    clear h_V
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    congr 2
    ext k : 1
    have hb : off ≤ 8 := by omega
    interval_cases off <;> (try omega) <;> simp at v0 v1 v2 v3 v4 v5 v6 v7 <;>
      simp only [Std.ExtHashMap.getElem?_insert, Nat.sub_zero, Nat.reduceSub, Nat.reduceAdd,
        v0, v1, v2, v3, v4, v5, v6, v7, beq_iff_eq] <;>
      split_ifs <;> first | omega | simp_all

  private lemma store_word_flow (s : SailState) (A addr off : ℕ) (P V : BitVec 64) (y : BitVec 32)
      (h_addr : addr = A + off) (h_off : off + 4 ≤ 8)
      (h_V : ∀ i < 8, BitVec.extractLsb' (8 * i) 8 V =
        if i = off then BitVec.extractLsb' 0 8 y
        else if i = off + 1 then BitVec.extractLsb' 8 8 y
        else if i = off + 2 then BitVec.extractLsb' 16 8 y
        else if i = off + 3 then BitVec.extractLsb' 24 8 y
        else BitVec.extractLsb' (8 * i) 8 P) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.WriteMem addr .Word y] s).hypotheses ∧
        (RV64IM.operation_list_effect [.WriteMem addr .Word y] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr
    have v0 := h_V 0 (by omega)
    have v1 := h_V 1 (by omega)
    have v2 := h_V 2 (by omega)
    have v3 := h_V 3 (by omega)
    have v4 := h_V 4 (by omega)
    have v5 := h_V 5 (by omega)
    have v6 := h_V 6 (by omega)
    have v7 := h_V 7 (by omega)
    clear h_V
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, BitVec.extractLsb,
      true_and]
    rintro ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩
    congr 2
    ext k : 1
    have hb : off ≤ 8 := by omega
    interval_cases off <;> (try omega) <;> simp at v0 v1 v2 v3 v4 v5 v6 v7 <;>
      simp only [Std.ExtHashMap.getElem?_insert, Nat.sub_zero, Nat.reduceSub, Nat.reduceAdd,
        v0, v1, v2, v3, v4, v5, v6, v7, beq_iff_eq] <;>
      split_ifs <;> first | omega | simp_all

  private lemma store_double_flow (s : SailState) (A addr : ℕ) (P V : BitVec 64) (y : BitVec 64)
      (h_addr : addr = A) (h_V : V = y) :
      (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).hypotheses →
        (RV64IM.operation_list_effect [.WriteMem addr .Double y] s).hypotheses ∧
        (RV64IM.operation_list_effect [.WriteMem addr .Double y] s).state =
          (RV64IM.operation_list_effect [.ReadMem A .Double P, .WriteMem A .Double V] s).state := by
    subst h_addr; subst V
    simp only [RV64IM.operation_list_effect, List.foldl, RV64IM.operation_effect, true_and]
    intro _
    trivial

  /-! ### The row's operation lists -/

  /-- The address `b + c` the memory dispatch names. -/
  private def dispatch_addr [Field ExtF] (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) :
      ℕ :=
    let v := air.cols.values
    (U64w.toBV #v[v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
        v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0] +
      U64w.toBV #v[v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
        v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0]).toNat

  /-- On a real row the access is a double-word read and write at `b + c` with its three low bits
      cleared: the address `[addr_word_0 - offset, addr_word_1, 0]` is at least `2^16`, so
      `bus_operations` reads it as memory, not as a register. -/
  private lemma access_ops
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    let v := air.cols.values
    RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := [] } =
      [ .ReadMem (dispatch_addr air row - dispatch_addr air row % 8) .Double
          (U64w.toBV #v[v.memory_access.prev_value_0 row 0, v.memory_access.prev_value_1 row 0,
            v.memory_access.prev_value_2 row 0, v.memory_access.prev_value_3 row 0]),
        .WriteMem (dispatch_addr air row - dispatch_addr air row % 8) .Double
          (U64w.toBV #v[v.memory_access.access.value_0 row 0, v.memory_access.access.value_1 row 0,
            v.memory_access.access.value_2 row 0, v.memory_access.access.value_3 row 0]) ]
  := by
    obtain ⟨ -, -, -, h_pos ⟩ := address air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, h_al ⟩ := aligned_address air row h_ext_asm h_wf_asm h_constraints h_mem
    simp only [is_memory] at h_mem
    dsimp only [dispatch_addr] at h_al ⊢
    rw [← h_al]
    have h_ge : ¬ ((air.cols.values.addr_word_0 row 0 - (air.cols.values.offset_bit_0 row 0 +
        2 * air.cols.values.offset_bit_1 row 0 + 4 * air.cols.values.offset_bit_2 row 0)).val +
        65536 * (air.cols.values.addr_word_1 row 0).val < 32) := by omega
    simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses, h_mem,
      h_ge]

  /-- The offset bits are the address's low three bits (`aligned_address`). -/
  private lemma offset_eq
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_mem : is_memory air row = 1)
  :
    (air.cols.values.offset_bit_0 row 0 + 2 * air.cols.values.offset_bit_1 row 0 +
      4 * air.cols.values.offset_bit_2 row 0).val = dispatch_addr air row % 8
  :=
    (aligned_address air row h_ext_asm h_wf_asm h_constraints h_mem).1

  /-- On a load row the double word is written back unchanged: `shift` is 0 (constraint 36) and
      so is every term the store flags gate (constraints 37 to 40). -/
  private lemma load_values
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_sb : air.cols.values.instruction.is_sb row 0 = 0)
    (h_sh : air.cols.values.instruction.is_sh row 0 = 0)
    (h_sw : air.cols.values.instruction.is_sw row 0 = 0)
    (h_sd : air.cols.values.instruction.is_sd row 0 = 0)
  :
    let v := air.cols.values
    v.memory_access.access.value_0 row 0 = v.memory_access.prev_value_0 row 0 ∧
    v.memory_access.access.value_1 row 0 = v.memory_access.prev_value_1 row 0 ∧
    v.memory_access.access.value_2 row 0 = v.memory_access.prev_value_2 row 0 ∧
    v.memory_access.access.value_3 row 0 = v.memory_access.prev_value_3 row 0
  := by
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, c36, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_36, constraint_37, constraint_38, constraint_39, constraint_40, h_sb, h_sh,
      h_sw, h_sd, zero_mul, add_zero, sub_zero, sub_eq_zero] at c36 c37 c38 c39 c40
    simp only [c36, mul_zero, add_zero] at c37 c38 c39 c40
    exact ⟨ c37, c38, c39, c40 ⟩

  /-- With the offset bits 0 or 1, `o0 + o1 = 0` makes both 0 (constraint 21, on a word row). -/
  private lemma bits_zero_2 {o0 o1 : FKB} (h0 : o0 = 0 ∨ o0 = 1) (h1 : o1 = 0 ∨ o1 = 1)
      (h : o0 + o1 = 0) : o0 = 0 ∧ o1 = 0 := by
    rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
      first | exact ⟨ rfl, rfl ⟩ | exact absurd h (by decide)

  /-- With the offset bits 0 or 1, `o0 + o1 + o2 = 0` makes all three 0 (constraint 22, on a
      double-word row). -/
  private lemma bits_zero_3 {o0 o1 o2 : FKB} (h0 : o0 = 0 ∨ o0 = 1) (h1 : o1 = 0 ∨ o1 = 1)
      (h2 : o2 = 0 ∨ o2 = 1) (h : o0 + o1 + o2 = 0) : o0 = 0 ∧ o1 = 0 ∧ o2 = 0 := by
    rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
      first | exact ⟨ rfl, rfl, rfl ⟩ | exact absurd h (by decide)

  /-! ### One opcode at a time -/

  private theorem dataFlow_LB
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lb : air.cols.values.instruction.is_lb row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lb air row h_constraints h_is_lb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_lo, h_hi ⟩ := h_split (by simp [f0, f1, f7])
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, -, -, -, -, -, -,
      c25, c26, -, -, -, -, c31, -, -, -, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_25, constraint_26, constraint_31, constraint_35, f0, f1, f2, f3,
      f4, f5, f6, f7, f8, f9, f10, sub_eq_zero] at c17 c25 c26 c31 c35
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Byte
              (BitVec.ofNat 8 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      refine load_byte_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega)
        (Nat.mod_lt _ (by norm_num)) rfl ?_
      rw [← h_off]
      simp only [h0] at c26
      have h_sbv : (air.cols.values.selected_byte row 0).val < 256 := by
        rcases c17 with o | o <;> simp [o] at c25 <;> rw [c25] <;> assumption
      have h_a0 : (air.cols.values.instruction.op_a_value_0 row 0).val % 256 =
          (air.cols.values.selected_byte row 0).val := by
        simp at c26
        rcases c31 with m | m <;> rw [m] at c26 <;> simp at c26 <;> rw [c26]
        · rw [Nat.mod_eq_of_lt h_sbv]
        · rw [val_add_of_lt (by rw [show (65280 : FKB).val = 65280 from rfl]; omega),
            show (65280 : FKB).val = 65280 from rfl]
          omega
      have h_sp := byte_split h_lo h_hi
      generalize (air.cols.values.selected_limb row 0 - air.cols.values.mem_limb_low_byte row 0) *
        2122383361 = H at h_sp h_hi c25
      obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
        (air.cols.values.memory_access.prev_value_0 row 0)
        (air.cols.values.memory_access.prev_value_1 row 0)
        (air.cols.values.memory_access.prev_value_2 row 0)
        (air.cols.values.memory_access.prev_value_3 row 0)
      obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
      rcases c17 with o0 | o0 <;>
        rcases selected_limb_cases air row h_constraints with
          ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
        have hk := congrArg Fin.val hsl <;>
        rw [o0] at c25 <;> simp at c25 <;> have hs := congrArg Fin.val c25 <;>
        rw [o0, o1, o2] <;> simp only [l0, l1, l2, l3, l4, l5, l6, l7, Nat.reduceMul, e0, e1, e2,
          e3, e4, e5, e6, e7] <;>
        apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
        clear * - h_a0 hs hk h_sp h_lo h_hi <;> omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Byte ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Byte (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_LBU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lbu : air.cols.values.instruction.is_lbu row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lbu air row h_constraints h_is_lbu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_lo, h_hi ⟩ := h_split (by simp [f0, f1, f7])
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, -, -, -, -, -, -,
      c25, c26, -, -, -, -, -, -, -, -, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_25, constraint_26, constraint_35, f0, f1, f2, f3, f4, f5, f6,
      f7, f8, f9, f10, sub_eq_zero] at c17 c25 c26 c35
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Byte
              (BitVec.ofNat 8 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      refine load_byte_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega)
        (Nat.mod_lt _ (by norm_num)) rfl ?_
      rw [← h_off]
      simp [h0] at c26
      have h_a0 := congrArg Fin.val c26
      have h_sp := byte_split h_lo h_hi
      generalize (air.cols.values.selected_limb row 0 - air.cols.values.mem_limb_low_byte row 0) *
        2122383361 = H at h_sp h_hi c25
      obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
        (air.cols.values.memory_access.prev_value_0 row 0)
        (air.cols.values.memory_access.prev_value_1 row 0)
        (air.cols.values.memory_access.prev_value_2 row 0)
        (air.cols.values.memory_access.prev_value_3 row 0)
      obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
      rcases c17 with o0 | o0 <;>
        rcases selected_limb_cases air row h_constraints with
          ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
        have hk := congrArg Fin.val hsl <;>
        rw [o0] at c25 <;> simp at c25 <;> have hs := congrArg Fin.val c25 <;>
        rw [o0, o1, o2] <;> simp only [l0, l1, l2, l3, l4, l5, l6, l7, Nat.reduceMul, e0, e1, e2,
          e3, e4, e5, e6, e7] <;>
        apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
        clear * - h_a0 hs hk h_sp h_lo h_hi <;> omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Byte ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Byte (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_LH
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lh : air.cols.values.instruction.is_lh row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lh air row h_constraints h_is_lh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c18, c19, c20, -, -, -, -,
      -, c26, -, -, -, -, -, -, -, -, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_18, constraint_19, constraint_20, constraint_26, constraint_35, f0, f1, f2, f3,
      f4, f5, f6, f7, f8, f9, f10, sub_eq_zero] at c18 c19 c20 c26 c35
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    have h_bound : dispatch_addr air row % 8 + 2 ≤ 8 := by
      rw [← h_off, c20]
      rcases c18 with o1 | o1 <;> rcases c19 with o2 | o2 <;> rw [o1, o2] <;>
        simp only [l0, l2, l4, l6] <;> omega
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Half
              (BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      simp [h0] at c26
      have h_a0 := congrArg Fin.val c26
      obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
        (air.cols.values.memory_access.prev_value_0 row 0)
        (air.cols.values.memory_access.prev_value_1 row 0)
        (air.cols.values.memory_access.prev_value_2 row 0)
        (air.cols.values.memory_access.prev_value_3 row 0)
      obtain ⟨ b0, b1 ⟩ := half_bytes (air.cols.values.instruction.op_a_value_0 row 0).val
      refine load_half_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega) h_bound rfl
        ?_ ?_ <;> rw [← h_off, c20] <;>
        rcases selected_limb_cases air row h_constraints with
            ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
        have hk := congrArg Fin.val hsl <;>
        rw [o1, o2] <;> simp only [l0, l2, l4, l6, Nat.reduceAdd, Nat.reduceMul, e0, e1, e2, e3,
          e4, e5, e6, e7, b0, b1] <;>
        apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
        clear * - h_a0 hk <;> omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Half ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Half (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_LHU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lhu : air.cols.values.instruction.is_lhu row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lhu air row h_constraints h_is_lhu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c18, c19, c20, -, -, -, -,
      -, c26, -, -, -, -, -, -, -, -, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_18, constraint_19, constraint_20, constraint_26, constraint_35, f0, f1, f2, f3,
      f4, f5, f6, f7, f8, f9, f10, sub_eq_zero] at c18 c19 c20 c26 c35
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    have h_bound : dispatch_addr air row % 8 + 2 ≤ 8 := by
      rw [← h_off, c20]
      rcases c18 with o1 | o1 <;> rcases c19 with o2 | o2 <;> rw [o1, o2] <;>
        simp only [l0, l2, l4, l6] <;> omega
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Half
              (BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      simp [h0] at c26
      have h_a0 := congrArg Fin.val c26
      obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
        (air.cols.values.memory_access.prev_value_0 row 0)
        (air.cols.values.memory_access.prev_value_1 row 0)
        (air.cols.values.memory_access.prev_value_2 row 0)
        (air.cols.values.memory_access.prev_value_3 row 0)
      obtain ⟨ b0, b1 ⟩ := half_bytes (air.cols.values.instruction.op_a_value_0 row 0).val
      refine load_half_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega) h_bound rfl
        ?_ ?_ <;> rw [← h_off, c20] <;>
        rcases selected_limb_cases air row h_constraints with
            ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
        have hk := congrArg Fin.val hsl <;>
        rw [o1, o2] <;> simp only [l0, l2, l4, l6, Nat.reduceAdd, Nat.reduceMul, e0, e1, e2, e3,
          e4, e5, e6, e7, b0, b1] <;>
        apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
        clear * - h_a0 hk <;> omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Half ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Half (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_LW
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lw : air.cols.values.instruction.is_lw row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lw air row h_constraints h_is_lw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, -, c21, -, -, -,
      -, c26, c27, -, -, -, -, -, -, c34, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_18, constraint_19, constraint_26, constraint_27, constraint_34,
      constraint_35, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, sub_eq_zero]
      at c17 c18 c19 c26 c27 c34 c35
    simp only [constraint_21, f4, f5, f9, add_zero, one_mul, zero_add] at c21
    obtain ⟨ ho0, ho1 ⟩ := bits_zero_2 c17 c18 c21
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    have h_bound : dispatch_addr air row % 8 + 4 ≤ 8 := by
      rw [← h_off, ho0, ho1]
      rcases c19 with o2 | o2 <;> rw [o2] <;> simp only [l0, l4] <;> omega
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Word
              (BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_1 row 0).val ++
                BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      simp [h0] at c26 c27
      have h_a0 := congrArg Fin.val c26
      have h_a1 := congrArg Fin.val c27
      obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
        (air.cols.values.memory_access.prev_value_0 row 0)
        (air.cols.values.memory_access.prev_value_1 row 0)
        (air.cols.values.memory_access.prev_value_2 row 0)
        (air.cols.values.memory_access.prev_value_3 row 0)
      obtain ⟨ b0, b1, b2, b3 ⟩ := word_bytes (air.cols.values.instruction.op_a_value_0 row 0).val
        (air.cols.values.instruction.op_a_value_1 row 0).val
      refine load_word_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega) h_bound rfl
        ?_ ?_ ?_ ?_ <;> rw [← h_off, ho0, ho1] <;>
        rcases selected_limb_cases air row h_constraints with
            ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
        rw [ho1] at o1 <;> (try exact absurd o1 (by decide)) <;>
        have hk := congrArg Fin.val hsl <;>
        rw [o2] at c34 <;> simp at c34 <;> have hl := congrArg Fin.val c34 <;>
        rw [o2] <;> simp only [l0, l4, Nat.reduceAdd, Nat.reduceMul, e0, e1, e2, e3, e4, e5, e6,
          e7, b0, b1, b2, b3] <;>
        apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
        clear * - h_a0 h_a1 hk hl <;> omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Word ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Word (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_LWU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lwu : air.cols.values.instruction.is_lwu row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_lwu air row h_constraints h_is_lwu
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, -, c21, -, -, -,
      -, c26, c27, -, -, -, -, -, -, c34, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_18, constraint_19, constraint_26, constraint_27, constraint_34,
      constraint_35, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, sub_eq_zero]
      at c17 c18 c19 c26 c27 c34 c35
    simp only [constraint_21, f4, f5, f9, add_zero, zero_add, one_mul] at c21
    obtain ⟨ ho0, ho1 ⟩ := bits_zero_2 c17 c18 c21
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    have h_bound : dispatch_addr air row % 8 + 4 ≤ 8 := by
      rw [← h_off, ho0, ho1]
      rcases c19 with o2 | o2 <;> rw [o2] <;> simp only [l0, l4] <;> omega
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Word
              (BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_1 row 0).val ++
                BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      simp [h0] at c26 c27
      have h_a0 := congrArg Fin.val c26
      have h_a1 := congrArg Fin.val c27
      obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
        (air.cols.values.memory_access.prev_value_0 row 0)
        (air.cols.values.memory_access.prev_value_1 row 0)
        (air.cols.values.memory_access.prev_value_2 row 0)
        (air.cols.values.memory_access.prev_value_3 row 0)
      obtain ⟨ b0, b1, b2, b3 ⟩ := word_bytes (air.cols.values.instruction.op_a_value_0 row 0).val
        (air.cols.values.instruction.op_a_value_1 row 0).val
      refine load_word_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega) h_bound rfl
        ?_ ?_ ?_ ?_ <;> rw [← h_off, ho0, ho1] <;>
        rcases selected_limb_cases air row h_constraints with
            ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
        rw [ho1] at o1 <;> (try exact absurd o1 (by decide)) <;>
        have hk := congrArg Fin.val hsl <;>
        rw [o2] at c34 <;> simp at c34 <;> have hl := congrArg Fin.val c34 <;>
        rw [o2] <;> simp only [l0, l4, Nat.reduceAdd, Nat.reduceMul, e0, e1, e2, e3, e4, e5, e6,
          e7, b0, b1, b2, b3] <;>
        apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
        clear * - h_a0 h_a1 hk hl <;> omega
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Word ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Word (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_LD
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_ld : air.cols.values.instruction.is_ld row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_ld air row h_constraints h_is_ld
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    obtain ⟨ hv0, hv1, hv2, hv3 ⟩ := load_values air row h_constraints f7 f8 f9 f10
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, -, -, c22, -, -,
      -, c26, c27, c28, c29, -, -, -, -, -, c35, - ⟩ := constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_18, constraint_19, constraint_26, constraint_27, constraint_28,
      constraint_29, constraint_35, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, sub_eq_zero]
      at c17 c18 c19 c26 c27 c28 c29 c35
    simp only [constraint_22, f6, f10, add_zero, zero_add, one_mul] at c22
    obtain ⟨ ho0, ho1, ho2 ⟩ := bits_zero_3 c17 c18 c19 c22
    have h_al : dispatch_addr air row % 8 = 0 := by
      rw [← h_off, ho0, ho1, ho2]; exact offset_lits.1
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, hv0, hv1, hv2, hv3]
    rcases c35 with h0 | h0
    · simp [h0] at c26 c27 c28 c29
      have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMem (dispatch_addr air row) .Double
              (U64w.toBV #v[air.cols.values.memory_access.prev_value_0 row 0,
                air.cols.values.memory_access.prev_value_1 row 0,
                air.cols.values.memory_access.prev_value_2 row 0,
                air.cols.values.memory_access.prev_value_3 row 0]) ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0, c26, c27, c28, c29]
      rw [h_disp]
      exact load_double_flow state _ _ _ _ _ (by omega) rfl rfl
    · have h_disp : RV64IM_Interactions.V3.bus_operations
          { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
          [ .ReadMemAny (dispatch_addr air row) .Double ] := by
        simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
          RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
          f7, f8, f9, f10, h0]
      rw [h_disp]
      exact load_any_flow state _ _ (dispatch_addr air row % 8) _ _ .Double (by omega)
        (by simp only [RV64IM.width_of_mem_width]; omega) rfl

  private theorem dataFlow_SB
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sb : air.cols.values.instruction.is_sb row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sb air row h_constraints h_is_sb
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, h_reg, h_split ⟩ :=
      bus_facts air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ h_lo, h_hi ⟩ := h_split (by simp [f0, f1, f7])
    obtain ⟨ h_rlo, h_rhi ⟩ := h_reg f7
    clear h_split h_reg
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, c36, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp only [constraint_17, constraint_36, constraint_37, constraint_38, constraint_39,
      constraint_40, f7, f8, f9, f10, zero_mul, add_zero, one_mul, sub_eq_zero]
      at c17 c36 c37 c38 c39 c40
    have c17' := bool_cases c17
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem]
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Byte
            (BitVec.ofNat 8 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
        f7, f8, f9, f10]
    rw [h_disp]
    refine store_byte_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega)
      (Nat.mod_lt _ (by norm_num)) ?_
    intro i hi
    rw [← h_off]
    have h_sp := byte_split h_lo h_hi
    have h_rsp := byte_split h_rlo h_rhi
    have pl := patch_low (r := air.cols.values.register_low_byte row 0)
      (split_eq (air.cols.values.selected_limb row 0) (air.cols.values.mem_limb_low_byte row 0))
      h_hi h_rlo
    have ph := patch_high (x := air.cols.values.selected_limb row 0) h_lo h_rlo
    generalize (air.cols.values.selected_limb row 0 - air.cols.values.mem_limb_low_byte row 0) *
      2122383361 = H at h_sp h_hi pl
    generalize (air.cols.values.instruction.op_a_value_0 row 0 -
      air.cols.values.register_low_byte row 0) * 2122383361 = R at h_rsp h_rhi
    obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
      (air.cols.values.memory_access.prev_value_0 row 0)
      (air.cols.values.memory_access.prev_value_1 row 0)
      (air.cols.values.memory_access.prev_value_2 row 0)
      (air.cols.values.memory_access.prev_value_3 row 0)
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7 ⟩ := toBV_bytes
      (air.cols.values.memory_access.access.value_0 row 0)
      (air.cols.values.memory_access.access.value_1 row 0)
      (air.cols.values.memory_access.access.value_2 row 0)
      (air.cols.values.memory_access.access.value_3 row 0)
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    rcases c17' with o0 | o0 <;>
      rcases selected_limb_cases air row h_constraints with
        ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
      have hk := congrArg Fin.val hsl <;>
      simp only [o0, o1, o2, sub_zero, sub_self, one_mul, mul_one, zero_mul, mul_zero, add_zero,
        zero_add] at c36 c37 c38 c39 c40 <;>
      simp only [c36] at c37 c38 c39 c40 <;>
      simp only [← hsl] at c37 c38 c39 c40 <;>
      have n0 := congrArg Fin.val c37 <;> have n1 := congrArg Fin.val c38 <;>
      have n2 := congrArg Fin.val c39 <;> have n3 := congrArg Fin.val c40 <;>
      simp only [pl, ph] at n0 n1 n2 n3 <;>
      rw [o0, o1, o2] <;> simp only [l0, l1, l2, l3, l4, l5, l6, l7] <;>
      interval_cases i <;>
      simp only [Nat.reduceMul, Nat.reduceEqDiff, if_true, if_false, e0, e1, e2, e3, e4, e5, e6,
        e7, w0, w1, w2, w3, w4, w5, w6, w7] <;>
      apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
      clear * - n0 n1 n2 n3 hk h_sp h_hi h_lo h_rsp h_rhi h_rlo <;> omega

  private theorem dataFlow_SH
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sh : air.cols.values.instruction.is_sh row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sh air row h_constraints h_is_sh
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c18, c19, c20, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, c36, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_18, constraint_19, constraint_20, f2, f3, f8, sub_eq_zero] at c18 c19 c20
    simp only [constraint_36, constraint_37, constraint_38, constraint_39, constraint_40, f7, f8,
      f9, f10, zero_mul, add_zero, one_mul, sub_eq_zero] at c36 c37 c38 c39 c40
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    have h_bound : dispatch_addr air row % 8 + 2 ≤ 8 := by
      rw [← h_off, c20]
      rcases c18 with o1 | o1 <;> rcases c19 with o2 | o2 <;> rw [o1, o2] <;>
        simp only [l0, l2, l4, l6] <;> omega
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem]
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Half
            (BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
        f7, f8, f9, f10]
    rw [h_disp]
    refine store_half_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega) h_bound ?_
    intro i hi
    rw [← h_off, c20]
    obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
      (air.cols.values.memory_access.prev_value_0 row 0)
      (air.cols.values.memory_access.prev_value_1 row 0)
      (air.cols.values.memory_access.prev_value_2 row 0)
      (air.cols.values.memory_access.prev_value_3 row 0)
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7 ⟩ := toBV_bytes
      (air.cols.values.memory_access.access.value_0 row 0)
      (air.cols.values.memory_access.access.value_1 row 0)
      (air.cols.values.memory_access.access.value_2 row 0)
      (air.cols.values.memory_access.access.value_3 row 0)
    obtain ⟨ b0, b1 ⟩ := half_bytes (air.cols.values.instruction.op_a_value_0 row 0).val
    rcases selected_limb_cases air row h_constraints with
        ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ | ⟨ o1, o2, hsl ⟩ <;>
      simp only [o1, o2, sub_zero, sub_self, one_mul, mul_one, zero_mul, mul_zero, add_zero,
        zero_add] at c37 c38 c39 c40 <;>
      simp only [c36] at c37 c38 c39 c40 <;>
      simp only [← hsl, add_sub_cancel] at c37 c38 c39 c40 <;>
      have n0 := congrArg Fin.val c37 <;> have n1 := congrArg Fin.val c38 <;>
      have n2 := congrArg Fin.val c39 <;> have n3 := congrArg Fin.val c40 <;>
      rw [o1, o2] <;> simp only [l0, l2, l4, l6] <;>
      interval_cases i <;>
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, if_true, if_false, e0, e1, e2,
        e3, e4, e5, e6, e7, w0, w1, w2, w3, w4, w5, w6, w7, b0, b1] <;>
      apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
      clear * - n0 n1 n2 n3 <;> omega

  private theorem dataFlow_SW
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sw : air.cols.values.instruction.is_sw row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sw air row h_constraints h_is_sw
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, -, c21, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, c36, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_18, constraint_19, sub_eq_zero] at c17 c18 c19
    simp only [constraint_21, f4, f5, f9, add_zero, zero_add, one_mul] at c21
    obtain ⟨ ho0, ho1 ⟩ := bits_zero_2 c17 c18 c21
    simp only [constraint_36, constraint_37, constraint_38, constraint_39, constraint_40, f7, f8,
      f9, f10, zero_mul, add_zero, one_mul, sub_eq_zero] at c36 c37 c38 c39 c40
    simp only [c36, mul_zero, add_zero] at c37 c38 c39 c40
    obtain ⟨ l0, l1, l2, l3, l4, l5, l6, l7 ⟩ := offset_lits
    have h_bound : dispatch_addr air row % 8 + 4 ≤ 8 := by
      rw [← h_off, ho0, ho1]
      rcases c19 with o2 | o2 <;> rw [o2] <;> simp only [l0, l4] <;> omega
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem]
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Word
            (BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_1 row 0).val ++
              BitVec.ofNat 16 (air.cols.values.instruction.op_a_value_0 row 0).val) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
        f7, f8, f9, f10]
    rw [h_disp]
    refine store_word_flow state _ _ (dispatch_addr air row % 8) _ _ _ (by omega) h_bound ?_
    intro i hi
    rw [← h_off, ho0, ho1]
    obtain ⟨ e0, e1, e2, e3, e4, e5, e6, e7 ⟩ := toBV_bytes
      (air.cols.values.memory_access.prev_value_0 row 0)
      (air.cols.values.memory_access.prev_value_1 row 0)
      (air.cols.values.memory_access.prev_value_2 row 0)
      (air.cols.values.memory_access.prev_value_3 row 0)
    obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7 ⟩ := toBV_bytes
      (air.cols.values.memory_access.access.value_0 row 0)
      (air.cols.values.memory_access.access.value_1 row 0)
      (air.cols.values.memory_access.access.value_2 row 0)
      (air.cols.values.memory_access.access.value_3 row 0)
    obtain ⟨ b0, b1, b2, b3 ⟩ := word_bytes (air.cols.values.instruction.op_a_value_0 row 0).val
      (air.cols.values.instruction.op_a_value_1 row 0).val
    rcases c19 with o2 | o2 <;>
      simp only [o2, sub_zero, sub_self, one_mul, zero_mul, add_zero, add_sub_cancel]
        at c37 c38 c39 c40 <;>
      have n0 := congrArg Fin.val c37 <;> have n1 := congrArg Fin.val c38 <;>
      have n2 := congrArg Fin.val c39 <;> have n3 := congrArg Fin.val c40 <;>
      rw [o2] <;> simp only [l0, l4] <;>
      interval_cases i <;>
      simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, if_true, if_false, e0, e1, e2,
        e3, e4, e5, e6, e7, w0, w1, w2, w3, w4, w5, w6, w7, b0, b1, b2, b3] <;>
      apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat, Nat.reducePow] <;>
      clear * - n0 n1 n2 n3 <;> omega

  private theorem dataFlow_SD
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sd : air.cols.values.instruction.is_sd row 0 = 1)
  :
    DataFlow air row state
  := by
    have hf := flags_of_is_sd air row h_constraints h_is_sd
    simp only [flags, List.cons.injEq, and_true] at hf
    obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := hf
    have h_mem : is_memory air row = 1 := by
      simp [is_memory, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10]
    have h_off := offset_eq air row h_ext_asm h_wf_asm h_constraints h_mem
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c17, c18, c19, -, -, c22, -, -, -,
      -, -, -, -, -, -, -, -, -, -, c36, c37, c38, c39, c40, - ⟩ :=
      constraints_of_allHold air row h_constraints
    simp [constraint_17, constraint_18, constraint_19, sub_eq_zero] at c17 c18 c19
    simp only [constraint_22, f6, f10, zero_add, one_mul] at c22
    obtain ⟨ ho0, ho1, ho2 ⟩ := bits_zero_3 c17 c18 c19 c22
    have h_al : dispatch_addr air row % 8 = 0 := by
      rw [← h_off, ho0, ho1, ho2]; exact offset_lits.1
    simp only [constraint_36, constraint_37, constraint_38, constraint_39, constraint_40, f7, f8,
      f9, f10, zero_mul, add_zero, sub_zero, one_mul, sub_eq_zero] at c36 c37 c38 c39 c40
    simp only [c36, mul_zero, add_zero, zero_add, add_sub_cancel] at c37 c38 c39 c40
    unfold DataFlow
    dsimp only
    rw [access_ops air row h_ext_asm h_wf_asm h_constraints h_mem, c37, c38, c39, c40]
    have h_disp : RV64IM_Interactions.V3.bus_operations
        { Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory } =
        [ .WriteMem (dispatch_addr air row) .Double
            (U64w.toBV #v[air.cols.values.instruction.op_a_value_0 row 0,
              air.cols.values.instruction.op_a_value_1 row 0,
              air.cols.values.instruction.op_a_value_2 row 0,
              air.cols.values.instruction.op_a_value_3 row 0]) ] := by
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, dispatch_addr, f0, f1, f2, f3, f4, f5, f6,
        f7, f8, f9, f10]
    rw [h_disp]
    exact store_double_flow state _ _ _ _ _ (by omega) rfl

  /-! ### Every row -/

  /-- On every row that satisfies the constraints, given what its messages are promised, the
      row's data flow holds in every Sail state. A row with no flag set sends its messages at
      multiplicity 0 and its dispatch with opcode 0, which `bus_operations` reads as no
      operation. -/
  theorem dataFlow_of_allHold
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    DataFlow air row state
  := by
    rcases flag_cases air row h_constraints with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [flags, List.cons.injEq, and_true] at h <;>
      obtain ⟨ f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 ⟩ := h
    · unfold DataFlow
      simp [RV64IM_Interactions.V3.bus_operations, bus_row, MemoryReadWriteChip.AbsBuses,
        RV64IM_Interactions.V3.mem_width_of_opcode, RV64IM.operation_list_effect, f0, f1, f2, f3,
        f4, f5, f6, f7, f8, f9, f10]
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

end MemoryReadWriteChip.Spec
