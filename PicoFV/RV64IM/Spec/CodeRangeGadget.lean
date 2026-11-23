import PicoFV.RV64IM.Constraints.CodeRangeGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# CodeRangeGadget — a store misses the code range it looks up

`CodeRangeCols::eval` (`vm/src/chips/gadgets/code_range.rs`, Pico v3.2.0) proves that a write of
`width` bytes at `addr` lands on no byte of the range `[code_start, code_end)` it looks up from
the Program table: either it ends at or below the range's start, or it starts at or above its
end.

What is proved is about the range as read from the row's own columns. The Program table's
promise (`V3.CodeRangeBus.Spec`) gives only that its four pieces are below 2^16, not that they
are this program's code range: no Lean statement names that range yet (`RVSail/BusesV3.lean`,
`CodeRangeBus.Spec`). So these theorems do not yet say that a store misses the program's code;
they say it misses whatever range the Program table answers.

`gadget_spec` states this on the gadget's column values, for a chip that embeds the gadget;
`spec` states it for the standalone wrapper air. Their premises are the ones the gadget's
documentation (`code_range.rs`, the doc comments of `CodeRangeCols::eval` and `populate`) leaves
to its caller: the row is a store (`is_store = 1`), `addr` is two 16-bit pieces and `width` is
below 2^16. The rest comes from the gadget's constraints and two bus promises: the Program
table answers the code-range lookup with four 16-bit pieces (`V3.CodeRangeBus.Spec`), and the
byte table's `U16Range` check bounds each piece of the distance (`ByteBus.Spec`, opcode 8). Both
are assumed through `bus_row_all_wf_asm`, the check over all of the row's messages.

The argument, from the comment in `eval`: with `below ∈ {0, 1}` and `borrow ∈ {0, 1, 2}`, every
side of the two distance equations lies within 2^18 of zero, far below the field's modulus, so
they hold in the integers. Then `distance_0 + 2^16 distance_1` is `code_start - (addr + width)`
below the code and `addr - code_end` above it, and it is not negative.

`wf_asrt` and `ext_asrt` say the gadget's messages owe nothing to the tables that answer them:
the gadget only looks up, with multiplicity `is_store`, which its caller keeps boolean.
-/

namespace CodeRangeGadget.Spec

  open RV64IM_Interactions.V3
  open CodeRangeGadget.Interactions
  open CodeRangeGadget.Interpretations

  set_option maxHeartbeats 1_000_000_000

  /-- On a store row, the write `[addr, addr + width)` misses the looked-up range
      `[code_start, code_end)`: it ends at or below the range's start, or starts at or above its
      end. Each address is read from its two 16-bit pieces. The range is the one in the row's
      columns, which this statement does not tie to the program's code range. -/
  theorem gadget_spec
    (is_store addr_0 addr_1 store_width
     code_start_0 code_start_1 code_end_0 code_end_1
     below borrow distance_0 distance_1 : FKB)
    (h_bus_wf_asm :
      bus_row_all_wf_asm
        (CodeRangeGadget.AbsBuses is_store code_start_0 code_start_1 code_end_0 code_end_1
          distance_0 distance_1))
    (h_constraints :
      CodeRangeGadget.AbsConstraints is_store addr_0 addr_1 store_width
        code_start_0 code_start_1 code_end_0 code_end_1 below borrow distance_0 distance_1)
    (h_is_store : is_store = 1)
    (h_addr : addr_0.val < 65536 ∧ addr_1.val < 65536)
    (h_width : store_width.val < 65536)
  :
    addr_0.val + 65536 * addr_1.val + store_width.val ≤
        code_start_0.val + 65536 * code_start_1.val ∨
      code_end_0.val + 65536 * code_end_1.val ≤ addr_0.val + 65536 * addr_1.val
  := by
    obtain ⟨ h_wf_asm, h_code_range_wf_asm ⟩ := h_bus_wf_asm
    subst h_is_store
    simp [bus_row_wf_asm, CodeRangeGadget.AbsBuses, RV64IM_Interactions.ByteBus.Spec]
      at h_wf_asm
    simp [bus_row_code_range_wf_asm, CodeRangeGadget.AbsBuses, CodeRangeBusEntryInstance,
      CodeRangeBusEntry.deserialise, CodeRangeBus.Spec] at h_code_range_wf_asm
    obtain ⟨ h_d0, h_d1 ⟩ := h_wf_asm
    obtain ⟨ h_cs0, h_cs1, h_ce0, h_ce1 ⟩ := h_code_range_wf_asm
    obtain ⟨ h_a0, h_a1 ⟩ := h_addr
    obtain ⟨ h_below, h_borrow, h_low, h_high ⟩ := h_constraints
    simp only [one_mul, sub_eq_zero] at h_low h_high
    have h_b : borrow.val ≤ 2 := by
      rcases mul_eq_zero.mp h_borrow with h | h
      · rcases mul_eq_zero.mp h with h | h
        · simp [h]
        · rw [sub_eq_zero.mp h]; decide
      · rw [sub_eq_zero.mp h]; decide
    rcases mul_eq_zero.mp h_below with h | h
    · -- `below = 0`: the write starts at or above the code's end.
      subst h
      have e0 : distance_0 + code_end_0 = addr_0 + 65536 * borrow := by
        rw [h_low]; ring
      have e1 : distance_1 + code_end_1 + borrow = addr_1 := by
        rw [h_high]; ring
      have v0 := congrArg Fin.val e0
      have v1 := congrArg Fin.val e1
      simp only [Fin.val_add, Fin.val_mul] at v0 v1
      norm_num at v0 v1
      -- Every side is far below the modulus, so the equations hold in ℕ.
      clear h_low h_high h_borrow h_below e0 e1
      repeat rw [Nat.mod_eq_of_lt (by omega)] at v0
      repeat rw [Nat.mod_eq_of_lt (by omega)] at v1
      right
      omega
    · -- `below = 1`: the write ends at or below the code's start.
      rw [sub_eq_zero.mp h] at h_low h_high
      have e0 : distance_0 + addr_0 + store_width = code_start_0 + 65536 * borrow := by
        rw [h_low]; ring
      have e1 : distance_1 + addr_1 + borrow = code_start_1 := by
        rw [h_high]; ring
      have v0 := congrArg Fin.val e0
      have v1 := congrArg Fin.val e1
      simp only [Fin.val_add, Fin.val_mul] at v0 v1
      norm_num at v0 v1
      clear h_low h_high h_borrow h_below e0 e1 h
      repeat rw [Nat.mod_eq_of_lt (by omega)] at v0
      repeat rw [Nat.mod_eq_of_lt (by omega)] at v1
      left
      omega

  /-- `gadget_spec` for the standalone wrapper air, on its named columns. As there, the range is
      the one in the row's columns, not yet tied to the program's code range. -/
  theorem spec
    [Field ExtF]
    (air : Valid_CodeRangeGadgetAir FKB ExtF)
    (row : ℕ)
    (h_bus_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : CodeRangeGadget.Extraction.allHold air row)
    (h_is_store : air.cols.is_store row 0 = 1)
    (h_addr : (air.cols.addr_0 row 0).val < 65536 ∧ (air.cols.addr_1 row 0).val < 65536)
    (h_width : (air.cols.store_width row 0).val < 65536)
  :
    (air.cols.addr_0 row 0).val + 65536 * (air.cols.addr_1 row 0).val +
        (air.cols.store_width row 0).val ≤
        (air.cols.gadget.code_start_0 row 0).val + 65536 * (air.cols.gadget.code_start_1 row 0).val ∨
      (air.cols.gadget.code_end_0 row 0).val + 65536 * (air.cols.gadget.code_end_1 row 0).val ≤
        (air.cols.addr_0 row 0).val + 65536 * (air.cols.addr_1 row 0).val
  := by
    rw [bus_row_abs] at h_bus_wf_asm
    exact gadget_spec _ _ _ _ _ _ _ _ _ _ _ _
      h_bus_wf_asm (allHold_abs air row h_constraints) h_is_store h_addr h_width

  /-- The gadget's messages promise nothing to the tables that answer them: no entry has
      multiplicity `-1` when `is_store` is boolean, as its caller keeps it. -/
  theorem wf_asrt
    [Field ExtF]
    (air : Valid_CodeRangeGadgetAir FKB ExtF)
    (row : ℕ)
    (h_is_store : air.cols.is_store row 0 = 0 ∨ air.cols.is_store row 0 = 1)
  :
    bus_row_all_wf_asrt (bus_row air row)
  := by
    simp [bus_row_all_wf_asrt, bus_row_wf_asrt, bus_row_code_range_wf_asrt, bus_row, CodeRangeGadget.AbsBuses,
      CodeRangeBusEntryInstance, CodeRangeBusEntry.deserialise]
    rcases h_is_store with h | h <;> simp [h]

  /-- Neither the byte table nor the code-range lookup has external facts to assert. -/
  theorem ext_asrt
    [Field ExtF]
    (air : Valid_CodeRangeGadgetAir FKB ExtF)
    (row : ℕ)
  :
    bus_row_all_ext_asrt (bus_row air row)
  := by
    simp [bus_row_all_ext_asrt, bus_row_ext_asrt, bus_row_code_range_ext_asrt, bus_row, CodeRangeGadget.AbsBuses,
      CodeRangeBusEntryInstance]

end CodeRangeGadget.Spec
