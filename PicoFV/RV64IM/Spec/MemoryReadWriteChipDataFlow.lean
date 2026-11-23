import PicoFV.RV64IM.Spec.MemoryReadWriteChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryReadWriteChip — what a row does to memory

The data flow of a row of `MemoryReadWriteChip` (`MemoryReadWriteChip::eval`,
`vm/src/chips/chips/riscv_memory/read_write/constraints.rs`, Pico v3.1.6
`6aa644efeff9ddbec6beb538200f98f2a70f5d8e`; messages in `Constraints/MemoryReadWriteChip.lean`).

A real row sends the memory argument two messages, a read of the double word at the aligned
address and its write back (`machine/builder/riscv_memory.rs:195-208` at v3.1.6), and receives
the memory dispatch from the CPU chip (`riscv_memory/read_write/constraints.rs:63-84` at v3.1.6).
`V3.bus_operations` reads the pair as a double-word `ReadMem` and `WriteMem` at the aligned
address, and the dispatch as an access of its opcode's width at `b + c`: a `WriteMem` of `a` for
a store, a `ReadMem` of `a` for a load, or a `ReadMemAny` for a load into `x0`.

- `bus_equiv_LB` … `bus_equiv_SD`, one per opcode, and `bus_equiv` for every row: in any Sail
  state that holds the double word the row reads, the dispatch's read holds too, so a load returns
  the bytes of that double word at `b + c` (`riscv_memory/read_write/constraints.rs:423-442` at
  v3.1.6); and the two operation lists leave the same state, so a store writes the double word
  back with the stored bytes patched in and a load writes it back unchanged
  (`riscv_memory/read_write/constraints.rs:587-595` at v3.1.6).

Each theorem assumes what the Memory promise's theorems assume (`Spec/MemoryReadWriteChip.lean`):
the row's constraints (`allHold`) and what its messages are promised (`bus_row_all_ext_asm`,
`bus_row_all_wf_asm`). That the double word read is the one memory holds is the memory
argument's promise, which these theorems take as the hypothesis of `bus_equiv_goal`.
`bus_operations` does not read the messages' `chunk`, `clk` and `prev_clk` fields, and nothing
here is said about them.
-/

namespace MemoryReadWriteChip.Spec

  open RV64IM_Interactions.V3
  open MemoryReadWriteChip.Interactions

  /-- The row's data flow in the Sail state `state`: if the reads among the row's messages to the
      memory argument hold in `state`, the read of the memory dispatch the row receives holds
      too, and the two lists of operations leave the same state. -/
  def bus_equiv_goal
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :
    Prop
  :=
    let memory_bus : RV64IM_Interactions.V3.BusRow := {
      Program := [], ALU := [], Byte := [], State := [], Memory := (bus_row air row).Memory
    }
    let state_bus : RV64IM_Interactions.V3.BusRow := {
      Program := [], ALU := [], Byte := [], State := (bus_row air row).State, Memory := []
    }
    (RV64IM.operation_list_effect
        (RV64IM_Interactions.V3.bus_operations state_bus) state).hypotheses →
      (RV64IM.operation_list_effect
          (RV64IM_Interactions.V3.bus_operations memory_bus) state).hypotheses ∧
      (RV64IM.operation_list_effect
          (RV64IM_Interactions.V3.bus_operations memory_bus) state).state =
        (RV64IM.operation_list_effect
          (RV64IM_Interactions.V3.bus_operations state_bus) state).state

  /-- On a load of a byte, sign-extended row (`is_lb = 1`), the row's data flow holds in every
      Sail state. -/
  theorem bus_equiv_LB
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lb : air.cols.values.instruction.is_lb row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a load of a byte, zero-extended row (`is_lbu = 1`), the row's data flow holds in every
      Sail state. -/
  theorem bus_equiv_LBU
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lbu : air.cols.values.instruction.is_lbu row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a load of a halfword, sign-extended row (`is_lh = 1`), the row's data flow holds in
      every Sail state. -/
  theorem bus_equiv_LH
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lh : air.cols.values.instruction.is_lh row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a load of a halfword, zero-extended row (`is_lhu = 1`), the row's data flow holds in
      every Sail state. -/
  theorem bus_equiv_LHU
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lhu : air.cols.values.instruction.is_lhu row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a load of a word, sign-extended row (`is_lw = 1`), the row's data flow holds in every
      Sail state. -/
  theorem bus_equiv_LW
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lw : air.cols.values.instruction.is_lw row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a load of a word, zero-extended row (`is_lwu = 1`), the row's data flow holds in every
      Sail state. -/
  theorem bus_equiv_LWU
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_lwu : air.cols.values.instruction.is_lwu row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a load of a doubleword row (`is_ld = 1`), the row's data flow holds in every Sail
      state. -/
  theorem bus_equiv_LD
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_ld : air.cols.values.instruction.is_ld row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a store of a byte row (`is_sb = 1`), the row's data flow holds in every Sail state. -/
  theorem bus_equiv_SB
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sb : air.cols.values.instruction.is_sb row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a store of a halfword row (`is_sh = 1`), the row's data flow holds in every Sail
      state. -/
  theorem bus_equiv_SH
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sh : air.cols.values.instruction.is_sh row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a store of a word row (`is_sw = 1`), the row's data flow holds in every Sail state. -/
  theorem bus_equiv_SW
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sw : air.cols.values.instruction.is_sw row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On a store of a doubleword row (`is_sd = 1`), the row's data flow holds in every Sail
      state. -/
  theorem bus_equiv_SD
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_is_sd : air.cols.values.instruction.is_sd row 0 = 1)
  :
    bus_equiv_goal air row state
  := by
    sorry

  /-- On every row, the row's data flow holds in every Sail state. A row with a flag set is one
      of the eleven above; a row with none sends its messages at multiplicity 0 and its dispatch
      with opcode 0, which `bus_operations` reads as no operation. -/
  theorem bus_equiv
    [Field ExtF]
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext_asm : bus_row_all_ext_asm (bus_row air row))
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    bus_equiv_goal air row state
  := by
    sorry

end MemoryReadWriteChip.Spec
