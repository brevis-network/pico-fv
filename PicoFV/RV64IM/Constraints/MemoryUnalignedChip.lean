import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.Extraction.MemoryUnalignedChip
import PicoFV.RV64IM.Airs.MemoryUnalignedChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryUnalignedChip — constraints and bus messages

Citations read at Pico v3.2.0.

`MemoryUnalignedChip::eval` (`vm/src/chips/chips/riscv_memory/unaligned/constraints.rs`) emits
59 constraints and 28 bus messages,
extracted in `PicoFV.RV64IM.Extraction.MemoryUnalignedChip`. This file restates them on the named
columns of `Valid_MemoryUnalignedChip` (`Airs/MemoryUnalignedChip.lean`), with an `_equiv` lemma
per constraint, and sorts the messages by contract (`AbsBuses`). Pico paths below are under
`vm/src/chips/chips/`, `vm/src/chips/` or `vm/src/`.

The chip takes the loads and stores whose address is not a multiple of their width, and is
correct for an aligned one too (`riscv_memory/unaligned/mod.rs:1-6`). A row reads the dword
holding the access's first byte at `clk + Memory`, and the next dword at `clk + C` when the
access runs past it (`riscv_memory/unaligned/mod.rs:8-12`).

Each restatement's `_equiv` lemma proves it equal to its extracted constraint, and
`allHold_iff_allHold_simplified` proves that `row_constraint_list` holds all 59 and `raw_bus_row`
all 28 messages: no restatement differs from the extraction, and none is missing.
`bus_row_equiv` proves that sorting `raw_bus_row` by contract gives `AbsBuses`. The column names
come from the layout in `Airs/MemoryUnalignedChip.lean`; that they are Pico's names is checked by
reading the layout against `columns.rs`, not by these lemmas.

`constraints.rs` reads in these sections, which is the order the extraction follows:
`39-64` the instruction and its flags, `65-94` the address `op_b + op_c` through boolean
carries, `95-117` the one-hot byte offset in the dword, `118-129` whether the access runs into
the next dword, `130-154` the next dword's address, `155-177` the two accesses, `178-210` the
byte splits, `211-272` what a load reads and its sign, `273-309` what a store writes, and
`310-324` that a store misses the program's code.

Each constraint's docstring gives its Pico line. In those of constraints 32 to 54, `w` is the
sixteen bytes of the two dwords before the access and `r` the eight of `op_a`, as in
`constraints.rs`.
-/

namespace MemoryUnalignedChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      /-- `is_lb ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lb row 0) * ((v.instruction.is_lb row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lbu ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lbu row 0) * ((v.instruction.is_lbu row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lh ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lh row 0) * ((v.instruction.is_lh row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lhu ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lhu row 0) * ((v.instruction.is_lhu row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lw ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lw row 0) * ((v.instruction.is_lw row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lwu ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lwu row 0) * ((v.instruction.is_lwu row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_ld ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_ld row 0) * ((v.instruction.is_ld row 0) - 1)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sb ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sb row 0) * ((v.instruction.is_sb row 0) - 1)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sh ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sh row 0) * ((v.instruction.is_sh row 0) - 1)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sw ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sw row 0) * ((v.instruction.is_sw row 0) - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sd ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sd row 0) * ((v.instruction.is_sd row 0) - 1)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The flag sum `is_lb + … + is_sd` is 0 or 1
          (`riscv_memory/read_write/constraints.rs:208`, called at
          `riscv_memory/unaligned/constraints.rs:45`). -/
      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The first address carry `(op_b_0 + op_c_0 - addr_word_0) / 2^16` is 0 or 1
          (`riscv_memory/unaligned/constraints.rs:73-74`); `2130673921` is `2^16`'s inverse. -/
      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921) * (((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The second carry `(op_b_1 + op_c_1 + k1 - addr_word_1) / 2^16` is 0 or 1
          (`riscv_memory/unaligned/constraints.rs:75-77`). -/
      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921) * ((((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The third carry `(op_b_2 + op_c_2 + k2) / 2^16` is 0 or 1
          (`riscv_memory/unaligned/constraints.rs:78-79`). -/
      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921) * (((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The fourth carry `(op_b_3 + op_c_3 + k3) / 2^16` is 0 or 1
          (`riscv_memory/unaligned/constraints.rs:80-81`). -/
      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.instruction.op_b_value_3 row 0)) + (v.instruction.op_c_value_3 row 0)) + ((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) * (((((0 + (v.instruction.op_b_value_3 row 0)) + (v.instruction.op_c_value_3 row 0)) + ((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `addr_limb1_inv · addr_word_1 = is_lb + … + is_sd`: on a real row the address's limb 1 is
          not 0, so the access is at or above `2^16`
          (`riscv_memory/unaligned/constraints.rs:90-93`). -/
      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((0 + ((v.addr_limb1_inv row 0) * (v.addr_word_1 row 0))) - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_0 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_0 row 0) * ((v.offset_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_1 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_1 row 0) * ((v.offset_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_2 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_2 row 0) * ((v.offset_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_3 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_3 row 0) * ((v.offset_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_4 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_4 row 0) * ((v.offset_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_5 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_5 row 0) * ((v.offset_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_6 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_6 row 0) * ((v.offset_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_7 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:104`). -/
      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_7 row 0) * ((v.offset_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_0 + … + offset_7 = is_lb + … + is_sd`: with each offset boolean, exactly one is
          set on a real row and none on padding (`riscv_memory/unaligned/constraints.rs:108`). -/
      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((((((0 + (v.offset_0 row 0)) + (v.offset_1 row 0)) + (v.offset_2 row 0)) + (v.offset_3 row 0)) + (v.offset_4 row 0)) + (v.offset_5 row 0)) + (v.offset_6 row 0)) + (v.offset_7 row 0)) - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `cross` says the access runs into the next dword: a halfword from offset 7, a word from 5,
          a doubleword from 1 (`riscv_memory/unaligned/constraints.rs:122-128`). -/
      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.cross row 0) - ((((((v.instruction.is_lh row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_sh row 0)) * (v.offset_7 row 0)) + ((((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) + (v.instruction.is_sw row 0)) * (((v.offset_5 row 0) + (v.offset_6 row 0)) + (v.offset_7 row 0)))) + (((v.instruction.is_ld row 0) + (v.instruction.is_sd row 0)) * (((((((v.offset_1 row 0) + (v.offset_2 row 0)) + (v.offset_3 row 0)) + (v.offset_4 row 0)) + (v.offset_5 row 0)) + (v.offset_6 row 0)) + (v.offset_7 row 0))))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `next_carry ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:137`). -/
      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.next_carry row 0) * ((v.next_carry row 0) - 1)) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `next_carry · (dword0 - 0xfff8) = 0`, where `dword0 = addr_word_0 - Σ k · offset_k` is the
          low limb of the dword's address: the next dword's address carries only from `0xfff8`
          (`riscv_memory/unaligned/constraints.rs:138`, `dword0` at `:109`). `65528` is `0xfff8`. -/
      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((0 + (v.next_carry row 0)) * (((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) - 65528)) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `(dword0 - 0xfff8) · next_carry_inv = is_lb + … + is_sd - next_carry`: on a real row with
          no carry, `dword0 ≠ 0xfff8`. With constraint 28, `next_carry` is 1 on a real row exactly
          when `dword0 = 0xfff8` (`riscv_memory/unaligned/constraints.rs:139-142`). -/
      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) - 65528) * (v.next_carry_inv row 0)) - (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - (v.next_carry row 0))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The flag sum `is_lb + … + is_sd` is 0 or 1 again: it gates the first access, and
          `eval_memory_access_lite` makes its gate boolean (`machine/builder/riscv_memory.rs:137`,
          called at `riscv_memory/unaligned/constraints.rs:159-169`). -/
      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `cross ∈ {0, 1}`: it gates the second access, and `eval_memory_access_lite` makes its
          gate boolean (`machine/builder/riscv_memory.rs:137`, called at
          `riscv_memory/unaligned/constraints.rs:170-176`). -/
      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.cross row 0) * ((v.cross row 0) - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `seen_0` is limb 0 of the eight bytes from the address on,
          `Σ_k offset_k · (w[k] + 256 · w[k+1])` (`riscv_memory/unaligned/constraints.rs:216-222`).
          `w` is the sixteen bytes of the two dwords before the access
          (`riscv_memory/unaligned/constraints.rs:206`): limb `i`'s low byte is `low_bytes_i` and
          its high byte `(prev_value_i - low_bytes_i) / 256` (`gadgets/u16_to_u8.rs:71-72`).
          `2122383361` is `256`'s inverse. -/
      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_0 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_0 row 0) + ((((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_1 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.first_bytes.low_bytes_1 row 0) + ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_2 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.first_bytes.low_bytes_2 row 0) + ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_3 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `seen_1` is limb 1 of the eight bytes from the address on,
          `Σ_k offset_k · (w[k+2] + 256 · w[k+3])`
          (`riscv_memory/unaligned/constraints.rs:216-222`). -/
      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_1 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_1 row 0) + ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_2 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.first_bytes.low_bytes_2 row 0) + ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_3 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.second_bytes.low_bytes_0 row 0) + ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_1 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `seen_2` is limb 2 of the eight bytes from the address on,
          `Σ_k offset_k · (w[k+4] + 256 · w[k+5])`
          (`riscv_memory/unaligned/constraints.rs:216-222`). -/
      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_2 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_2 row 0) + ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_3 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.second_bytes.low_bytes_0 row 0) + ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_1 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.second_bytes.low_bytes_1 row 0) + ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_2 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `seen_3` is limb 3 of the eight bytes from the address on,
          `Σ_k offset_k · (w[k+6] + 256 · w[k+7])`
          (`riscv_memory/unaligned/constraints.rs:216-222`). -/
      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_3 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.second_bytes.low_bytes_0 row 0) + ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_1 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.second_bytes.low_bytes_1 row 0) + ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_2 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.second_bytes.low_bytes_2 row 0) + ((((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_3 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `seen_byte = Σ_k offset_k · w[k]`, the byte at the address, which a byte load reads
          (`riscv_memory/unaligned/constraints.rs:223-227`). -/
      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_byte row 0) - ((((((((0 + ((v.offset_0 row 0) * (v.first_bytes.low_bytes_0 row 0))) + ((v.offset_1 row 0) * (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361))) + ((v.offset_2 row 0) * (v.first_bytes.low_bytes_1 row 0))) + ((v.offset_3 row 0) * (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361))) + ((v.offset_4 row 0) * (v.first_bytes.low_bytes_2 row 0))) + ((v.offset_5 row 0) * (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361))) + ((v.offset_6 row 0) * (v.first_bytes.low_bytes_3 row 0))) + ((v.offset_7 row 0) * (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, limb 0 of `op_a` is `seen_byte` on `LB` and `LBU`, plus `0xff00` on
          `LB` when `msb` is set; `seen_0` on the wider loads; and `op_a`'s own on a store row
          (`riscv_memory/unaligned/constraints.rs:237-240`, asserted at `:247-250`). `65280` is
          `0xff00`. -/
      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_0 row 0) - ((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) * (v.seen_byte row 0)) + ((((((v.instruction.is_lh row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.seen_0 row 0))) + (((v.instruction.is_lb row 0) * (v.msb row 0)) * 65280)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_0 row 0))))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, limb 1 of `op_a` is `seen_1` on `LW`, `LWU` and `LD`; the sign fill
          `msb · 0xffff` on `LB` and `LH`; 0 on `LBU` and `LHU`; and `op_a`'s own on a store row
          (`riscv_memory/unaligned/constraints.rs:241-243`, asserted at `:247-250`). -/
      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_1 row 0) - ((((((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.seen_1 row 0)) + ((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) * (v.msb row 0)) * 65535)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_1 row 0))))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, limb 2 of `op_a` is `seen_2` on `LD`; the sign fill `msb · 0xffff` on
          `LB`, `LH` and `LW`; 0 on the other loads; and `op_a`'s own on a store row
          (`riscv_memory/unaligned/constraints.rs:244`, asserted at `:247-250`). -/
      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_2 row 0) - ((((v.instruction.is_ld row 0) * (v.seen_2 row 0)) + (((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)) * (v.msb row 0)) * 65535)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_2 row 0))))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, limb 3 of `op_a` is `seen_3` on `LD`; the sign fill `msb · 0xffff` on
          `LB`, `LH` and `LW`; 0 on the other loads; and `op_a`'s own on a store row
          (`riscv_memory/unaligned/constraints.rs:245`, asserted at `:247-250`). -/
      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_3 row 0) - ((((v.instruction.is_ld row 0) * (v.seen_3 row 0)) + (((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)) * (v.msb row 0)) * 65535)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `instruction.op_a_0 ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:251`). -/
      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.op_a_0 row 0) * ((v.instruction.op_a_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- On `LB`, `sign_src = 256 · seen_byte`, whose bit 15 is the byte's bit 7
          (`riscv_memory/unaligned/constraints.rs:256-258`). -/
      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lb row 0) * ((v.sign_src row 0) - (256 * (v.seen_byte row 0)))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- On `LH`, `sign_src = seen_0` (`riscv_memory/unaligned/constraints.rs:259`). -/
      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lh row 0) * ((v.sign_src row 0) - (v.seen_0 row 0))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- On `LW`, `sign_src = seen_1`, the loaded word's limb 1
          (`riscv_memory/unaligned/constraints.rs:260`). -/
      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lw row 0) * ((v.sign_src row 0) - (v.seen_1 row 0))) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `msb ∈ {0, 1}` (`riscv_memory/unaligned/constraints.rs:261`). -/
      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.msb row 0) * ((v.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `msb = 0` on `LBU`, `LHU`, `LWU` and `LD`
          (`riscv_memory/unaligned/constraints.rs:262-264`). -/
      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((v.instruction.is_lbu row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.msb row 0)) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 0 of the first dword after the access is `written(0) + 256 · written(1)`
          (`riscv_memory/unaligned/constraints.rs:303`). `written(i)` is byte `i` of `w` plus
          `offset_k · cov[i-k] · (r[i-k] - w[i])` for each offset `k`: a store at offset `k` that
          covers its byte `i - k` writes that byte of `op_a` (`r`,
          `riscv_memory/unaligned/constraints.rs:200-205`), and every other byte keeps its value
          (`written` at `:291-298`, `cov` at `:281-290`). -/
      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_0 row 0) - (((v.first_bytes.low_bytes_0 row 0) + (((v.offset_0 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_0 row 0)))) + ((((((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361) + (((v.offset_0 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 0 of the second dword after the access is `written(8) + 256 · written(9)`
          (`riscv_memory/unaligned/constraints.rs:304-307`; `written` as in constraint 47). -/
      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_0 row 0) - (((((((((v.second_bytes.low_bytes_0 row 0) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_5 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_6 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_7 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + ((((((((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_6 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 1 of the first dword after the access is `written(2) + 256 · written(3)`
          (`riscv_memory/unaligned/constraints.rs:303`). -/
      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_1 row 0) - (((((v.first_bytes.low_bytes_1 row 0) + (((v.offset_0 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.first_bytes.low_bytes_1 row 0)))) + (((v.offset_1 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.first_bytes.low_bytes_1 row 0)))) + (((v.offset_2 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_1 row 0)))) + ((((((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) + (((v.offset_0 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_2 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 1 of the second dword after the access is `written(10) + 256 · written(11)`
          (`riscv_memory/unaligned/constraints.rs:304-307`). -/
      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_1 row 0) - (((((((v.second_bytes.low_bytes_1 row 0) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_7 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.second_bytes.low_bytes_1 row 0)))) + ((((((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 2 of the first dword after the access is `written(4) + 256 · written(5)`
          (`riscv_memory/unaligned/constraints.rs:303`). -/
      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_2 row 0) - (((((((v.first_bytes.low_bytes_2 row 0) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_1 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_2 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_3 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_4 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_2 row 0)))) + ((((((((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_2 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_4 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 2 of the second dword after the access is `written(12) + 256 · written(13)`
          (`riscv_memory/unaligned/constraints.rs:304-307`). -/
      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_2 row 0) - (((((v.second_bytes.low_bytes_2 row 0) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_2 row 0)))) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.second_bytes.low_bytes_2 row 0)))) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.second_bytes.low_bytes_2 row 0)))) + ((((((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 3 of the first dword after the access is `written(6) + 256 · written(7)`
          (`riscv_memory/unaligned/constraints.rs:303`). -/
      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_3 row 0) - (((((((((v.first_bytes.low_bytes_3 row 0) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_3 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_4 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_5 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_6 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + ((((((((((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_4 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_6 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Limb 3 of the second dword after the access is `written(14) + 256 · written(15)`
          (`riscv_memory/unaligned/constraints.rs:304-307`). -/
      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_3 row 0) - (((v.second_bytes.low_bytes_3 row 0) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_3 row 0)))) + ((((v.second.prev_value_3 row 0) - (v.second_bytes.low_bytes_3 row 0)) * 2122383361) * 256))) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `code_range.below ∈ {0, 1}` (`gadgets/code_range.rs:135`, called at
          `riscv_memory/unaligned/constraints.rs:316-322`). -/
      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.code_range.below row 0) * ((v.code_range.below row 0) - 1)) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `code_range.borrow ∈ {0, 1, 2}` (`gadgets/code_range.rs:137-139`, called at
          `riscv_memory/unaligned/constraints.rs:316-322`). -/
      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((v.code_range.borrow row 0) * ((v.code_range.borrow row 0) - 1)) * ((v.code_range.borrow row 0) - 2)) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- On a store row, `code_range.distance_0 = low + 2^16 · borrow`, where `low` is
          `code_start_0 - addr_word_0 - width` below the code and `addr_word_0 - code_end_0` above
          it (`gadgets/code_range.rs:149-150, 154-156`). The width is
          `is_sb + 2 · is_sh + 4 · is_sw + 8 · is_sd`
          (`riscv_memory/unaligned/constraints.rs:311-315`). -/
      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * ((v.code_range.distance_0 row 0) - ((((v.code_range.below row 0) * (((0 + (v.code_range.code_start_0 row 0)) - (v.addr_word_0 row 0)) - ((((0 + (v.instruction.is_sb row 0)) + ((v.instruction.is_sh row 0) * 2)) + ((v.instruction.is_sw row 0) * 4)) + ((v.instruction.is_sd row 0) * 8)))) + ((1 - (v.code_range.below row 0)) * ((v.addr_word_0 row 0) - (v.code_range.code_end_0 row 0)))) + (65536 * (v.code_range.borrow row 0))))) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- On a store row, `code_range.distance_1 = high - borrow`, where `high` is
          `code_start_1 - addr_word_1` below the code and `addr_word_1 - code_end_1` above it
          (`gadgets/code_range.rs:151-152, 157-159`). -/
      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * ((v.code_range.distance_1 row 0) - ((((v.code_range.below row 0) * ((0 + (v.code_range.code_start_1 row 0)) - (v.addr_word_1 row 0))) + ((1 - (v.code_range.below row 0)) * ((v.addr_word_1 row 0) - (v.code_range.code_end_1 row 0)))) - (v.code_range.borrow row 0)))) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row, constraint_1 air row, constraint_2 air row,
          constraint_3 air row, constraint_4 air row, constraint_5 air row,
          constraint_6 air row, constraint_7 air row, constraint_8 air row,
          constraint_9 air row, constraint_10 air row, constraint_11 air row,
          constraint_12 air row, constraint_13 air row, constraint_14 air row,
          constraint_15 air row, constraint_16 air row, constraint_17 air row,
          constraint_18 air row, constraint_19 air row, constraint_20 air row,
          constraint_21 air row, constraint_22 air row, constraint_23 air row,
          constraint_24 air row, constraint_25 air row, constraint_26 air row,
          constraint_27 air row, constraint_28 air row, constraint_29 air row,
          constraint_30 air row, constraint_31 air row, constraint_32 air row,
          constraint_33 air row, constraint_34 air row, constraint_35 air row,
          constraint_36 air row, constraint_37 air row, constraint_38 air row,
          constraint_39 air row, constraint_40 air row, constraint_41 air row,
          constraint_42 air row, constraint_43 air row, constraint_44 air row,
          constraint_45 air row, constraint_46 air row, constraint_47 air row,
          constraint_48 air row, constraint_49 air row, constraint_50 air row,
          constraint_51 air row, constraint_52 air row, constraint_53 air row,
          constraint_54 air row, constraint_55 air row, constraint_56 air row,
          constraint_57 air row, constraint_58 air row
        ]

    end row_constraints

    section row_buses

      /-- The row's 28 messages, `(multiplicity, [tag, ...fields])`, as extracted. Tags are
          Pico's `LookupType`: 1 Memory, 2 Program, 5 Byte. -/
      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
          List (FKB × List FKB) :=
        let v := air.cols
        -- 0: the memory dispatch, received from the CPU chip (`riscv_memory/unaligned/constraints.rs:44-63`)
        [ ((0 - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))), [1, (((((((((((0 + ((0 + (v.instruction.is_lb row 0)) * 10)) + ((0 + (v.instruction.is_lbu row 0)) * 13)) + ((0 + (v.instruction.is_lh row 0)) * 11)) + ((0 + (v.instruction.is_lhu row 0)) * 14)) + ((0 + (v.instruction.is_lw row 0)) * 12)) + ((0 + (v.instruction.is_lwu row 0)) * 45)) + ((0 + (v.instruction.is_ld row 0)) * 46)) + ((0 + (v.instruction.is_sb row 0)) * 15)) + ((0 + (v.instruction.is_sh row 0)) * 16)) + ((0 + (v.instruction.is_sw row 0)) * 17)) + ((0 + (v.instruction.is_sd row 0)) * 47)), (v.instruction.op_a_value_0 row 0), (v.instruction.op_a_value_1 row 0), (v.instruction.op_a_value_2 row 0), (v.instruction.op_a_value_3 row 0), (v.instruction.op_b_value_0 row 0), (v.instruction.op_b_value_1 row 0), (v.instruction.op_b_value_2 row 0), (v.instruction.op_b_value_3 row 0), (v.instruction.op_c_value_0 row 0), (v.instruction.op_c_value_1 row 0), (v.instruction.op_c_value_2 row 0), (v.instruction.op_c_value_3 row 0), (v.instruction.op_a_0 row 0), ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), (v.chunk row 0), (v.clk row 0)]),
        -- 1: `U16Range` of `addr_word_1` (`riscv_memory/unaligned/constraints.rs:82-89`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 8, (v.addr_word_1 row 0), 0, 0, 0]),
        -- 2: `BitRange(13)` of `dword0 / 8`, the dword's low piece over 8 (`riscv_memory/unaligned/constraints.rs:109-116`); `1864368129` is `8`'s inverse
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 9, (((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) * 1864368129), 0, 13, 0]),
        -- 3: `U16Range` of the next dword's second piece `addr_word_1 + next_carry`, on a row that crosses (`riscv_memory/unaligned/constraints.rs:145-153`)
          ((v.cross row 0), [5, 8, ((0 + (v.addr_word_1 row 0)) + (v.next_carry row 0)), 0, 0, 0]),
        -- 4: `U16Range` of the first access's `diff_16bit_limb` (`machine/builder/range_check.rs:88-95`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 8, (v.first.access.diff_16bit_limb row 0), 0, 0, 0]),
        -- 5: `BitRange(9)` of the first access's `diff_hi9` (`machine/builder/range_check.rs:96-102`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 9, (v.first.access.diff_hi9 row 0), 0, 9, 0]),
        -- 6: the read of the first dword at `prev_clk` (`machine/builder/riscv_memory.rs:195-200`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [1, (v.chunk row 0), ((((v.clk row 0) + 0) - ((v.first.access.diff_16bit_limb row 0) + ((v.first.access.diff_hi9 row 0) * 65536))) - 1), ((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))), (0 + (v.addr_word_1 row 0)), 0, (v.first.prev_value_0 row 0), (v.first.prev_value_1 row 0), (v.first.prev_value_2 row 0), (v.first.prev_value_3 row 0)]),
        -- 7: the write of the first dword at `clk + 0` (`machine/builder/riscv_memory.rs:203-208`)
          ((0 - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))), [1, (v.chunk row 0), ((v.clk row 0) + 0), ((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))), (0 + (v.addr_word_1 row 0)), 0, (v.first.access.value_0 row 0), (v.first.access.value_1 row 0), (v.first.access.value_2 row 0), (v.first.access.value_3 row 0)]),
        -- 8: `U16Range` of the second access's `diff_16bit_limb`, on a row that crosses (`machine/builder/range_check.rs:88-95`)
          ((v.cross row 0), [5, 8, (v.second.access.diff_16bit_limb row 0), 0, 0, 0]),
        -- 9: `BitRange(9)` of the second access's `diff_hi9`, on a row that crosses (`machine/builder/range_check.rs:96-102`)
          ((v.cross row 0), [5, 9, (v.second.access.diff_hi9 row 0), 0, 9, 0]),
        -- 10: the read of the next dword at its `prev_clk`, on a row that crosses (`machine/builder/riscv_memory.rs:195-200`)
          ((v.cross row 0), [1, (v.chunk row 0), ((((v.clk row 0) + 1) - ((v.second.access.diff_16bit_limb row 0) + ((v.second.access.diff_hi9 row 0) * 65536))) - 1), ((((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) + 8) - ((0 + (v.next_carry row 0)) * 65536)), ((0 + (v.addr_word_1 row 0)) + (v.next_carry row 0)), 0, (v.second.prev_value_0 row 0), (v.second.prev_value_1 row 0), (v.second.prev_value_2 row 0), (v.second.prev_value_3 row 0)]),
        -- 11: the write of the next dword at `clk + 1`, on a row that crosses (`machine/builder/riscv_memory.rs:203-208`)
          ((0 - (v.cross row 0)), [1, (v.chunk row 0), ((v.clk row 0) + 1), ((((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) + 8) - ((0 + (v.next_carry row 0)) * 65536)), ((0 + (v.addr_word_1 row 0)) + (v.next_carry row 0)), 0, (v.second.access.value_0 row 0), (v.second.access.value_1 row 0), (v.second.access.value_2 row 0), (v.second.access.value_3 row 0)]),
        -- 12: `U8Range` of the first dword's limb 0, its low and high byte (`machine/builder/range_check.rs:15-30`, called at `riscv_memory/unaligned/constraints.rs:188-193`); `2122383361` is `256`'s inverse
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 7, 0, 0, (v.first_bytes.low_bytes_0 row 0), (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361)]),
        -- 13: `U8Range` of the first dword's limb 1
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 7, 0, 0, (v.first_bytes.low_bytes_1 row 0), (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)]),
        -- 14: `U8Range` of the first dword's limb 2
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 7, 0, 0, (v.first_bytes.low_bytes_2 row 0), (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)]),
        -- 15: `U8Range` of the first dword's limb 3
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 7, 0, 0, (v.first_bytes.low_bytes_3 row 0), (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)]),
        -- 16: `U8Range` of the second dword's limb 0, on a row that crosses (`riscv_memory/unaligned/constraints.rs:194-199`)
          ((v.cross row 0), [5, 7, 0, 0, (v.second_bytes.low_bytes_0 row 0), (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)]),
        -- 17: `U8Range` of the second dword's limb 1
          ((v.cross row 0), [5, 7, 0, 0, (v.second_bytes.low_bytes_1 row 0), (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)]),
        -- 18: `U8Range` of the second dword's limb 2
          ((v.cross row 0), [5, 7, 0, 0, (v.second_bytes.low_bytes_2 row 0), (((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361)]),
        -- 19: `U8Range` of the second dword's limb 3
          ((v.cross row 0), [5, 7, 0, 0, (v.second_bytes.low_bytes_3 row 0), (((v.second.prev_value_3 row 0) - (v.second_bytes.low_bytes_3 row 0)) * 2122383361)]),
        -- 20: `U8Range` of `op_a`'s limb 0, on a store row (`riscv_memory/unaligned/constraints.rs:200-205`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 7, 0, 0, (v.value_bytes.low_bytes_0 row 0), (((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361)]),
        -- 21: `U8Range` of `op_a`'s limb 1
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 7, 0, 0, (v.value_bytes.low_bytes_1 row 0), (((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361)]),
        -- 22: `U8Range` of `op_a`'s limb 2
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 7, 0, 0, (v.value_bytes.low_bytes_2 row 0), (((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361)]),
        -- 23: `U8Range` of `op_a`'s limb 3
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 7, 0, 0, (v.value_bytes.low_bytes_3 row 0), (((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361)]),
        -- 24: `U16Range` of `2 · sign_src - msb · 2^16`, the sign-bit check (`riscv_memory/unaligned/constraints.rs:265-271`)
          ((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)), [5, 8, ((2 * (v.sign_src row 0)) - ((v.msb row 0) * 65536)), 0, 0, 0]),
        -- 25: the `code_range` gadget's lookup of the code range (`gadgets/code_range.rs:126-134`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [2, (v.code_range.code_start_0 row 0), (v.code_range.code_start_1 row 0), (v.code_range.code_end_0 row 0), (v.code_range.code_end_1 row 0)]),
        -- 26: the gadget's `U16Range` of `distance_0` (`gadgets/code_range.rs:160-169`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 8, (v.code_range.distance_0 row 0), 0, 0, 0]),
        -- 27: the gadget's `U16Range` of `distance_1` (`gadgets/code_range.rs:160-169`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 8, (v.code_range.distance_1 row 0), 0, 0, 0]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_MemoryUnalignedChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    /-- The extracted `allHold` with each constraint and the bus messages replaced by their
        restatements. -/
    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_MemoryUnalignedChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_MemoryUnalignedChip FKB ExtF)
      (row : ℕ)
    :
      MemoryUnalignedChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition,
        constraint_and_interaction_simplification]

  end constraint_simplification

end MemoryUnalignedChip.ConstraintsAndBuses

namespace MemoryUnalignedChip

  open RV64IM_Interactions

  /-- The high byte `(x - lo) / 256` of a 16-bit piece `x` whose low byte is `lo`
      (`gadgets/u16_to_u8.rs:71-72`), meant at `FKB`, where `2122383361` is `256`'s inverse.
      Stated over any field so that at `FKB` it uses the field arithmetic of the restated
      constraints, not `Fin`'s. -/
  abbrev high_byte [Field F] (x lo : F) : F := (x - lo) * 2122383361

  /-- The 16-bit piece whose low byte is `x` and high byte `y`, meant at `FKB` as
      `high_byte`. -/
  abbrev limb [Field F] (x y : F) : F := x + y * 256

  /-- The number of bytes a store writes: 1, 2, 4 or 8 on a store row, 0 on any other row.
      `width` in `MemoryUnalignedChip::eval` (`riscv_memory/unaligned/constraints.rs:311-315`),
      the width it hands the `code_range` gadget. -/
  def store_width [Field F] (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : F :=
    let i := air.cols.instruction
    i.is_sb row 0 + i.is_sh row 0 * 2 + i.is_sw row 0 * 4 + i.is_sd row 0 * 8

  /-- The row's messages, sorted by contract. With `is_memory` the flags' sum, `is_store` the
      store flags' sum, `dword0 = addr_word_0 - Σ k · offset_k` the low piece of the dword
      holding the first byte, and `next0 = dword0 + 8 - 2^16 · next_carry`,
      `next1 = addr_word_1 + next_carry` the next dword's address:

      - `Memory`: the memory dispatch `[opcode, a, b, c, op_a_0, is_memory, chunk, clk]`,
        received at `-is_memory`, its opcode `Σ flag · opcode`;
      - `State`: the read of the dword `[chunk, prev_clk, dword0, addr_word_1, 0, prev_value]` at
        `+is_memory` and its write `[chunk, clk, dword0, addr_word_1, 0, value]` at
        `-is_memory`; then the read of the next dword `[chunk, prev_clk', next0, next1, 0,
        prev_value']` at `+cross` and its write `[chunk, clk + 1, next0, next1, 0, value']` at
        `-cross`;
      - `Byte`: at `+is_memory`, the address's second piece, `dword0 / 8`, the two pieces of the
        first access's `clk - prev_clk - 1` and the first dword's eight bytes; at `+cross`, the
        next dword's second piece, the two pieces of the second access's clock difference and
        the next dword's eight bytes; at `+is_store`, `op_a`'s eight bytes and the gadget's two
        distance checks; and the sign-bit check;
      - `CodeRange`: the gadget's lookup of the code range, at `+is_store`. -/
  def AbsBuses (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) : BusRow :=
    let v := air.cols
    let is_lb := v.instruction.is_lb row 0
    let is_lbu := v.instruction.is_lbu row 0
    let is_lh := v.instruction.is_lh row 0
    let is_lhu := v.instruction.is_lhu row 0
    let is_lw := v.instruction.is_lw row 0
    let is_lwu := v.instruction.is_lwu row 0
    let is_ld := v.instruction.is_ld row 0
    let is_sb := v.instruction.is_sb row 0
    let is_sh := v.instruction.is_sh row 0
    let is_sw := v.instruction.is_sw row 0
    let is_sd := v.instruction.is_sd row 0
    let is_store := is_sb + is_sh + is_sw + is_sd
    let is_memory := is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld + is_store
    let opcode := is_lb * 10 + is_lbu * 13 + is_lh * 11 + is_lhu * 14 + is_lw * 12 +
      is_lwu * 45 + is_ld * 46 + is_sb * 15 + is_sh * 16 + is_sw * 17 + is_sd * 47
    let cross := v.cross row 0
    let dword0 := v.addr_word_0 row 0 -
      (v.offset_1 row 0 + v.offset_2 row 0 * 2 + v.offset_3 row 0 * 3 + v.offset_4 row 0 * 4 +
        v.offset_5 row 0 * 5 + v.offset_6 row 0 * 6 + v.offset_7 row 0 * 7)
    let next0 := dword0 + 8 - v.next_carry row 0 * 65536
    let next1 := v.addr_word_1 row 0 + v.next_carry row 0
    let prev_clk := v.clk row 0 -
      (v.first.access.diff_16bit_limb row 0 + v.first.access.diff_hi9 row 0 * 65536) - 1
    let prev_clk' := v.clk row 0 + 1 -
      (v.second.access.diff_16bit_limb row 0 + v.second.access.diff_hi9 row 0 * 65536) - 1
    {
      Program := [],
      ALU := [],
      Byte := List.map RV64IM_Interactions.ByteBusEntry.deserialise [
        (is_memory, #v[8, v.addr_word_1 row 0, 0, 0, 0]),
        (is_memory, #v[9, dword0 * 1864368129, 0, 13, 0]),
        (cross, #v[8, next1, 0, 0, 0]),
        (is_memory, #v[8, v.first.access.diff_16bit_limb row 0, 0, 0, 0]),
        (is_memory, #v[9, v.first.access.diff_hi9 row 0, 0, 9, 0]),
        (cross, #v[8, v.second.access.diff_16bit_limb row 0, 0, 0, 0]),
        (cross, #v[9, v.second.access.diff_hi9 row 0, 0, 9, 0]),
        (is_memory, #v[7, 0, 0, v.first_bytes.low_bytes_0 row 0,
          high_byte (v.first.prev_value_0 row 0) (v.first_bytes.low_bytes_0 row 0)]),
        (is_memory, #v[7, 0, 0, v.first_bytes.low_bytes_1 row 0,
          high_byte (v.first.prev_value_1 row 0) (v.first_bytes.low_bytes_1 row 0)]),
        (is_memory, #v[7, 0, 0, v.first_bytes.low_bytes_2 row 0,
          high_byte (v.first.prev_value_2 row 0) (v.first_bytes.low_bytes_2 row 0)]),
        (is_memory, #v[7, 0, 0, v.first_bytes.low_bytes_3 row 0,
          high_byte (v.first.prev_value_3 row 0) (v.first_bytes.low_bytes_3 row 0)]),
        (cross, #v[7, 0, 0, v.second_bytes.low_bytes_0 row 0,
          high_byte (v.second.prev_value_0 row 0) (v.second_bytes.low_bytes_0 row 0)]),
        (cross, #v[7, 0, 0, v.second_bytes.low_bytes_1 row 0,
          high_byte (v.second.prev_value_1 row 0) (v.second_bytes.low_bytes_1 row 0)]),
        (cross, #v[7, 0, 0, v.second_bytes.low_bytes_2 row 0,
          high_byte (v.second.prev_value_2 row 0) (v.second_bytes.low_bytes_2 row 0)]),
        (cross, #v[7, 0, 0, v.second_bytes.low_bytes_3 row 0,
          high_byte (v.second.prev_value_3 row 0) (v.second_bytes.low_bytes_3 row 0)]),
        (is_store, #v[7, 0, 0, v.value_bytes.low_bytes_0 row 0,
          high_byte (v.instruction.op_a_value_0 row 0) (v.value_bytes.low_bytes_0 row 0)]),
        (is_store, #v[7, 0, 0, v.value_bytes.low_bytes_1 row 0,
          high_byte (v.instruction.op_a_value_1 row 0) (v.value_bytes.low_bytes_1 row 0)]),
        (is_store, #v[7, 0, 0, v.value_bytes.low_bytes_2 row 0,
          high_byte (v.instruction.op_a_value_2 row 0) (v.value_bytes.low_bytes_2 row 0)]),
        (is_store, #v[7, 0, 0, v.value_bytes.low_bytes_3 row 0,
          high_byte (v.instruction.op_a_value_3 row 0) (v.value_bytes.low_bytes_3 row 0)]),
        (is_lb + is_lh + is_lw, #v[8, 2 * v.sign_src row 0 - v.msb row 0 * 65536, 0, 0, 0]),
        (is_store, #v[8, v.code_range.distance_0 row 0, 0, 0, 0]),
        (is_store, #v[8, v.code_range.distance_1 row 0, 0, 0, 0])
      ],
      State := List.map RV64IM_Interactions.StateBusEntry.deserialise [
        (is_memory, #v[v.chunk row 0, prev_clk, dword0, v.addr_word_1 row 0, 0,
          v.first.prev_value_0 row 0, v.first.prev_value_1 row 0,
          v.first.prev_value_2 row 0, v.first.prev_value_3 row 0]),
        (-(is_memory), #v[v.chunk row 0, v.clk row 0, dword0, v.addr_word_1 row 0, 0,
          v.first.access.value_0 row 0, v.first.access.value_1 row 0,
          v.first.access.value_2 row 0, v.first.access.value_3 row 0]),
        (cross, #v[v.chunk row 0, prev_clk', next0, next1, 0,
          v.second.prev_value_0 row 0, v.second.prev_value_1 row 0,
          v.second.prev_value_2 row 0, v.second.prev_value_3 row 0]),
        (-(cross), #v[v.chunk row 0, v.clk row 0 + 1, next0, next1, 0,
          v.second.access.value_0 row 0, v.second.access.value_1 row 0,
          v.second.access.value_2 row 0, v.second.access.value_3 row 0])
      ],
      Memory := List.map MemoryBusEntry.deserialise [
        (-(is_memory), #v[opcode,
          v.instruction.op_a_value_0 row 0, v.instruction.op_a_value_1 row 0,
          v.instruction.op_a_value_2 row 0, v.instruction.op_a_value_3 row 0,
          v.instruction.op_b_value_0 row 0, v.instruction.op_b_value_1 row 0,
          v.instruction.op_b_value_2 row 0, v.instruction.op_b_value_3 row 0,
          v.instruction.op_c_value_0 row 0, v.instruction.op_c_value_1 row 0,
          v.instruction.op_c_value_2 row 0, v.instruction.op_c_value_3 row 0,
          v.instruction.op_a_0 row 0, is_memory, v.chunk row 0, v.clk row 0])
      ],
      CodeRange := [
        CodeRangeBusEntry.deserialise (is_store,
          #v[v.code_range.code_start_0 row 0, v.code_range.code_start_1 row 0,
             v.code_range.code_end_0 row 0, v.code_range.code_end_1 row 0])
      ]
    }

end MemoryUnalignedChip

namespace MemoryUnalignedChip.Interactions

  /-- The chip's messages on one row, sorted by contract. -/
  def bus_row (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
      RV64IM_Interactions.BusRow :=
    MemoryUnalignedChip.AbsBuses air row

  /-- Sorting the row's extracted messages gives `bus_row`. -/
  @[simp]
  lemma bus_row_equiv (air : Valid_MemoryUnalignedChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (MemoryUnalignedChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      RV64IM_Interactions.deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      MemoryUnalignedChip.AbsBuses,
      MemoryUnalignedChip.high_byte,
      pico_encapsulation,
    ]

end MemoryUnalignedChip.Interactions
