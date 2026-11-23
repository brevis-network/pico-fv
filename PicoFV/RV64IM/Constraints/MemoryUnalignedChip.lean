import PicoFV.RV64IM.Extraction.MemoryUnalignedChip
import PicoFV.RV64IM.Airs.MemoryUnalignedChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryUnalignedChip — constraints

`MemoryUnalignedChip::eval` (`vm/src/chips/chips/riscv_memory/unaligned/constraints.rs`, Pico
v3.1.6 `6aa644efeff9ddbec6beb538200f98f2a70f5d8e`) emits 59 constraints and 28 bus messages,
extracted in `PicoFV.RV64IM.Extraction.MemoryUnalignedChip`. This file restates the constraints
on the named columns of `Valid_MemoryUnalignedChip` (`Airs/MemoryUnalignedChip.lean`). Pico paths
below are under `vm/src/chips/chips/`, `vm/src/chips/` or `vm/src/`, at v3.1.6.

The chip takes the loads and stores whose address is not a multiple of their width, and is
correct for an aligned one too (`riscv_memory/unaligned/mod.rs:1-6`). A row reads the dword
holding the access's first byte at `clk + Memory`, and the next dword at `clk + C` when the
access runs past it (`riscv_memory/unaligned/mod.rs:8-12`).

Each restatement's `_equiv` lemma proves it equal to its extracted constraint, and
`allHold_iff_allHold_simplified` proves that `row_constraint_list` holds all 59: no restatement
differs from the extraction, and none is missing. The column names come from the layout in
`Airs/MemoryUnalignedChip.lean`; that they are Pico's names is checked by reading the layout
against `columns.rs`, not by these lemmas.

`constraints.rs` reads in these sections, which is the order the extraction follows:
`39-64` the instruction and its flags, `65-94` the address `op_b + op_c` through boolean
carries, `95-117` the one-hot byte offset in the dword, `118-129` whether the access runs into
the next dword, `130-154` the next dword's address, `155-177` the two accesses, `178-210` the
byte splits, `211-272` what a load reads and its sign, `273-309` what a store writes, and
`310-324` that a store misses the program's code.

Each constraint's docstring gives its Pico line. In those of constraints 32 to 54, `w` is the
sixteen bytes of the two dwords before the access and `r` the eight of `op_a`, as in
`constraints.rs`.

The bus messages are not restated: `allHold_simplified` keeps the extracted
`constrain_interactions`.
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

    /-- The extracted `allHold` with each constraint replaced by its restatement; the bus
        messages stay as extracted. -/
    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_MemoryUnalignedChip F ExtF)
      (row : ℕ)
    : Prop :=
      MemoryUnalignedChip.Extraction.constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_MemoryUnalignedChip F ExtF)
      (row : ℕ)
    :
      MemoryUnalignedChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition,
        constraint_and_interaction_simplification]

  end constraint_simplification

end MemoryUnalignedChip.ConstraintsAndBuses
