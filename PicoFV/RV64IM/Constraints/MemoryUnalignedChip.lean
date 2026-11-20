import PicoFV.RV64IM.RVSail.BusesV3
import PicoFV.RV64IM.Extraction.MemoryUnalignedChip
import PicoFV.RV64IM.Airs.MemoryUnalignedChip
import PicoFV.RV64IM.Constraints.CodeRangeGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryUnalignedChip — constraints

`MemoryUnalignedChip::eval` (`vm/src/chips/chips/riscv_memory/unaligned/constraints.rs`, Pico
v3.1.6 `6aa644efeff9ddbec6beb538200f98f2a70f5d8e`) emits 59 constraints and 28 bus messages,
extracted in `PicoFV.RV64IM.Extraction.MemoryUnalignedChip`. This file restates the constraints
on the named columns of `Valid_MemoryUnalignedChip` (`Airs/MemoryUnalignedChip.lean`), with an
`_equiv` lemma per constraint. Pico paths below are under `vm/src/chips/chips/` at v3.1.6.

The chip takes the loads and stores whose address is not a multiple of their width, and is
correct for an aligned one too (`unaligned/mod.rs:1-6`). A row reads the dword holding the
access's first byte at `clk + Memory`, and the next dword at `clk + C` when the access runs
past it (`mod.rs:7-12`).

Each restatement is tied to the extracted constraint by its `_equiv` lemma, so the two cannot
drift: a wrong column name does not typecheck.

`constraints.rs` reads in these sections, which is the order the extraction follows:
`39-64` the instruction and its flags, `65-94` the address `op_b + op_c` through boolean
carries, `95-117` the one-hot byte offset in the dword, `118-129` whether the access runs into
the next dword, `130-154` the next dword's address, `155-177` the two accesses, `178-210` the
byte splits, `211-272` what a load reads and its sign, `273-309` what a store writes, and
`310-324` that a store misses the program's code.

Only the constraints whose content is plain from the restatement itself — the booleanity ones —
carry a docstring here. The rest are deliberately left without one rather than given a Pico line
I have not checked them against, which is the next piece of work on this file: the read/write
chip's constraints each cite their line, and these should too.

**The bus messages are not sorted here yet.** `AbsBuses` and `bus_row_equiv`, which the
specification needs, come with the specification; this file is the constraints alone, so that
the column layout and the restatement can be reviewed before any proof rests on them.
-/

namespace MemoryUnalignedChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      /-- `is_lb ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lb row 0) * ((v.instruction.is_lb row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lbu ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lbu row 0) * ((v.instruction.is_lbu row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lh ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lh row 0) * ((v.instruction.is_lh row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lhu ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lhu row 0) * ((v.instruction.is_lhu row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lw ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lw row 0) * ((v.instruction.is_lw row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lwu ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lwu row 0) * ((v.instruction.is_lwu row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_ld ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_ld row 0) * ((v.instruction.is_ld row 0) - 1)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sb ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sb row 0) * ((v.instruction.is_sb row 0) - 1)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sh ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sh row 0) * ((v.instruction.is_sh row 0) - 1)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sw ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sw row 0) * ((v.instruction.is_sw row 0) - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sd ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_sd row 0) * ((v.instruction.is_sd row 0) - 1)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921) * (((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921) * ((((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921) * (((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.instruction.op_b_value_3 row 0)) + (v.instruction.op_c_value_3 row 0)) + ((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) * (((((0 + (v.instruction.op_b_value_3 row 0)) + (v.instruction.op_c_value_3 row 0)) + ((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((0 + ((v.addr_limb1_inv row 0) * (v.addr_word_1 row 0))) - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_0 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_0 row 0) * ((v.offset_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_1 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_1 row 0) * ((v.offset_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_2 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_2 row 0) * ((v.offset_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_3 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_3 row 0) * ((v.offset_3 row 0) - 1)) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_4 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_4 row 0) * ((v.offset_4 row 0) - 1)) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_5 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_5 row 0) * ((v.offset_5 row 0) - 1)) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_6 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_6 row 0) * ((v.offset_6 row 0) - 1)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_7 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.offset_7 row 0) * ((v.offset_7 row 0) - 1)) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((((((0 + (v.offset_0 row 0)) + (v.offset_1 row 0)) + (v.offset_2 row 0)) + (v.offset_3 row 0)) + (v.offset_4 row 0)) + (v.offset_5 row 0)) + (v.offset_6 row 0)) + (v.offset_7 row 0)) - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.cross row 0) - ((((((v.instruction.is_lh row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_sh row 0)) * (v.offset_7 row 0)) + ((((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) + (v.instruction.is_sw row 0)) * (((v.offset_5 row 0) + (v.offset_6 row 0)) + (v.offset_7 row 0)))) + (((v.instruction.is_ld row 0) + (v.instruction.is_sd row 0)) * (((((((v.offset_1 row 0) + (v.offset_2 row 0)) + (v.offset_3 row 0)) + (v.offset_4 row 0)) + (v.offset_5 row 0)) + (v.offset_6 row 0)) + (v.offset_7 row 0))))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `next_carry ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.next_carry row 0) * ((v.next_carry row 0) - 1)) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((0 + (v.next_carry row 0)) * (((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) - 65528)) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((0 + (v.addr_word_0 row 0)) - ((((((((0 + ((v.offset_0 row 0) * 0)) + ((v.offset_1 row 0) * 1)) + ((v.offset_2 row 0) * 2)) + ((v.offset_3 row 0) * 3)) + ((v.offset_4 row 0) * 4)) + ((v.offset_5 row 0) * 5)) + ((v.offset_6 row 0) * 6)) + ((v.offset_7 row 0) * 7))) - 65528) * (v.next_carry_inv row 0)) - (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - (v.next_carry row 0))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `cross ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.cross row 0) * ((v.cross row 0) - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_0 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_0 row 0) + ((((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_1 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.first_bytes.low_bytes_1 row 0) + ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_2 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.first_bytes.low_bytes_2 row 0) + ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_3 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_1 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_1 row 0) + ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_2 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.first_bytes.low_bytes_2 row 0) + ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_3 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.second_bytes.low_bytes_0 row 0) + ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_1 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_2 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_2 row 0) + ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.first_bytes.low_bytes_3 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.second_bytes.low_bytes_0 row 0) + ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_1 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.second_bytes.low_bytes_1 row 0) + ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_2 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_3 row 0) - ((((((((0 + ((v.offset_0 row 0) * ((v.first_bytes.low_bytes_3 row 0) + ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) * 256)))) + ((v.offset_1 row 0) * ((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_0 row 0) * 256)))) + ((v.offset_2 row 0) * ((v.second_bytes.low_bytes_0 row 0) + ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) * 256)))) + ((v.offset_3 row 0) * ((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_1 row 0) * 256)))) + ((v.offset_4 row 0) * ((v.second_bytes.low_bytes_1 row 0) + ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) * 256)))) + ((v.offset_5 row 0) * ((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_2 row 0) * 256)))) + ((v.offset_6 row 0) * ((v.second_bytes.low_bytes_2 row 0) + ((((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361) * 256)))) + ((v.offset_7 row 0) * ((((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361) + ((v.second_bytes.low_bytes_3 row 0) * 256))))) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.seen_byte row 0) - ((((((((0 + ((v.offset_0 row 0) * (v.first_bytes.low_bytes_0 row 0))) + ((v.offset_1 row 0) * (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361))) + ((v.offset_2 row 0) * (v.first_bytes.low_bytes_1 row 0))) + ((v.offset_3 row 0) * (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361))) + ((v.offset_4 row 0) * (v.first_bytes.low_bytes_2 row 0))) + ((v.offset_5 row 0) * (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361))) + ((v.offset_6 row 0) * (v.first_bytes.low_bytes_3 row 0))) + ((v.offset_7 row 0) * (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_0 row 0) - ((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) * (v.seen_byte row 0)) + ((((((v.instruction.is_lh row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.seen_0 row 0))) + (((v.instruction.is_lb row 0) * (v.msb row 0)) * 65280)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_0 row 0))))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_1 row 0) - ((((((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.seen_1 row 0)) + ((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) * (v.msb row 0)) * 65535)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_1 row 0))))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_2 row 0) - ((((v.instruction.is_ld row 0) * (v.seen_2 row 0)) + (((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)) * (v.msb row 0)) * 65535)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_2 row 0))))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_3 row 0) - ((((v.instruction.is_ld row 0) * (v.seen_3 row 0)) + (((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)) * (v.msb row 0)) * 65535)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `instruction.op_a_0 ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.op_a_0 row 0) * ((v.instruction.op_a_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lb row 0) * ((v.sign_src row 0) - (256 * (v.seen_byte row 0)))) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lh row 0) * ((v.sign_src row 0) - (v.seen_0 row 0))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.instruction.is_lw row 0) * ((v.sign_src row 0) - (v.seen_1 row 0))) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `msb ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.msb row 0) * ((v.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((v.instruction.is_lbu row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.msb row 0)) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_0 row 0) - (((v.first_bytes.low_bytes_0 row 0) + (((v.offset_0 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_0 row 0)))) + ((((((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361) + (((v.offset_0 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_0 row 0) - (v.first_bytes.low_bytes_0 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_0 row 0) - (((((((((v.second_bytes.low_bytes_0 row 0) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_5 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_6 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.second_bytes.low_bytes_0 row 0)))) + (((v.offset_7 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.second_bytes.low_bytes_0 row 0)))) + ((((((((((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_6 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.second.prev_value_0 row 0) - (v.second_bytes.low_bytes_0 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_1 row 0) - (((((v.first_bytes.low_bytes_1 row 0) + (((v.offset_0 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.first_bytes.low_bytes_1 row 0)))) + (((v.offset_1 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.first_bytes.low_bytes_1 row 0)))) + (((v.offset_2 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_1 row 0)))) + ((((((((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361) + (((v.offset_0 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_2 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_1 row 0) - (v.first_bytes.low_bytes_1 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_1 row 0) - (((((((v.second_bytes.low_bytes_1 row 0) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.second_bytes.low_bytes_1 row 0)))) + (((v.offset_7 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.second_bytes.low_bytes_1 row 0)))) + ((((((((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361) + (((v.offset_4 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.second.prev_value_1 row 0) - (v.second_bytes.low_bytes_1 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_2 row 0) - (((((((v.first_bytes.low_bytes_2 row 0) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_1 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_2 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_3 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.first_bytes.low_bytes_2 row 0)))) + (((v.offset_4 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_2 row 0)))) + ((((((((((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_2 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_4 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_2 row 0) - (v.first_bytes.low_bytes_2 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_2 row 0) - (((((v.second_bytes.low_bytes_2 row 0) + (((v.offset_5 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_2 row 0)))) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.second_bytes.low_bytes_2 row 0)))) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.second_bytes.low_bytes_2 row 0)))) + ((((((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361) + (((v.offset_6 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.second.prev_value_2 row 0) - (v.second_bytes.low_bytes_2 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.first.access.value_3 row 0) - (((((((((v.first_bytes.low_bytes_3 row 0) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_3 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_4 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_5 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (v.first_bytes.low_bytes_3 row 0)))) + (((v.offset_6 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (v.first_bytes.low_bytes_3 row 0)))) + ((((((((((((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361) + (((v.offset_0 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_1 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_3 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_2 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_2 row 0) - (v.value_bytes.low_bytes_2 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_3 row 0) * (v.instruction.is_sd row 0)) * ((v.value_bytes.low_bytes_2 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_4 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_1 row 0) - (v.value_bytes.low_bytes_1 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_5 row 0) * ((v.instruction.is_sw row 0) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_1 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_6 row 0) * (((v.instruction.is_sh row 0) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((((v.instruction.op_a_value_0 row 0) - (v.value_bytes.low_bytes_0 row 0)) * 2122383361) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) + (((v.offset_7 row 0) * ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * ((v.value_bytes.low_bytes_0 row 0) - (((v.first.prev_value_3 row 0) - (v.first_bytes.low_bytes_3 row 0)) * 2122383361)))) * 256))) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.second.access.value_3 row 0) - (((v.second_bytes.low_bytes_3 row 0) + (((v.offset_7 row 0) * (v.instruction.is_sd row 0)) * ((((v.instruction.op_a_value_3 row 0) - (v.value_bytes.low_bytes_3 row 0)) * 2122383361) - (v.second_bytes.low_bytes_3 row 0)))) + ((((v.second.prev_value_3 row 0) - (v.second_bytes.low_bytes_3 row 0)) * 2122383361) * 256))) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `code_range.below ∈ {0, 1}`. -/
      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        ((v.code_range.below row 0) * ((v.code_range.below row 0) - 1)) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((v.code_range.borrow row 0) * ((v.code_range.borrow row 0) - 1)) * ((v.code_range.borrow row 0) - 2)) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * ((v.code_range.distance_0 row 0) - ((((v.code_range.below row 0) * (((0 + (v.code_range.code_start_0 row 0)) - (v.addr_word_0 row 0)) - ((((0 + (v.instruction.is_sb row 0)) + ((v.instruction.is_sh row 0) * 2)) + ((v.instruction.is_sw row 0) * 4)) + ((v.instruction.is_sd row 0) * 8)))) + ((1 - (v.code_range.below row 0)) * ((v.addr_word_0 row 0) - (v.code_range.code_end_0 row 0)))) + (65536 * (v.code_range.borrow row 0))))) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols
        (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * ((v.code_range.distance_1 row 0) - ((((v.code_range.below row 0) * ((0 + (v.code_range.code_start_1 row 0)) - (v.addr_word_1 row 0))) + ((1 - (v.code_range.below row 0)) * ((v.addr_word_1 row 0) - (v.code_range.code_end_1 row 0)))) - (v.code_range.borrow row 0)))) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_MemoryUnalignedChip F ExtF) (row : ℕ)
      : MemoryUnalignedChip.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]
    end row_constraints

  end constraint_simplification

end MemoryUnalignedChip.ConstraintsAndBuses
