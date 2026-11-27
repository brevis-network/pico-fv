import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.Extraction.MemoryReadWriteChip
import PicoFV.RV64IM.Airs.MemoryReadWriteChip
import PicoFV.RV64IM.Constraints.CodeRangeGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryReadWriteChip — constraints and bus messages

Citations read at Pico v3.2.0.

`MemoryReadWriteChip::eval` (`vm/src/chips/chips/riscv_memory/read_write/constraints.rs`) emits
45 constraints and 13 bus messages,
extracted in `PicoFV.RV64IM.Extraction.MemoryReadWriteChip`. This file restates them on the named
columns of `Valid_MemoryReadWriteChip` (`Airs/MemoryReadWriteChip.lean`), with an `_equiv` lemma
per constraint, and sorts the messages by contract (`AbsBuses`). Pico paths below are under
`vm/src/chips/chips/`, `vm/src/chips/` or `vm/src/`.

The chip takes the loads and stores whose address is aligned to their width. Per row:

- **Flags** (constraints 0 to 11): the eleven instruction flags are 0 or 1 and at most one is
  set. Their sum `is_memory` is the multiplicity of every message the row always sends; the
  weighted sum `Σ flag · opcode` is the opcode field of the memory dispatch.
- **Address** (12 to 22): `addr_word = b + c` through a carry chain whose third and fourth result
  pieces are 0; the second piece is not 0; three offset bits; alignment by width.
- **Memory access** (23): the read of the aligned double word at `prev_clk` and its write at
  `clk`, with `prev_clk = clk - (diff_16bit_limb + 2^16 diff_hi9) - 1`.
- **Load** (24 to 35): the selected piece and byte, the value of `a` with its sign fill when
  `op_a_0 = 0`, and the sign bit `msb`.
- **Store** (36 to 40): the double word after the access, from the one before and `a`.
- **Code range** (41 to 44): the `code_range` gadget's four constraints
  (`Constraints/CodeRangeGadget.lean`), with `addr_word`, `store_width` and
  `is_store = is_sb + is_sh + is_sw + is_sd` as its inputs (`riscv_memory/read_write/constraints.rs:94-108`).
-/

namespace MemoryReadWriteChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      /-- `is_lb ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lb row 0) * ((v.instruction.is_lb row 0) - 1)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lbu ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lbu row 0) * ((v.instruction.is_lbu row 0) - 1)) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lh ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lh row 0) * ((v.instruction.is_lh row 0) - 1)) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lhu ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lhu row 0) * ((v.instruction.is_lhu row 0) - 1)) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lw ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lw row 0) * ((v.instruction.is_lw row 0) - 1)) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_lwu ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lwu row 0) * ((v.instruction.is_lwu row 0) - 1)) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_ld ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_ld row 0) * ((v.instruction.is_ld row 0) - 1)) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sb ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_sb row 0) * ((v.instruction.is_sb row 0) - 1)) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sh ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_sh row 0) * ((v.instruction.is_sh row 0) - 1)) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sw ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_sw row 0) * ((v.instruction.is_sw row 0) - 1)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_sd ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:203`). -/
      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_sd row 0) * ((v.instruction.is_sd row 0) - 1)) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_memory ∈ {0, 1}`, the flags' sum: at most one flag is set (`riscv_memory/read_write/constraints.rs:208`). -/
      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The address's first carry `k1 = (b_0 + c_0 - addr_word_0) / 2^16` is 0 or 1 (`riscv_memory/read_write/constraints.rs:245-246`). `2130673921` is `2^16`'s inverse. -/
      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921) * (((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The second carry `k2 = (b_1 + c_1 + k1 - addr_word_1) / 2^16` is 0 or 1 (`riscv_memory/read_write/constraints.rs:247-249`). -/
      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921) * ((((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The third carry `k3 = (b_2 + c_2 + k2) / 2^16` is 0 or 1: the address's third piece is 0 (`riscv_memory/read_write/constraints.rs:250-251`). -/
      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921) * (((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The fourth carry `k4 = (b_3 + c_3 + k3) / 2^16` is 0 or 1: the address's fourth piece is 0 (`riscv_memory/read_write/constraints.rs:252-253`). -/
      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((0 + (v.instruction.op_b_value_3 row 0)) + (v.instruction.op_c_value_3 row 0)) + ((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) * (((((0 + (v.instruction.op_b_value_3 row 0)) + (v.instruction.op_c_value_3 row 0)) + ((((0 + (v.instruction.op_b_value_2 row 0)) + (v.instruction.op_c_value_2 row 0)) + (((((0 + (v.instruction.op_b_value_1 row 0)) + (v.instruction.op_c_value_1 row 0)) + ((((0 + (v.instruction.op_b_value_0 row 0)) + (v.instruction.op_c_value_0 row 0)) - (v.addr_word_0 row 0)) * 2130673921)) - (v.addr_word_1 row 0)) * 2130673921)) * 2130673921)) * 2130673921) - 1)) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `addr_limb1_inv · addr_word_1 = is_memory`: on a real row the address's second piece is not 0 (`riscv_memory/read_write/constraints.rs:271-274`). -/
      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((0 + ((v.addr_limb1_inv row 0) * (v.addr_word_1 row 0))) - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_bit_0 ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:283-285`). -/
      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.offset_bit_0 row 0) * ((v.offset_bit_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_bit_1 ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:283-285`). -/
      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.offset_bit_1 row 0) * ((v.offset_bit_1 row 0) - 1)) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `offset_bit_2 ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:283-285`). -/
      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.offset_bit_2 row 0) * ((v.offset_bit_2 row 0) - 1)) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- A half-word access has `offset_bit_0 = 0` (`riscv_memory/read_write/constraints.rs:313-315`). -/
      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((((v.instruction.is_lh row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_sh row 0)) * (v.offset_bit_0 row 0)) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- A word access has `offset_bit_0 + offset_bit_1 = 0` (`riscv_memory/read_write/constraints.rs:317-319`). -/
      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) + (v.instruction.is_sw row 0)) * ((0 + (v.offset_bit_0 row 0)) + (v.offset_bit_1 row 0))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- A double-word access has `offset_bit_0 + offset_bit_1 + offset_bit_2 = 0` (`riscv_memory/read_write/constraints.rs:321-325`). -/
      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((v.instruction.is_ld row 0) + (v.instruction.is_sd row 0)) * (((0 + (v.offset_bit_0 row 0)) + (v.offset_bit_1 row 0)) + (v.offset_bit_2 row 0))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `is_memory ∈ {0, 1}` again, the memory access's own check of its gate (`machine/builder/riscv_memory.rs:137`). -/
      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) * (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `selected_limb` is the piece of the previous double word that `offset_bit_1`, `offset_bit_2` select (`riscv_memory/read_write/constraints.rs:367-373`). -/
      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.selected_limb row 0) - ((((0 + (((1 - (0 + (v.offset_bit_1 row 0))) * (1 - (0 + (v.offset_bit_2 row 0)))) * (v.memory_access.prev_value_0 row 0))) + (((0 + (v.offset_bit_1 row 0)) * (1 - (0 + (v.offset_bit_2 row 0)))) * (v.memory_access.prev_value_1 row 0))) + (((1 - (0 + (v.offset_bit_1 row 0))) * (0 + (v.offset_bit_2 row 0))) * (v.memory_access.prev_value_2 row 0))) + (((0 + (v.offset_bit_1 row 0)) * (0 + (v.offset_bit_2 row 0))) * (v.memory_access.prev_value_3 row 0)))) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- A byte load's `selected_byte` is the low byte of `selected_limb` (`offset_bit_0 = 0`) or its high byte (`riscv_memory/read_write/constraints.rs:386-390`). `2122383361` is `256`'s inverse. -/
      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) * ((v.selected_byte row 0) - ((0 + ((v.offset_bit_0 row 0) * (((0 + (v.selected_limb row 0)) - (v.mem_limb_low_byte row 0)) * 2122383361))) + ((1 - (v.offset_bit_0 row 0)) * (0 + (v.mem_limb_low_byte row 0)))))) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, piece 0 of `a` is the loaded value's, sign fill included; on a store row it is `a`'s own (`riscv_memory/read_write/constraints.rs:417-442`). -/
      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_0 row 0) - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) * (v.selected_byte row 0)) + (((v.instruction.is_lh row 0) + (v.instruction.is_lhu row 0)) * (v.selected_limb row 0))) + (((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) * (v.selected_limb row 0))) + ((v.instruction.is_ld row 0) * (v.memory_access.prev_value_0 row 0))) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_0 row 0))) + (((v.instruction.is_lb row 0) * (v.msb row 0)) * 65280)))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, piece 1 of `a` is the loaded value's, sign fill included; on a store row it is `a`'s own (`riscv_memory/read_write/constraints.rs:417-442`). -/
      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_1 row 0) - ((((((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) * (v.lhw_val row 0)) + ((v.instruction.is_ld row 0) * (v.memory_access.prev_value_1 row 0))) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_1 row 0))) + ((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) * (v.msb row 0)) * 65535)))) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, piece 2 of `a` is the loaded value's, sign fill included; on a store row it is `a`'s own (`riscv_memory/read_write/constraints.rs:417-442`). -/
      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_2 row 0) - ((((v.instruction.is_ld row 0) * (v.memory_access.prev_value_2 row 0)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_2 row 0))) + (((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)) * (v.msb row 0)) * 65535)))) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- When `op_a_0 = 0`, piece 3 of `a` is the loaded value's, sign fill included; on a store row it is `a`'s own (`riscv_memory/read_write/constraints.rs:417-442`). -/
      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((1 - (v.instruction.op_a_0 row 0)) * ((v.instruction.op_a_value_3 row 0) - ((((v.instruction.is_ld row 0) * (v.memory_access.prev_value_3 row 0)) + (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * (v.instruction.op_a_value_3 row 0))) + (((((v.instruction.is_lb row 0) + (v.instruction.is_lh row 0)) + (v.instruction.is_lw row 0)) * (v.msb row 0)) * 65535)))) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- An `LB` row's `lhw_val` is `256 · selected_byte` (`riscv_memory/read_write/constraints.rs:451-453`). -/
      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lb row 0) * ((v.lhw_val row 0) - (256 * (v.selected_byte row 0)))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `msb ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:457`). -/
      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.msb row 0) * ((v.msb row 0) - 1)) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `msb = 0` on an unsigned load and on `LD` (`riscv_memory/read_write/constraints.rs:458-465`). -/
      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((v.instruction.is_lbu row 0) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) * (v.msb row 0)) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- A half-word load's `lhw_val` is `selected_limb` (`riscv_memory/read_write/constraints.rs:471-473`). -/
      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.is_lh row 0) * ((v.lhw_val row 0) - (v.selected_limb row 0))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- A word load's `lhw_val` is the high half of the selected word (`riscv_memory/read_write/constraints.rs:480-484`). -/
      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((v.instruction.is_lw row 0) + (v.instruction.is_lwu row 0)) * ((v.lhw_val row 0) - (((1 - (v.offset_bit_2 row 0)) * (v.memory_access.prev_value_1 row 0)) + ((0 + (v.offset_bit_2 row 0)) * (v.memory_access.prev_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `op_a_0 ∈ {0, 1}` (`riscv_memory/read_write/constraints.rs:497`). -/
      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.instruction.op_a_0 row 0) * ((v.instruction.op_a_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- `shift`: what a half-word or byte store adds to the selected piece, 0 on any other row (`riscv_memory/read_write/constraints.rs:553-563`). -/
      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.shift row 0) - (((v.instruction.is_sh row 0) * ((v.instruction.op_a_value_0 row 0) - (v.selected_limb row 0))) + ((v.instruction.is_sb row 0) * (((1 - (v.offset_bit_0 row 0)) * ((0 + (v.register_low_byte row 0)) - (v.mem_limb_low_byte row 0))) + ((0 + (v.offset_bit_0 row 0)) * ((((0 + (v.register_low_byte row 0)) * 256) - (v.selected_limb row 0)) + (v.mem_limb_low_byte row 0))))))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Piece 0 of the double word after the access: the previous piece, changed only by a store (`riscv_memory/read_write/constraints.rs:578-595`). -/
      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.memory_access.access.value_0 row 0) - ((((v.memory_access.prev_value_0 row 0) + (((1 - (0 + (v.offset_bit_1 row 0))) * (1 - (0 + (v.offset_bit_2 row 0)))) * (v.shift row 0))) + ((v.instruction.is_sd row 0) * ((v.instruction.op_a_value_0 row 0) - (v.memory_access.prev_value_0 row 0)))) + (((v.instruction.is_sw row 0) * (1 - (v.offset_bit_2 row 0))) * ((v.instruction.op_a_value_0 row 0) - (v.memory_access.prev_value_0 row 0))))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Piece 1 of the double word after the access: the previous piece, changed only by a store (`riscv_memory/read_write/constraints.rs:578-595`). -/
      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.memory_access.access.value_1 row 0) - ((((v.memory_access.prev_value_1 row 0) + (((0 + (v.offset_bit_1 row 0)) * (1 - (0 + (v.offset_bit_2 row 0)))) * (v.shift row 0))) + ((v.instruction.is_sd row 0) * ((v.instruction.op_a_value_1 row 0) - (v.memory_access.prev_value_1 row 0)))) + (((v.instruction.is_sw row 0) * (1 - (v.offset_bit_2 row 0))) * ((v.instruction.op_a_value_1 row 0) - (v.memory_access.prev_value_1 row 0))))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Piece 2 of the double word after the access: the previous piece, changed only by a store (`riscv_memory/read_write/constraints.rs:578-595`). -/
      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.memory_access.access.value_2 row 0) - ((((v.memory_access.prev_value_2 row 0) + (((1 - (0 + (v.offset_bit_1 row 0))) * (0 + (v.offset_bit_2 row 0))) * (v.shift row 0))) + ((v.instruction.is_sd row 0) * ((v.instruction.op_a_value_2 row 0) - (v.memory_access.prev_value_2 row 0)))) + (((v.instruction.is_sw row 0) * (v.offset_bit_2 row 0)) * ((v.instruction.op_a_value_0 row 0) - (v.memory_access.prev_value_2 row 0))))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- Piece 3 of the double word after the access: the previous piece, changed only by a store (`riscv_memory/read_write/constraints.rs:578-595`). -/
      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.memory_access.access.value_3 row 0) - ((((v.memory_access.prev_value_3 row 0) + (((0 + (v.offset_bit_1 row 0)) * (0 + (v.offset_bit_2 row 0))) * (v.shift row 0))) + ((v.instruction.is_sd row 0) * ((v.instruction.op_a_value_3 row 0) - (v.memory_access.prev_value_3 row 0)))) + (((v.instruction.is_sw row 0) * (v.offset_bit_2 row 0)) * ((v.instruction.op_a_value_1 row 0) - (v.memory_access.prev_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The `code_range` gadget: `below ∈ {0, 1}` (`gadgets/code_range.rs:135`). -/
      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        ((v.code_range.below row 0) * ((v.code_range.below row 0) - 1)) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The `code_range` gadget: `borrow ∈ {0, 1, 2}` (`gadgets/code_range.rs:137-139`). -/
      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((v.code_range.borrow row 0) * ((v.code_range.borrow row 0) - 1)) * ((v.code_range.borrow row 0) - 2)) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The `code_range` gadget, on a store row: the distance's low piece (`gadgets/code_range.rs:154-156`). -/
      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * ((v.code_range.distance_0 row 0) - ((((v.code_range.below row 0) * (((0 + (v.code_range.code_start_0 row 0)) - (v.addr_word_0 row 0)) - ((((0 + (v.instruction.is_sb row 0)) + ((v.instruction.is_sh row 0) * 2)) + ((v.instruction.is_sw row 0) * 4)) + ((v.instruction.is_sd row 0) * 8)))) + ((1 - (v.code_range.below row 0)) * ((v.addr_word_0 row 0) - (v.code_range.code_end_0 row 0)))) + (65536 * (v.code_range.borrow row 0))))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      /-- The `code_range` gadget, on a store row: the distance's high piece (`gadgets/code_range.rs:157-159`). -/
      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        let v := air.cols.values
        (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)) * ((v.code_range.distance_1 row 0) - ((((v.code_range.below row 0) * ((0 + (v.code_range.code_start_1 row 0)) - (v.addr_word_1 row 0))) + ((1 - (v.code_range.below row 0)) * ((v.addr_word_1 row 0) - (v.code_range.code_end_1 row 0)))) - (v.code_range.borrow row 0)))) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[simp]
      def row_constraint_list (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : List Prop :=
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
          constraint_42 air row, constraint_43 air row, constraint_44 air row
        ]

    end row_constraints

    section row_buses

      /-- The row's 13 messages, `(multiplicity, [tag, ...fields])`, as extracted. Tags are
          Pico's `LookupType`: 1 Memory, 2 Program, 5 Byte. -/
      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) :
          List (FKB × List FKB) :=
        let v := air.cols.values
        -- 0: the memory dispatch, received from the CPU chip (`riscv_memory/read_write/constraints.rs:63-84`)
        [ ((0 - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))), [1, (((((((((((0 + ((0 + (v.instruction.is_lb row 0)) * 10)) + ((0 + (v.instruction.is_lbu row 0)) * 13)) + ((0 + (v.instruction.is_lh row 0)) * 11)) + ((0 + (v.instruction.is_lhu row 0)) * 14)) + ((0 + (v.instruction.is_lw row 0)) * 12)) + ((0 + (v.instruction.is_lwu row 0)) * 45)) + ((0 + (v.instruction.is_ld row 0)) * 46)) + ((0 + (v.instruction.is_sb row 0)) * 15)) + ((0 + (v.instruction.is_sh row 0)) * 16)) + ((0 + (v.instruction.is_sw row 0)) * 17)) + ((0 + (v.instruction.is_sd row 0)) * 47)), (v.instruction.op_a_value_0 row 0), (v.instruction.op_a_value_1 row 0), (v.instruction.op_a_value_2 row 0), (v.instruction.op_a_value_3 row 0), (v.instruction.op_b_value_0 row 0), (v.instruction.op_b_value_1 row 0), (v.instruction.op_b_value_2 row 0), (v.instruction.op_b_value_3 row 0), (v.instruction.op_c_value_0 row 0), (v.instruction.op_c_value_1 row 0), (v.instruction.op_c_value_2 row 0), (v.instruction.op_c_value_3 row 0), (v.instruction.op_a_0 row 0), ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), (v.chunk row 0), (v.clk row 0)]),
        -- 1: `U16Range` of `addr_word_1` (`riscv_memory/read_write/constraints.rs:259-266`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 8, (v.addr_word_1 row 0), 0, 0, 0]),
        -- 2: `BitRange(13)` of the aligned low piece over 8 (`riscv_memory/read_write/constraints.rs:292-309`); `1864368129` is `8`'s inverse
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 9, (((0 + (v.addr_word_0 row 0)) - (((0 + (v.offset_bit_0 row 0)) + (2 * (v.offset_bit_1 row 0))) + (4 * (v.offset_bit_2 row 0)))) * 1864368129), 0, 13, 0]),
        -- 3: `U16Range` of `diff_16bit_limb` (`machine/builder/range_check.rs:88-95`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 8, (v.memory_access.access.diff_16bit_limb row 0), 0, 0, 0]),
        -- 4: `BitRange(9)` of `diff_hi9` (`machine/builder/range_check.rs:96-102`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [5, 9, (v.memory_access.access.diff_hi9 row 0), 0, 9, 0]),
        -- 5: the read of the aligned double word at `prev_clk` (`machine/builder/riscv_memory.rs:195-200`)
          (((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0))), [1, (v.chunk row 0), ((((v.clk row 0) + 0) - ((v.memory_access.access.diff_16bit_limb row 0) + ((v.memory_access.access.diff_hi9 row 0) * 65536))) - 1), ((0 + (v.addr_word_0 row 0)) - (((0 + (v.offset_bit_0 row 0)) + (2 * (v.offset_bit_1 row 0))) + (4 * (v.offset_bit_2 row 0)))), (0 + (v.addr_word_1 row 0)), 0, (v.memory_access.prev_value_0 row 0), (v.memory_access.prev_value_1 row 0), (v.memory_access.prev_value_2 row 0), (v.memory_access.prev_value_3 row 0)]),
        -- 6: the write of the aligned double word at `clk` (`machine/builder/riscv_memory.rs:203-208`)
          ((0 - ((((((((v.instruction.is_lb row 0) + (v.instruction.is_lbu row 0)) + (v.instruction.is_lh row 0)) + (v.instruction.is_lhu row 0)) + (v.instruction.is_lw row 0)) + (v.instruction.is_lwu row 0)) + (v.instruction.is_ld row 0)) + ((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)))), [1, (v.chunk row 0), ((v.clk row 0) + 0), ((0 + (v.addr_word_0 row 0)) - (((0 + (v.offset_bit_0 row 0)) + (2 * (v.offset_bit_1 row 0))) + (4 * (v.offset_bit_2 row 0)))), (0 + (v.addr_word_1 row 0)), 0, (v.memory_access.access.value_0 row 0), (v.memory_access.access.value_1 row 0), (v.memory_access.access.value_2 row 0), (v.memory_access.access.value_3 row 0)]),
        -- 7: `U16Range` of `2 · lhw_val - msb · 2^16`, the sign-bit check (`riscv_memory/read_write/constraints.rs:486-494`)
          ((((v.instruction.is_lh row 0) + (v.instruction.is_lw row 0)) + (v.instruction.is_lb row 0)), [5, 8, (((2 * (v.lhw_val row 0)) - 0) - ((v.msb row 0) * 65536)), 0, 0, 0]),
        -- 8: `U8Range` of the byte split of `op_a_value_0` (`riscv_memory/read_write/constraints.rs:521-528`)
          ((v.instruction.is_sb row 0), [5, 7, 0, 0, (v.register_low_byte row 0), (((0 + (v.instruction.op_a_value_0 row 0)) - (v.register_low_byte row 0)) * 2122383361)]),
        -- 9: `U8Range` of the byte split of `selected_limb` (`riscv_memory/read_write/constraints.rs:532-542`)
          ((((v.instruction.is_sb row 0) + (v.instruction.is_lb row 0)) + (v.instruction.is_lbu row 0)), [5, 7, 0, 0, (v.mem_limb_low_byte row 0), (((0 + (v.selected_limb row 0)) - (v.mem_limb_low_byte row 0)) * 2122383361)]),
        -- 10: the `code_range` gadget's lookup of the code range (`gadgets/code_range.rs:126-134`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [2, (v.code_range.code_start_0 row 0), (v.code_range.code_start_1 row 0), (v.code_range.code_end_0 row 0), (v.code_range.code_end_1 row 0)]),
        -- 11: the gadget's `U16Range` of `distance_0` (`gadgets/code_range.rs:160-169`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 8, (v.code_range.distance_0 row 0), 0, 0, 0]),
        -- 12: the gadget's `U16Range` of `distance_1` (`gadgets/code_range.rs:160-169`)
          (((((v.instruction.is_sb row 0) + (v.instruction.is_sh row 0)) + (v.instruction.is_sw row 0)) + (v.instruction.is_sd row 0)), [5, 8, (v.code_range.distance_1 row 0), 0, 0, 0]) ]

      @[constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_MemoryReadWriteChip FKB ExtF) : Prop :=
        air.bus =
          List.flatMap
            (fun row ↦ raw_bus_row air row)
            (List.range (air.last_row + 1))

    end row_buses

    @[constraint_and_interaction_simplification]
    def allHold_simplified
      (air : Valid_MemoryReadWriteChip FKB ExtF)
      (row : ℕ)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_MemoryReadWriteChip FKB ExtF)
      (row : ℕ)
    :
      MemoryReadWriteChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition,
        constraint_and_interaction_simplification]

  end constraint_simplification

end MemoryReadWriteChip.ConstraintsAndBuses

namespace MemoryReadWriteChip

  open RV64IM_Interactions

  /-- The row's messages, sorted by contract. With `is_memory` the flags' sum and `is_store` the
      store flags' sum:

      - `Memory`: the memory dispatch `[opcode, a, b, c, op_a_0, is_memory, chunk, clk]`,
        received at `-is_memory`, its opcode `Σ flag · opcode`;
      - `State`: the read of the aligned double word `[chunk, prev_clk, addr, prev_value]` at
        `+is_memory` and its write `[chunk, clk, addr, value]` at `-is_memory`, where `addr` is
        `[addr_word_0 - offset, addr_word_1, 0]`;
      - `Byte`: four range checks at `+is_memory` (the address's second piece, the aligned low
        piece over 8, the two pieces of `clk - prev_clk - 1`), the sign-bit check, the two byte
        splits, and the gadget's two distance checks;
      - `CodeRange`: the gadget's lookup of the code range, at `+is_store`. -/
  def AbsBuses (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) : BusRow :=
    let v := air.cols.values
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
    let aligned_addr_0 := v.addr_word_0 row 0 -
      (v.offset_bit_0 row 0 + 2 * v.offset_bit_1 row 0 + 4 * v.offset_bit_2 row 0)
    let diff_16 := v.memory_access.access.diff_16bit_limb row 0
    let diff_hi9 := v.memory_access.access.diff_hi9 row 0
    let prev_clk := v.clk row 0 - (diff_16 + diff_hi9 * 65536) - 1
    {
      Program := [],
      ALU := [],
      Byte := List.map RV64IM_Interactions.ByteBusEntry.deserialise [
        (is_memory, #v[8, v.addr_word_1 row 0, 0, 0, 0]),
        (is_memory, #v[9, aligned_addr_0 * 1864368129, 0, 13, 0]),
        (is_memory, #v[8, diff_16, 0, 0, 0]),
        (is_memory, #v[9, diff_hi9, 0, 9, 0]),
        (is_lh + is_lw + is_lb, #v[8, 2 * v.lhw_val row 0 - v.msb row 0 * 65536, 0, 0, 0]),
        (is_sb, #v[7, 0, 0, v.register_low_byte row 0,
          (v.instruction.op_a_value_0 row 0 - v.register_low_byte row 0) * 2122383361]),
        (is_sb + is_lb + is_lbu, #v[7, 0, 0, v.mem_limb_low_byte row 0,
          (v.selected_limb row 0 - v.mem_limb_low_byte row 0) * 2122383361]),
        (is_store, #v[8, v.code_range.distance_0 row 0, 0, 0, 0]),
        (is_store, #v[8, v.code_range.distance_1 row 0, 0, 0, 0])
      ],
      State := List.map RV64IM_Interactions.StateBusEntry.deserialise [
        (is_memory, #v[v.chunk row 0, prev_clk, aligned_addr_0, v.addr_word_1 row 0, 0,
          v.memory_access.prev_value_0 row 0, v.memory_access.prev_value_1 row 0,
          v.memory_access.prev_value_2 row 0, v.memory_access.prev_value_3 row 0]),
        (-(is_memory), #v[v.chunk row 0, v.clk row 0, aligned_addr_0, v.addr_word_1 row 0, 0,
          v.memory_access.access.value_0 row 0, v.memory_access.access.value_1 row 0,
          v.memory_access.access.value_2 row 0, v.memory_access.access.value_3 row 0])
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

end MemoryReadWriteChip

namespace MemoryReadWriteChip.Interactions

  /-- The chip's messages on one row, sorted by contract. -/
  def bus_row (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) :
      RV64IM_Interactions.BusRow :=
    MemoryReadWriteChip.AbsBuses air row

  /-- Sorting the row's extracted messages gives `bus_row`. -/
  @[simp]
  lemma bus_row_equiv (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (MemoryReadWriteChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      RV64IM_Interactions.deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      MemoryReadWriteChip.AbsBuses,
      pico_encapsulation,
    ]

end MemoryReadWriteChip.Interactions

namespace MemoryReadWriteChip.Interpretations

  open RV64IM_Interactions
  open MemoryReadWriteChip.ConstraintsAndBuses
  open MemoryReadWriteChip.Interactions

  /-- The row's columns satisfy the `code_range` gadget's constraints, with the inputs the chip
      hands it: `is_store`, `addr_word` and `store_width` (`riscv_memory/read_write/constraints.rs:94-108`). -/
  lemma allHold_code_range
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    let v := air.cols.values
    CodeRangeGadget.AbsConstraints
      (v.instruction.is_sb row 0 + v.instruction.is_sh row 0 + v.instruction.is_sw row 0 +
        v.instruction.is_sd row 0)
      (v.addr_word_0 row 0) (v.addr_word_1 row 0) (v.store_width row 0)
      (v.code_range.code_start_0 row 0) (v.code_range.code_start_1 row 0)
      (v.code_range.code_end_0 row 0) (v.code_range.code_end_1 row 0)
      (v.code_range.below row 0) (v.code_range.borrow row 0)
      (v.code_range.distance_0 row 0) (v.code_range.distance_1 row 0)
  := by
    simp only [allHold_iff_allHold_simplified, allHold_simplified, row_constraint_list,
      List.Forall] at h_constraints
    obtain ⟨ -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h41, h42, h43, h44 ⟩ := h_constraints
    simp only [constraint_41, constraint_42, constraint_43, constraint_44] at h41 h42 h43 h44
    refine ⟨ h41, h42, ?_, ?_ ⟩
    · unfold Valid_MemoryChipValueCols.store_width; linear_combination h43
    · linear_combination h44

  /-- What the tables promise the row's messages covers what they promise the `code_range`
      gadget's three: the gadget's messages are among the row's. -/
  lemma bus_row_all_wf_asm_code_range
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_wf_asm : bus_row_all_wf_asm (bus_row air row))
  :
    let v := air.cols.values
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

end MemoryReadWriteChip.Interpretations

