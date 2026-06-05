import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.Extraction.MemoryReadWriteChip
import PicoFV.RV64IM.Airs.MemoryReadWriteChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryReadWriteChip — human-readable constraints and bus interactions

The `ConstraintsAndBuses` namespace below restates each of the 85
algebraic constraints and the 16 bus interactions emitted by
`MemoryReadWriteChip::eval`
(`vm/src/chips/chips/riscv_memory/read_write/constraints.rs` at commit
`0ecd943c3dba682e1848d1f2d52ac50a24949d8a`, Pico PR #101 head) in terms of
the `Valid_MemoryReadWriteChip` air's named accessors, plus a `_equiv` lemma
per constraint proving equality with the raw form in
`PicoFV.RV64IM.Extraction.MemoryReadWriteChip`.

The chip layout (matching `MemoryChipValueCols<F>`, 80 columns) is:

| Cols    | Field path (under `air.cols.values`)                | Notes |
|---------|-----------------------------------------------------|-------|
| 0       | `chunk`                                             | execution chunk |
| 1       | `clk`                                               | clock |
| 2..5    | `addr_word_0..3`                                    | full 64-bit address |
| 6..8    | `offset_bit_0..2`                                   | low 3 bits of `addr_word_0` |
| 9..12   | `limb_select_0..3`                                  | one-hot limb selector |
| 13      | `addr_top_two_limb_inv`                             | stack-guard witness |
| 14..17  | `memory_access.prev_value_0..3`                     | RW: previous memory value |
| 18..21  | `memory_access.access.value_0..3`                   | RW: current memory value |
| 22..26  | `memory_access.access.{prev_chunk,prev_clk,compare_clk,diff_16bit_limb,diff_8bit_limb}` | access metadata |
| 27      | `selected_limb`                                     | mem limb at `limb_select` |
| 28      | `selected_limb_low_byte`                            | low byte of `selected_limb` |
| 29      | `selected_byte`                                     | byte at `offset_bit_0` |
| 30..31  | `selected_word_0..1`                                | word-load output (LW/LWU) |
| 32      | `msb`                                               | sign-extension flag |
| 33      | `register_low_byte`                                 | low byte of `op_a_0` (SB) |
| 34      | `mem_limb_low_byte`                                 | low byte of target mem limb |
| 35      | `increment`                                         | SB/SH/SW: delta to memory |
| 36..39  | `store_value_0..3`                                  | store: new memory value |
| 40..43  | `unsigned_mem_val_0..3`                             | zero-extended load result |
| 44      | `mem_value_is_pos_not_x0`                           | gate for non-extending load |
| 45      | `mem_value_is_neg_not_x0`                           | gate for sign-extending load |
| 46      | `instruction.opcode`                                |  |
| 47      | `instruction.op_a_0`                                | x0 flag (rd == x0) |
| 48..58  | `instruction.is_lb..is_sd`                          | 11 op selectors |
| 59..62  | `instruction.op_a_access.prev_value_0..3`           | RW: previous register `rd` |
| 63..66  | `instruction.op_a_access.access.value_0..3`         | RW: new register `rd` |
| 67..71  | `instruction.op_a_access.access.{prev_chunk,…}`     | access metadata |
| 72..75  | `instruction.op_b_access_0..3`                      | register `rs1` (now plain `Word`) |
| 76..79  | `instruction.op_c_access_0..3`                      | immediate (treated as register-shaped, plain `Word`) |

Post-PR-#101 deltas vs the prior `b6f2de04` baseline:
* `addr_aligned_0..3` removed (commit `db682d9c`): aligned address now
  computed inline as `addr_word_0 - offset_sum` in the State-bus tuples.
* `op_b_access`/`op_c_access` flattened to plain `Word` (commit `0ecd943c`):
  10 unused metadata cols removed across the two operands.
* 4 new constraints `op_a_0 · op_a_val_i = 0` (commit `7860af12`).
* LB/LBU byte-bus tuple's `x_3` slot is now the high-byte witness instead
  of `0` (commit `fc197c0b`).

Semantic grouping (from the Rust eval, C1..C8):

- **C1** (constraints 0..1, plus bus entries): address calculation —
  ALU ADD `addr_word = op_b + op_c`, top limb = 0, u16 range checks,
  stack-guard `(addr_word_1 + addr_word_2) ≠ 0 ∨ addr_top_two_limb_inv = 0`.
- **C2** (constraints 2..11): offset decomposition + alignment —
  `offset_bit_i ∈ {0, 1}`, `limb_select` one-hot derivation,
  alignment gates for LH/LHU/SH, LW/LWU/SW, LD/SD.
- **C3** (bus entries): timestamp + 9-element Regional lookup.
- **C4** (constraints 16..19): load-doesn't-write — `value_i = prev_value_i`
  on the load selectors.
- **C5** (constraints 20..29): limb selection + word-load selection.
- **C6** (constraints 30..47): byte/half/word load + sign-extension fill +
  `msb` independent verification via byte / U16MSB lookup.
- **C7** (constraints 48..63, 81..84): store sub-word writing via
  `increment * limb_select_i` pattern; `store_value = memory_access.value`.
- **C8** (constraints 12..15, 64..80): x0 handling +
  `mem_value_is_pos_not_x0` / `mem_value_is_neg_not_x0` derivation +
  per-selector sign extension into `op_a_access.value`.

The bus interactions are 16 entries:
- 1 looked Instruction bus entry (`+is_mem`, opcode 0): supplies the
  decoded instruction back to `CpuChip`.
- 1 looking ALU ADD (`-is_mem`): addr = op_b + op_c.
- 3 looking ByteBus u16-range (`-is_mem`): `addr_word_2/3` (well, 1/2/3).
- 1 looking ByteBus BitRange-13 (`-is_mem`): `(addr_word_0 - offset_word) / 8`.
- 1 looking ByteBus u16-range (`-is_mem`): `addr_top_two_limb_inv` (stack-guard helper).
- 1 looking ByteBus u8-range (`-is_mem`): `addr_top_two_limb_inv * 65535` / similar helper.
- 1 looked Regional bus (`+is_mem`, opcode 0): timestamp monotonicity.
- 1 looking Regional bus (`-(is_lb + is_lbu)`): timestamp helper.
- 1 looking ByteBus MSB (`-is_lb`): `selected_byte` msb.
- 1 looking ByteBus u16-range (`-is_lh`): `2·selected_limb - msb·2^16`.
- 1 looking ByteBus u16-range (`-is_lw`): `2·selected_word_1 - msb·2^16`.
- 2 looking ByteBus u8-range (`-is_sb`): byte split of `op_a_0`.
-/

namespace MemoryReadWriteChip.ConstraintsAndBuses

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * (air.cols.values.addr_word_3 row 0)) = 0

      @[simp]
      lemma constraint_0_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_0 air row ↔ constraint_0 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((0 + ((air.cols.values.addr_top_two_limb_inv row 0) * ((air.cols.values.addr_word_1 row 0) + (air.cols.values.addr_word_2 row 0)))) - ((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))) = 0

      @[simp]
      lemma constraint_1_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_1 air row ↔ constraint_1 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.offset_bit_0 row 0) * ((air.cols.values.offset_bit_0 row 0) - 1))) = 0

      @[simp]
      lemma constraint_2_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_2 air row ↔ constraint_2 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.offset_bit_1 row 0) * ((air.cols.values.offset_bit_1 row 0) - 1))) = 0

      @[simp]
      lemma constraint_3_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_3 air row ↔ constraint_3 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.offset_bit_2 row 0) * ((air.cols.values.offset_bit_2 row 0) - 1))) = 0

      @[simp]
      lemma constraint_4_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_4 air row ↔ constraint_4 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.limb_select_0 row 0) - ((1 - (0 + (air.cols.values.offset_bit_1 row 0))) * (1 - (0 + (air.cols.values.offset_bit_2 row 0)))))) = 0

      @[simp]
      lemma constraint_5_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_5 air row ↔ constraint_5 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.limb_select_1 row 0) - ((0 + (air.cols.values.offset_bit_1 row 0)) * (1 - (0 + (air.cols.values.offset_bit_2 row 0)))))) = 0

      @[simp]
      lemma constraint_6_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_6 air row ↔ constraint_6 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.limb_select_2 row 0) - ((1 - (0 + (air.cols.values.offset_bit_1 row 0))) * (0 + (air.cols.values.offset_bit_2 row 0))))) = 0

      @[simp]
      lemma constraint_7_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_7 air row ↔ constraint_7 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.limb_select_3 row 0) - ((0 + (air.cols.values.offset_bit_1 row 0)) * (0 + (air.cols.values.offset_bit_2 row 0))))) = 0

      @[simp]
      lemma constraint_8_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_8 air row ↔ constraint_8 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.instruction.is_lh row 0) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_sh row 0)) * (air.cols.values.offset_bit_0 row 0)) = 0

      @[simp]
      lemma constraint_9_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_9 air row ↔ constraint_9 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_sw row 0)) * ((0 + (air.cols.values.offset_bit_0 row 0)) + (air.cols.values.offset_bit_1 row 0))) = 0

      @[simp]
      lemma constraint_10_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_10 air row ↔ constraint_10 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_ld row 0) + (air.cols.values.instruction.is_sd row 0)) * (((0 + (air.cols.values.offset_bit_0 row 0)) + (air.cols.values.offset_bit_1 row 0)) + (air.cols.values.offset_bit_2 row 0))) = 0

      @[simp]
      lemma constraint_11_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_11 air row ↔ constraint_11 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) - 1)) = 0

      @[simp]
      lemma constraint_12_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_12 air row ↔ constraint_12 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.memory_access.access.compare_clk row 0) * ((air.cols.values.memory_access.access.compare_clk row 0) - 1))) = 0

      @[simp]
      lemma constraint_13_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_13 air row ↔ constraint_13 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.memory_access.access.compare_clk row 0) * ((air.cols.values.chunk row 0) - (air.cols.values.memory_access.access.prev_chunk row 0)))) = 0

      @[simp]
      lemma constraint_14_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_14 air row ↔ constraint_14 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((((((air.cols.values.memory_access.access.compare_clk row 0) * ((air.cols.values.clk row 0) + 0)) + ((1 - (air.cols.values.memory_access.access.compare_clk row 0)) * (air.cols.values.chunk row 0))) - (((air.cols.values.memory_access.access.compare_clk row 0) * (air.cols.values.memory_access.access.prev_clk row 0)) + ((1 - (air.cols.values.memory_access.access.compare_clk row 0)) * (air.cols.values.memory_access.access.prev_chunk row 0)))) - 1) - ((air.cols.values.memory_access.access.diff_16bit_limb row 0) + ((air.cols.values.memory_access.access.diff_8bit_limb row 0) * 65536)))) = 0

      @[simp]
      lemma constraint_15_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_15 air row ↔ constraint_15 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) * ((air.cols.values.memory_access.access.value_0 row 0) - (air.cols.values.memory_access.prev_value_0 row 0))) = 0

      @[simp]
      lemma constraint_16_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_16 air row ↔ constraint_16 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) * ((air.cols.values.memory_access.access.value_1 row 0) - (air.cols.values.memory_access.prev_value_1 row 0))) = 0

      @[simp]
      lemma constraint_17_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_17 air row ↔ constraint_17 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) * ((air.cols.values.memory_access.access.value_2 row 0) - (air.cols.values.memory_access.prev_value_2 row 0))) = 0

      @[simp]
      lemma constraint_18_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_18 air row ↔ constraint_18 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) * ((air.cols.values.memory_access.access.value_3 row 0) - (air.cols.values.memory_access.prev_value_3 row 0))) = 0

      @[simp]
      lemma constraint_19_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_19 air row ↔ constraint_19 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))) * ((air.cols.values.selected_limb row 0) - ((((0 + ((air.cols.values.limb_select_0 row 0) * (air.cols.values.memory_access.prev_value_0 row 0))) + ((air.cols.values.limb_select_1 row 0) * (air.cols.values.memory_access.prev_value_1 row 0))) + ((air.cols.values.limb_select_2 row 0) * (air.cols.values.memory_access.prev_value_2 row 0))) + ((air.cols.values.limb_select_3 row 0) * (air.cols.values.memory_access.prev_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_20_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_20 air row ↔ constraint_20 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) * ((air.cols.values.selected_byte row 0) - ((0 + ((air.cols.values.offset_bit_0 row 0) * (((0 + (air.cols.values.selected_limb row 0)) - (air.cols.values.selected_limb_low_byte row 0)) * 2122383361))) + ((1 - (air.cols.values.offset_bit_0 row 0)) * (0 + (air.cols.values.selected_limb_low_byte row 0)))))) = 0

      @[simp]
      lemma constraint_21_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_21 air row ↔ constraint_21 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) * ((air.cols.values.unsigned_mem_val_0 row 0) - (0 + (air.cols.values.selected_byte row 0)))) = 0

      @[simp]
      lemma constraint_22_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_22 air row ↔ constraint_22 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) * ((air.cols.values.unsigned_mem_val_1 row 0) - 0)) = 0

      @[simp]
      lemma constraint_23_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_23 air row ↔ constraint_23 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) * ((air.cols.values.unsigned_mem_val_2 row 0) - 0)) = 0

      @[simp]
      lemma constraint_24_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_24 air row ↔ constraint_24 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) * ((air.cols.values.unsigned_mem_val_3 row 0) - 0)) = 0

      @[simp]
      lemma constraint_25_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_25 air row ↔ constraint_25 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lh row 0) + (air.cols.values.instruction.is_lhu row 0)) * ((air.cols.values.unsigned_mem_val_0 row 0) - (0 + (air.cols.values.selected_limb row 0)))) = 0

      @[simp]
      lemma constraint_26_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_26 air row ↔ constraint_26 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lh row 0) + (air.cols.values.instruction.is_lhu row 0)) * ((air.cols.values.unsigned_mem_val_1 row 0) - 0)) = 0

      @[simp]
      lemma constraint_27_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_27 air row ↔ constraint_27 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lh row 0) + (air.cols.values.instruction.is_lhu row 0)) * ((air.cols.values.unsigned_mem_val_2 row 0) - 0)) = 0

      @[simp]
      lemma constraint_28_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_28 air row ↔ constraint_28 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lh row 0) + (air.cols.values.instruction.is_lhu row 0)) * ((air.cols.values.unsigned_mem_val_3 row 0) - 0)) = 0

      @[simp]
      lemma constraint_29_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_29 air row ↔ constraint_29 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) * ((air.cols.values.selected_word_0 row 0) - (((1 - (air.cols.values.offset_bit_2 row 0)) * (air.cols.values.memory_access.prev_value_0 row 0)) + ((0 + (air.cols.values.offset_bit_2 row 0)) * (air.cols.values.memory_access.prev_value_2 row 0))))) = 0

      @[simp]
      lemma constraint_30_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_30 air row ↔ constraint_30 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) * ((air.cols.values.selected_word_1 row 0) - (((1 - (air.cols.values.offset_bit_2 row 0)) * (air.cols.values.memory_access.prev_value_1 row 0)) + ((0 + (air.cols.values.offset_bit_2 row 0)) * (air.cols.values.memory_access.prev_value_3 row 0))))) = 0

      @[simp]
      lemma constraint_31_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_31 air row ↔ constraint_31 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) * ((air.cols.values.unsigned_mem_val_0 row 0) - (0 + (air.cols.values.selected_word_0 row 0)))) = 0

      @[simp]
      lemma constraint_32_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_32 air row ↔ constraint_32 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) * ((air.cols.values.unsigned_mem_val_1 row 0) - (0 + (air.cols.values.selected_word_1 row 0)))) = 0

      @[simp]
      lemma constraint_33_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_33 air row ↔ constraint_33 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) * ((air.cols.values.unsigned_mem_val_2 row 0) - 0)) = 0

      @[simp]
      lemma constraint_34_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_34 air row ↔ constraint_34 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lw row 0) + (air.cols.values.instruction.is_lwu row 0)) * ((air.cols.values.unsigned_mem_val_3 row 0) - 0)) = 0

      @[simp]
      lemma constraint_35_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_35 air row ↔ constraint_35 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_ld row 0) * ((air.cols.values.unsigned_mem_val_0 row 0) - (air.cols.values.memory_access.prev_value_0 row 0))) = 0

      @[simp]
      lemma constraint_36_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_36 air row ↔ constraint_36 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_ld row 0) * ((air.cols.values.unsigned_mem_val_1 row 0) - (air.cols.values.memory_access.prev_value_1 row 0))) = 0

      @[simp]
      lemma constraint_37_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_37 air row ↔ constraint_37 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_ld row 0) * ((air.cols.values.unsigned_mem_val_2 row 0) - (air.cols.values.memory_access.prev_value_2 row 0))) = 0

      @[simp]
      lemma constraint_38_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_38 air row ↔ constraint_38 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_ld row 0) * ((air.cols.values.unsigned_mem_val_3 row 0) - (air.cols.values.memory_access.prev_value_3 row 0))) = 0

      @[simp]
      lemma constraint_39_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_39 air row ↔ constraint_39 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_lbu row 0) * (air.cols.values.msb row 0)) = 0

      @[simp]
      lemma constraint_40_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_40 air row ↔ constraint_40 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_lh row 0) * ((air.cols.values.msb row 0) * ((air.cols.values.msb row 0) - 1))) = 0

      @[simp]
      lemma constraint_41_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_41 air row ↔ constraint_41 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_lhu row 0) * (air.cols.values.msb row 0)) = 0

      @[simp]
      lemma constraint_42_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_42 air row ↔ constraint_42 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_lw row 0) * ((air.cols.values.msb row 0) * ((air.cols.values.msb row 0) - 1))) = 0

      @[simp]
      lemma constraint_43_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_43 air row ↔ constraint_43 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((air.cols.values.instruction.is_lwu row 0) + (air.cols.values.instruction.is_ld row 0)) * (air.cols.values.msb row 0)) = 0

      @[simp]
      lemma constraint_44_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_44 air row ↔ constraint_44 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.op_a_0 row 0) * ((air.cols.values.instruction.op_a_0 row 0) - 1)) = 0

      @[simp]
      lemma constraint_45_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_45 air row ↔ constraint_45 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) - (((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lw row 0)) * (air.cols.values.msb row 0)) * (1 - (air.cols.values.instruction.op_a_0 row 0)))) = 0

      @[simp]
      lemma constraint_46_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_46 air row ↔ constraint_46 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_pos_not_x0 row 0) - ((((((air.cols.values.instruction.is_lbu row 0) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lw row 0)) * (1 - (air.cols.values.msb row 0)))) * (1 - (air.cols.values.instruction.op_a_0 row 0)))) = 0

      @[simp]
      lemma constraint_47_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_47 air row ↔ constraint_47 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lb row 0) * ((air.cols.values.instruction.op_a_access.access.value_0 row 0) - ((0 + (air.cols.values.selected_byte row 0)) + (65280 * (0 + (air.cols.values.msb row 0))))))) = 0

      @[simp]
      lemma constraint_48_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_48 air row ↔ constraint_48 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lb row 0) * ((air.cols.values.instruction.op_a_access.access.value_1 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_49_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_49 air row ↔ constraint_49 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lb row 0) * ((air.cols.values.instruction.op_a_access.access.value_2 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_50_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_50 air row ↔ constraint_50 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lb row 0) * ((air.cols.values.instruction.op_a_access.access.value_3 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_51_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_51 air row ↔ constraint_51 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lh row 0) * ((air.cols.values.instruction.op_a_access.access.value_0 row 0) - (0 + (air.cols.values.selected_limb row 0))))) = 0

      @[simp]
      lemma constraint_52_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_52 air row ↔ constraint_52 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lh row 0) * ((air.cols.values.instruction.op_a_access.access.value_1 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_53_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_53 air row ↔ constraint_53 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lh row 0) * ((air.cols.values.instruction.op_a_access.access.value_2 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_54_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_54 air row ↔ constraint_54 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lh row 0) * ((air.cols.values.instruction.op_a_access.access.value_3 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_55_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_55 air row ↔ constraint_55 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lw row 0) * ((air.cols.values.instruction.op_a_access.access.value_0 row 0) - (0 + (air.cols.values.selected_word_0 row 0))))) = 0

      @[simp]
      lemma constraint_56_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_56 air row ↔ constraint_56 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lw row 0) * ((air.cols.values.instruction.op_a_access.access.value_1 row 0) - (0 + (air.cols.values.selected_word_1 row 0))))) = 0

      @[simp]
      lemma constraint_57_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_57 air row ↔ constraint_57 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lw row 0) * ((air.cols.values.instruction.op_a_access.access.value_2 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_58_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_58 air row ↔ constraint_58 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_neg_not_x0 row 0) * ((air.cols.values.instruction.is_lw row 0) * ((air.cols.values.instruction.op_a_access.access.value_3 row 0) - (65535 * (0 + (air.cols.values.msb row 0)))))) = 0

      @[simp]
      lemma constraint_59_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_59 air row ↔ constraint_59 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_pos_not_x0 row 0) * ((air.cols.values.unsigned_mem_val_0 row 0) - (air.cols.values.instruction.op_a_access.access.value_0 row 0))) = 0

      @[simp]
      lemma constraint_60_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_60 air row ↔ constraint_60 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_pos_not_x0 row 0) * ((air.cols.values.unsigned_mem_val_1 row 0) - (air.cols.values.instruction.op_a_access.access.value_1 row 0))) = 0

      @[simp]
      lemma constraint_61_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_61 air row ↔ constraint_61 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_pos_not_x0 row 0) * ((air.cols.values.unsigned_mem_val_2 row 0) - (air.cols.values.instruction.op_a_access.access.value_2 row 0))) = 0

      @[simp]
      lemma constraint_62_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_62 air row ↔ constraint_62 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.mem_value_is_pos_not_x0 row 0) * ((air.cols.values.unsigned_mem_val_3 row 0) - (air.cols.values.instruction.op_a_access.access.value_3 row 0))) = 0

      @[simp]
      lemma constraint_63_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_63 air row ↔ constraint_63 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sb row 0) * ((air.cols.values.increment row 0) - (((1 - (air.cols.values.offset_bit_0 row 0)) * ((0 + (air.cols.values.register_low_byte row 0)) - (air.cols.values.mem_limb_low_byte row 0))) + ((0 + (air.cols.values.offset_bit_0 row 0)) * ((((0 + (air.cols.values.register_low_byte row 0)) * 256) - (air.cols.values.selected_limb row 0)) + (air.cols.values.mem_limb_low_byte row 0)))))) = 0

      @[simp]
      lemma constraint_64_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_64 air row ↔ constraint_64 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_65 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sb row 0) * ((air.cols.values.store_value_0 row 0) - ((0 + (air.cols.values.memory_access.prev_value_0 row 0)) + ((0 + (air.cols.values.increment row 0)) * (air.cols.values.limb_select_0 row 0))))) = 0

      @[simp]
      lemma constraint_65_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_65 air row ↔ constraint_65 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_66 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sb row 0) * ((air.cols.values.store_value_1 row 0) - ((0 + (air.cols.values.memory_access.prev_value_1 row 0)) + ((0 + (air.cols.values.increment row 0)) * (air.cols.values.limb_select_1 row 0))))) = 0

      @[simp]
      lemma constraint_66_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_66 air row ↔ constraint_66 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_67 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sb row 0) * ((air.cols.values.store_value_2 row 0) - ((0 + (air.cols.values.memory_access.prev_value_2 row 0)) + ((0 + (air.cols.values.increment row 0)) * (air.cols.values.limb_select_2 row 0))))) = 0

      @[simp]
      lemma constraint_67_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_67 air row ↔ constraint_67 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_68 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sb row 0) * ((air.cols.values.store_value_3 row 0) - ((0 + (air.cols.values.memory_access.prev_value_3 row 0)) + ((0 + (air.cols.values.increment row 0)) * (air.cols.values.limb_select_3 row 0))))) = 0

      @[simp]
      lemma constraint_68_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_68 air row ↔ constraint_68 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_69 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sh row 0) * ((air.cols.values.store_value_0 row 0) - ((0 + (air.cols.values.memory_access.prev_value_0 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.memory_access.prev_value_0 row 0)) * (air.cols.values.limb_select_0 row 0))))) = 0

      @[simp]
      lemma constraint_69_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_69 air row ↔ constraint_69 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_70 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sh row 0) * ((air.cols.values.store_value_1 row 0) - ((0 + (air.cols.values.memory_access.prev_value_1 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.memory_access.prev_value_1 row 0)) * (air.cols.values.limb_select_1 row 0))))) = 0

      @[simp]
      lemma constraint_70_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_70 air row ↔ constraint_70 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_71 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sh row 0) * ((air.cols.values.store_value_2 row 0) - ((0 + (air.cols.values.memory_access.prev_value_2 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.memory_access.prev_value_2 row 0)) * (air.cols.values.limb_select_2 row 0))))) = 0

      @[simp]
      lemma constraint_71_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_71 air row ↔ constraint_71 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_72 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sh row 0) * ((air.cols.values.store_value_3 row 0) - ((0 + (air.cols.values.memory_access.prev_value_3 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.memory_access.prev_value_3 row 0)) * (air.cols.values.limb_select_3 row 0))))) = 0

      @[simp]
      lemma constraint_72_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_72 air row ↔ constraint_72 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_73 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sw row 0) * ((air.cols.values.store_value_0 row 0) - ((0 + (air.cols.values.memory_access.prev_value_0 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.memory_access.prev_value_0 row 0)) * (1 - (air.cols.values.offset_bit_2 row 0)))))) = 0

      @[simp]
      lemma constraint_73_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_73 air row ↔ constraint_73 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_74 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sw row 0) * ((air.cols.values.store_value_1 row 0) - ((0 + (air.cols.values.memory_access.prev_value_1 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_1 row 0)) - (air.cols.values.memory_access.prev_value_1 row 0)) * (1 - (air.cols.values.offset_bit_2 row 0)))))) = 0

      @[simp]
      lemma constraint_74_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_74 air row ↔ constraint_74 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_75 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sw row 0) * ((air.cols.values.store_value_2 row 0) - ((0 + (air.cols.values.memory_access.prev_value_2 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.memory_access.prev_value_2 row 0)) * (0 + (air.cols.values.offset_bit_2 row 0)))))) = 0

      @[simp]
      lemma constraint_75_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_75 air row ↔ constraint_75 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_76 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sw row 0) * ((air.cols.values.store_value_3 row 0) - ((0 + (air.cols.values.memory_access.prev_value_3 row 0)) + (((0 + (air.cols.values.instruction.op_a_access.access.value_1 row 0)) - (air.cols.values.memory_access.prev_value_3 row 0)) * (0 + (air.cols.values.offset_bit_2 row 0)))))) = 0

      @[simp]
      lemma constraint_76_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_76 air row ↔ constraint_76 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_77 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sd row 0) * ((air.cols.values.store_value_0 row 0) - (air.cols.values.instruction.op_a_access.access.value_0 row 0))) = 0

      @[simp]
      lemma constraint_77_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_77 air row ↔ constraint_77 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_78 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sd row 0) * ((air.cols.values.store_value_1 row 0) - (air.cols.values.instruction.op_a_access.access.value_1 row 0))) = 0

      @[simp]
      lemma constraint_78_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_78 air row ↔ constraint_78 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_79 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sd row 0) * ((air.cols.values.store_value_2 row 0) - (air.cols.values.instruction.op_a_access.access.value_2 row 0))) = 0

      @[simp]
      lemma constraint_79_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_79 air row ↔ constraint_79 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_80 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.is_sd row 0) * ((air.cols.values.store_value_3 row 0) - (air.cols.values.instruction.op_a_access.access.value_3 row 0))) = 0

      @[simp]
      lemma constraint_80_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_80 air row ↔ constraint_80 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_81 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)) * ((air.cols.values.memory_access.access.value_0 row 0) - (air.cols.values.store_value_0 row 0))) = 0

      @[simp]
      lemma constraint_81_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_81 air row ↔ constraint_81 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_82 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)) * ((air.cols.values.memory_access.access.value_1 row 0) - (air.cols.values.store_value_1 row 0))) = 0

      @[simp]
      lemma constraint_82_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_82 air row ↔ constraint_82 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_83 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)) * ((air.cols.values.memory_access.access.value_2 row 0) - (air.cols.values.store_value_2 row 0))) = 0

      @[simp]
      lemma constraint_83_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_83 air row ↔ constraint_83 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_84 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        (((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)) * ((air.cols.values.memory_access.access.value_3 row 0) - (air.cols.values.store_value_3 row 0))) = 0

      @[simp]
      lemma constraint_84_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_84 air row ↔ constraint_84 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      -- Constraints 85-88 (Pico PR #101 commit `7860af12`): when `op_a_0 = 1`
      -- (rd = x0), pin each `op_a_access.access.value_i` to zero. Closes the
      -- soundness gap where the existing fill constraints (c48-c63) all carry
      -- `(1 - op_a_0)` and so leave the payload unconstrained on x0 writes.

      @[constraint_and_interaction_simplification]
      def constraint_85 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.op_a_0 row 0) * (air.cols.values.instruction.op_a_access.access.value_0 row 0)) = 0

      @[simp]
      lemma constraint_85_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_85 air row ↔ constraint_85 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_86 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.op_a_0 row 0) * (air.cols.values.instruction.op_a_access.access.value_1 row 0)) = 0

      @[simp]
      lemma constraint_86_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_86 air row ↔ constraint_86 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_87 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.op_a_0 row 0) * (air.cols.values.instruction.op_a_access.access.value_2 row 0)) = 0

      @[simp]
      lemma constraint_87_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_87 air row ↔ constraint_87 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def constraint_88 (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : Prop :=
        ((air.cols.values.instruction.op_a_0 row 0) * (air.cols.values.instruction.op_a_access.access.value_3 row 0)) = 0

      @[simp]
      lemma constraint_88_equiv (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ)
      : MemoryReadWriteChip.Extraction.constraint_88 air row ↔ constraint_88 air row
      := by simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

      @[constraint_and_interaction_simplification]
      def row_constraint_list (air : Valid_MemoryReadWriteChip F ExtF) (row : ℕ) : List Prop :=
        [
          constraint_0 air row,
          constraint_1 air row,
          constraint_2 air row,
          constraint_3 air row,
          constraint_4 air row,
          constraint_5 air row,
          constraint_6 air row,
          constraint_7 air row,
          constraint_8 air row,
          constraint_9 air row,
          constraint_10 air row,
          constraint_11 air row,
          constraint_12 air row,
          constraint_13 air row,
          constraint_14 air row,
          constraint_15 air row,
          constraint_16 air row,
          constraint_17 air row,
          constraint_18 air row,
          constraint_19 air row,
          constraint_20 air row,
          constraint_21 air row,
          constraint_22 air row,
          constraint_23 air row,
          constraint_24 air row,
          constraint_25 air row,
          constraint_26 air row,
          constraint_27 air row,
          constraint_28 air row,
          constraint_29 air row,
          constraint_30 air row,
          constraint_31 air row,
          constraint_32 air row,
          constraint_33 air row,
          constraint_34 air row,
          constraint_35 air row,
          constraint_36 air row,
          constraint_37 air row,
          constraint_38 air row,
          constraint_39 air row,
          constraint_40 air row,
          constraint_41 air row,
          constraint_42 air row,
          constraint_43 air row,
          constraint_44 air row,
          constraint_45 air row,
          constraint_46 air row,
          constraint_47 air row,
          constraint_48 air row,
          constraint_49 air row,
          constraint_50 air row,
          constraint_51 air row,
          constraint_52 air row,
          constraint_53 air row,
          constraint_54 air row,
          constraint_55 air row,
          constraint_56 air row,
          constraint_57 air row,
          constraint_58 air row,
          constraint_59 air row,
          constraint_60 air row,
          constraint_61 air row,
          constraint_62 air row,
          constraint_63 air row,
          constraint_64 air row,
          constraint_65 air row,
          constraint_66 air row,
          constraint_67 air row,
          constraint_68 air row,
          constraint_69 air row,
          constraint_70 air row,
          constraint_71 air row,
          constraint_72 air row,
          constraint_73 air row,
          constraint_74 air row,
          constraint_75 air row,
          constraint_76 air row,
          constraint_77 air row,
          constraint_78 air row,
          constraint_79 air row,
          constraint_80 air row,
          constraint_81 air row,
          constraint_82 air row,
          constraint_83 air row,
          constraint_84 air row,
          constraint_85 air row,
          constraint_86 air row,
          constraint_87 air row,
          constraint_88 air row
        ]

    end row_constraints

    section row_buses

      @[constraint_and_interaction_simplification]
      def raw_bus_row (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) : List (FKB × List FKB) :=
        [ (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))), [0, (air.cols.values.instruction.opcode row 0), (air.cols.values.instruction.op_a_access.access.value_0 row 0), (air.cols.values.instruction.op_a_access.access.value_1 row 0), (air.cols.values.instruction.op_a_access.access.value_2 row 0), (air.cols.values.instruction.op_a_access.access.value_3 row 0), (air.cols.values.instruction.op_b_access_0 row 0), (air.cols.values.instruction.op_b_access_1 row 0), (air.cols.values.instruction.op_b_access_2 row 0), (air.cols.values.instruction.op_b_access_3 row 0), (air.cols.values.instruction.op_c_access_0 row 0), (air.cols.values.instruction.op_c_access_1 row 0), (air.cols.values.instruction.op_c_access_2 row 0), (air.cols.values.instruction.op_c_access_3 row 0), (air.cols.values.instruction.op_a_0 row 0), (air.cols.values.instruction.is_lb row 0), (air.cols.values.instruction.is_lbu row 0), (air.cols.values.instruction.is_lh row 0), (air.cols.values.instruction.is_lhu row 0), (air.cols.values.instruction.is_lw row 0), (air.cols.values.instruction.is_lwu row 0), (air.cols.values.instruction.is_ld row 0), (air.cols.values.instruction.is_sb row 0), (air.cols.values.instruction.is_sh row 0), (air.cols.values.instruction.is_sw row 0), (air.cols.values.instruction.is_sd row 0)]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [3, 0, (air.cols.values.addr_word_0 row 0), (air.cols.values.addr_word_1 row 0), (air.cols.values.addr_word_2 row 0), (air.cols.values.addr_word_3 row 0), (air.cols.values.instruction.op_b_access_0 row 0), (air.cols.values.instruction.op_b_access_1 row 0), (air.cols.values.instruction.op_b_access_2 row 0), (air.cols.values.instruction.op_b_access_3 row 0), (air.cols.values.instruction.op_c_access_0 row 0), (air.cols.values.instruction.op_c_access_1 row 0), (air.cols.values.instruction.op_c_access_2 row 0), (air.cols.values.instruction.op_c_access_3 row 0)]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [4, 8, (air.cols.values.addr_word_0 row 0), 0, 0, 0]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [4, 8, (air.cols.values.addr_word_1 row 0), 0, 0, 0]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [4, 8, (air.cols.values.addr_word_2 row 0), 0, 0, 0]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [4, 9, (((0 + (air.cols.values.addr_word_0 row 0)) - (((0 + (air.cols.values.offset_bit_0 row 0)) + (2 * (air.cols.values.offset_bit_1 row 0))) + (4 * (air.cols.values.offset_bit_2 row 0)))) * 1864368129), 0, 13, 0]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [4, 8, (air.cols.values.memory_access.access.diff_16bit_limb row 0), 0, 0, 0]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [4, 7, 0, 0, (air.cols.values.memory_access.access.diff_8bit_limb row 0), 0]),
          (-(((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0)))), [0, (air.cols.values.memory_access.access.prev_chunk row 0), (air.cols.values.memory_access.access.prev_clk row 0), ((air.cols.values.addr_word_0 row 0) - ((0 + (air.cols.values.offset_bit_0 row 0)) + 2 * (air.cols.values.offset_bit_1 row 0) + 4 * (air.cols.values.offset_bit_2 row 0))), (air.cols.values.addr_word_1 row 0), (air.cols.values.addr_word_2 row 0), (air.cols.values.memory_access.prev_value_0 row 0), (air.cols.values.memory_access.prev_value_1 row 0), (air.cols.values.memory_access.prev_value_2 row 0), (air.cols.values.memory_access.prev_value_3 row 0)]),
          (((((((((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0)) + (air.cols.values.instruction.is_lh row 0)) + (air.cols.values.instruction.is_lhu row 0)) + (air.cols.values.instruction.is_lw row 0)) + (air.cols.values.instruction.is_lwu row 0)) + (air.cols.values.instruction.is_ld row 0)) + ((((air.cols.values.instruction.is_sb row 0) + (air.cols.values.instruction.is_sh row 0)) + (air.cols.values.instruction.is_sw row 0)) + (air.cols.values.instruction.is_sd row 0))), [0, (air.cols.values.chunk row 0), ((air.cols.values.clk row 0) + 0), ((air.cols.values.addr_word_0 row 0) - ((0 + (air.cols.values.offset_bit_0 row 0)) + 2 * (air.cols.values.offset_bit_1 row 0) + 4 * (air.cols.values.offset_bit_2 row 0))), (air.cols.values.addr_word_1 row 0), (air.cols.values.addr_word_2 row 0), (air.cols.values.memory_access.access.value_0 row 0), (air.cols.values.memory_access.access.value_1 row 0), (air.cols.values.memory_access.access.value_2 row 0), (air.cols.values.memory_access.access.value_3 row 0)]),
          (-(((air.cols.values.instruction.is_lb row 0) + (air.cols.values.instruction.is_lbu row 0))), [4, 7, 0, 0, (air.cols.values.selected_limb_low_byte row 0), (((0 + (air.cols.values.selected_limb row 0)) - (air.cols.values.selected_limb_low_byte row 0)) * 2122383361)]),
          (-((air.cols.values.instruction.is_lb row 0)), [4, 6, (air.cols.values.msb row 0), 0, (air.cols.values.selected_byte row 0), 0]),
          (-((air.cols.values.instruction.is_lh row 0)), [4, 8, (((2 * (air.cols.values.selected_limb row 0)) - 0) - ((air.cols.values.msb row 0) * 65536)), 0, 0, 0]),
          (-((air.cols.values.instruction.is_lw row 0)), [4, 8, (((2 * (air.cols.values.selected_word_1 row 0)) - 0) - ((air.cols.values.msb row 0) * 65536)), 0, 0, 0]),
          (-((air.cols.values.instruction.is_sb row 0)), [4, 7, 0, 0, (air.cols.values.register_low_byte row 0), (((0 + (air.cols.values.instruction.op_a_access.access.value_0 row 0)) - (air.cols.values.register_low_byte row 0)) * 2122383361)]),
          (-((air.cols.values.instruction.is_sb row 0)), [4, 7, 0, 0, (air.cols.values.mem_limb_low_byte row 0), (((0 + (air.cols.values.selected_limb row 0)) - (air.cols.values.mem_limb_low_byte row 0)) * 2122383361)]) ]

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

    set_option maxRecDepth 2_000_000 in
    @[simp]
    lemma allHold_iff_allHold_simplified
      (air : Valid_MemoryReadWriteChip FKB ExtF)
      (row : ℕ)
    :
      MemoryReadWriteChip.Extraction.allHold air row ↔ allHold_simplified air row
    := by
      simp [pico_encapsulation, extracted_constraint_definition, constraint_and_interaction_simplification]

  end constraint_simplification

  -- =====================================================================
  -- Typed `BusRow` for `MemoryReadWriteChip`. Mirrors the 16 entries of
  -- `raw_bus_row` (1 Memory + 1 ALU + 12 Byte + 2 State; no Program
  -- entries), constructed directly from the air's accessors.
  --
  -- The chip embeds **no sub-gadgets** — all 85 constraints are inline
  -- chip-level relations (no `<Gadget>::eval` invocations on the Rust
  -- side, no `SubAir["...": "<Gadget>"]` in the Air). Spec proofs
  -- therefore consume the existing `allHold_simplified` (which exposes
  -- `constrain_interactions ∧ List.Forall (·) row_constraint_list`)
  -- directly — no abstract `AbsConstraints` decomposition is needed.
  -- =====================================================================

  variable [Field F] [Field ExtF]

  open RV64IM_Interactions

  @[constraint_and_interaction_simplification]
  def AbsBuses (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) : BusRow :=
    let is_mem    := air.cols.values.is_real row 0
    let is_lb     := air.cols.values.instruction.is_lb     row 0
    let is_lbu    := air.cols.values.instruction.is_lbu    row 0
    let is_lh     := air.cols.values.instruction.is_lh     row 0
    let is_lhu    := air.cols.values.instruction.is_lhu    row 0
    let is_lw     := air.cols.values.instruction.is_lw     row 0
    let is_lwu    := air.cols.values.instruction.is_lwu    row 0
    let is_ld     := air.cols.values.instruction.is_ld     row 0
    let is_sb     := air.cols.values.instruction.is_sb     row 0
    let is_sh     := air.cols.values.instruction.is_sh     row 0
    let is_sw     := air.cols.values.instruction.is_sw     row 0
    let is_sd     := air.cols.values.instruction.is_sd     row 0
    let opcode    := air.cols.values.instruction.opcode    row 0
    let op_a_0    := air.cols.values.instruction.op_a_0    row 0
    let a_0 := air.cols.values.instruction.op_a_access.access.value_0 row 0
    let a_1 := air.cols.values.instruction.op_a_access.access.value_1 row 0
    let a_2 := air.cols.values.instruction.op_a_access.access.value_2 row 0
    let a_3 := air.cols.values.instruction.op_a_access.access.value_3 row 0
    let b_0 := air.cols.values.instruction.op_b_access_0 row 0
    let b_1 := air.cols.values.instruction.op_b_access_1 row 0
    let b_2 := air.cols.values.instruction.op_b_access_2 row 0
    let b_3 := air.cols.values.instruction.op_b_access_3 row 0
    let c_0 := air.cols.values.instruction.op_c_access_0 row 0
    let c_1 := air.cols.values.instruction.op_c_access_1 row 0
    let c_2 := air.cols.values.instruction.op_c_access_2 row 0
    let c_3 := air.cols.values.instruction.op_c_access_3 row 0
    let addr_word_0 := air.cols.values.addr_word_0 row 0
    let addr_word_1 := air.cols.values.addr_word_1 row 0
    let addr_word_2 := air.cols.values.addr_word_2 row 0
    let addr_word_3 := air.cols.values.addr_word_3 row 0
    let offset_bit_0 := air.cols.values.offset_bit_0 row 0
    let offset_bit_1 := air.cols.values.offset_bit_1 row 0
    let offset_bit_2 := air.cols.values.offset_bit_2 row 0
    -- Aligned address now computed inline (Pico PR #101 commit db682d9c).
    let addr_aligned_0 := addr_word_0 -
      ((0 + offset_bit_0) + 2 * offset_bit_1 + 4 * offset_bit_2)
    let addr_aligned_1 := addr_word_1
    let addr_aligned_2 := addr_word_2
    let chunk := air.cols.values.chunk row 0
    let clk   := air.cols.values.clk   row 0
    let prev_chunk := air.cols.values.memory_access.access.prev_chunk row 0
    let prev_clk   := air.cols.values.memory_access.access.prev_clk   row 0
    let mem_prev_0 := air.cols.values.memory_access.prev_value_0 row 0
    let mem_prev_1 := air.cols.values.memory_access.prev_value_1 row 0
    let mem_prev_2 := air.cols.values.memory_access.prev_value_2 row 0
    let mem_prev_3 := air.cols.values.memory_access.prev_value_3 row 0
    let mem_val_0 := air.cols.values.memory_access.access.value_0 row 0
    let mem_val_1 := air.cols.values.memory_access.access.value_1 row 0
    let mem_val_2 := air.cols.values.memory_access.access.value_2 row 0
    let mem_val_3 := air.cols.values.memory_access.access.value_3 row 0
    let diff_16 := air.cols.values.memory_access.access.diff_16bit_limb row 0
    let diff_8  := air.cols.values.memory_access.access.diff_8bit_limb  row 0
    let selected_limb          := air.cols.values.selected_limb          row 0
    let selected_limb_low_byte := air.cols.values.selected_limb_low_byte row 0
    let selected_byte          := air.cols.values.selected_byte          row 0
    let selected_word_1        := air.cols.values.selected_word_1        row 0
    let msb                    := air.cols.values.msb                    row 0
    let register_low_byte      := air.cols.values.register_low_byte      row 0
    let mem_limb_low_byte      := air.cols.values.mem_limb_low_byte      row 0
    {
      Program := [],
      ALU := List.map ALUBusEntry.deserialise [
        -- ALU ADD: addr_word = op_b + op_c (gated by -is_mem).
        (-(is_mem), #v[0,
                      addr_word_0, addr_word_1, addr_word_2, addr_word_3,
                      b_0, b_1, b_2, b_3,
                      c_0, c_1, c_2, c_3])
      ],
      Byte := List.map ByteBusEntry.deserialise [
        -- u16 range checks on addr_word_0..2 (gated by -is_mem).
        (-(is_mem), #v[8, addr_word_0, 0, 0, 0]),
        (-(is_mem), #v[8, addr_word_1, 0, 0, 0]),
        (-(is_mem), #v[8, addr_word_2, 0, 0, 0]),
        -- BitRange-13 on (addr_word_0 - offset_decoded) / 8, binding
        -- offset_bits to addr_word_0's low 3 bits (-is_mem).
        (-(is_mem), #v[9,
                      ((0 + addr_word_0) - ((0 + offset_bit_0) +
                          2 * offset_bit_1 + 4 * offset_bit_2)) * 1864368129,
                      0, 13, 0]),
        -- u16 range on diff_16bit_limb (memory access metadata, -is_mem).
        (-(is_mem), #v[8, diff_16, 0, 0, 0]),
        -- u8 range on diff_8bit_limb (memory access metadata, -is_mem).
        (-(is_mem), #v[7, 0, 0, diff_8, 0]),
        -- Two-byte range check on the (low, high) decomposition of `selected_limb`
        -- (Pico PR #101 commit `fc197c0b`, gated by -(is_lb + is_lbu)).
        (-(is_lb + is_lbu), #v[7, 0, 0, selected_limb_low_byte,
                              ((0 + selected_limb) - selected_limb_low_byte) * 2122383361]),
        -- MSB lookup: verify `msb` is bit-7 of selected_byte (-is_lb).
        (-(is_lb), #v[6, msb, 0, selected_byte, 0]),
        -- U16MSB on selected_limb: 2·selected_limb - msb·2^16 ∈ [0, 2^16)
        -- (-is_lh).
        (-(is_lh), #v[8, ((2 * selected_limb) - 0) - (msb * 65536), 0, 0, 0]),
        -- U16MSB on selected_word_1: 2·selected_word_1 - msb·2^16 ∈
        -- [0, 2^16) (-is_lw).
        (-(is_lw), #v[8, ((2 * selected_word_1) - 0) - (msb * 65536), 0, 0, 0]),
        -- SB byte split of `op_a_value_0`: low+high byte pair (-is_sb).
        (-(is_sb), #v[7, 0, 0, register_low_byte,
                     ((0 + a_0) - register_low_byte) * 2122383361]),
        -- SB byte split of `selected_limb`: low+high byte pair (-is_sb).
        (-(is_sb), #v[7, 0, 0, mem_limb_low_byte,
                     ((0 + selected_limb) - mem_limb_low_byte) * 2122383361])
      ],
      State := List.map StateBusEntry.deserialise [
        -- Previous memory access at addr_aligned (-is_mem).
        (-(is_mem), #v[prev_chunk, prev_clk,
                      addr_aligned_0, addr_aligned_1, addr_aligned_2,
                      mem_prev_0, mem_prev_1, mem_prev_2, mem_prev_3]),
        -- Current memory access at addr_aligned (+is_mem).
        (is_mem, #v[chunk, clk + 0,
                     addr_aligned_0, addr_aligned_1, addr_aligned_2,
                     mem_val_0, mem_val_1, mem_val_2, mem_val_3])
      ],
      Memory := List.map MemoryBusEntry.deserialise [
        -- Receive the decoded load/store instruction from CpuChip
        -- (+is_mem looked from this chip's side).
        (is_mem, #v[opcode,
                     a_0, a_1, a_2, a_3,
                     b_0, b_1, b_2, b_3,
                     c_0, c_1, c_2, c_3,
                     op_a_0,
                     is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld,
                     is_sb, is_sh, is_sw, is_sd])
      ]
    }

end MemoryReadWriteChip.ConstraintsAndBuses

namespace MemoryReadWriteChip.Interactions

  open RV64IM_Interactions

  /-- The typed `BusRow` per `MemoryReadWriteChip` row. Just an alias
      for `ConstraintsAndBuses.AbsBuses`, which already takes the air
      directly. -/
  def bus_row (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) : BusRow :=
    MemoryReadWriteChip.ConstraintsAndBuses.AbsBuses air row

  /-- Trivial unfolding of `bus_row`. -/
  @[simp]
  lemma bus_row_def (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) :
    bus_row air row = MemoryReadWriteChip.ConstraintsAndBuses.AbsBuses air row
  := rfl

  @[simp]
  lemma bus_row_equiv (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ) :
    RV64IM_Interactions.deserialise_bus_row
      (MemoryReadWriteChip.ConstraintsAndBuses.raw_bus_row air row) = bus_row air row
  := by
    simp [
      deserialise_bus_row,
      constraint_and_interaction_simplification,
      bus_row,
      MemoryReadWriteChip.ConstraintsAndBuses.AbsBuses,
      pico_encapsulation,
    ]
    refine ⟨?_, ?_⟩ <;> rw [← MemoryChipValueCols.is_real_def] <;> ring

end MemoryReadWriteChip.Interactions

namespace MemoryReadWriteChip.Interpretations

  open RV64IM_Interactions
  open MemoryReadWriteChip.ConstraintsAndBuses
  open MemoryReadWriteChip.Interactions

  /-- Booleanness facts derivable from the chip's own constraints (no
      bus assumption needed):
        * `is_real ∈ {0, 1}` — sum of the 11 instruction selectors is
          boolean (constraint 12).
        * `op_a_0 ∈ {0, 1}` — the x0 flag is boolean (constraint 45).

      Individual selector booleanness (`is_lb ∈ {0, 1}` etc.) is **not**
      enforced by chip constraints alone — it comes from the Memory-bus
      `externals` consumed by `selector_exclusivity` below. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
  :
    (air.cols.values.is_real row 0 = 0 ∨ air.cols.values.is_real row 0 = 1) ∧
    (air.cols.values.instruction.op_a_0 row 0 = 0 ∨
     air.cols.values.instruction.op_a_0 row 0 = 1)
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c12, h_c45 ⟩ : constraint_12 air row ∧ constraint_45 air row := by aesop
    clear h_constraints
    refine ⟨?_, ?_⟩
    . simp only [constraint_12] at h_c12
      have h_def := MemoryChipValueCols.is_real_def air.cols.values row 0
      grind
    . simp only [constraint_45] at h_c45
      clear *- h_c45; grind

  /-- Selector exclusivity from the Memory-bus assumption. Given the
      chip-level `is_real ∈ {0, 1}` and `bus_row_ext_asm` (the chip's
      assumed bus externals, in particular the Memory-bus
      `externals` enforced by `CpuChip`), under `is_real = 1` we get:
        * the `mem_opcode` lies in `{10..17, 45, 46, 47}`;
        * exactly one of the 11 instruction selectors is `1` (matching
          the opcode), all others are `0`.

      The `b_*, c_* < 65536` u16-range facts (also part of the Memory-bus
      externals) are exposed too for downstream use. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
  :
    let opcode := air.cols.values.instruction.opcode      row 0
    let is_lb  := air.cols.values.instruction.is_lb       row 0
    let is_lbu := air.cols.values.instruction.is_lbu      row 0
    let is_lh  := air.cols.values.instruction.is_lh       row 0
    let is_lhu := air.cols.values.instruction.is_lhu      row 0
    let is_lw  := air.cols.values.instruction.is_lw       row 0
    let is_lwu := air.cols.values.instruction.is_lwu      row 0
    let is_ld  := air.cols.values.instruction.is_ld       row 0
    let is_sb  := air.cols.values.instruction.is_sb       row 0
    let is_sh  := air.cols.values.instruction.is_sh       row 0
    let is_sw  := air.cols.values.instruction.is_sw       row 0
    let is_sd  := air.cols.values.instruction.is_sd       row 0
    let b_0 := air.cols.values.instruction.op_b_access_0 row 0
    let b_1 := air.cols.values.instruction.op_b_access_1 row 0
    let b_2 := air.cols.values.instruction.op_b_access_2 row 0
    let b_3 := air.cols.values.instruction.op_b_access_3 row 0
    let c_0 := air.cols.values.instruction.op_c_access_0 row 0
    let c_1 := air.cols.values.instruction.op_c_access_1 row 0
    let c_2 := air.cols.values.instruction.op_c_access_2 row 0
    let c_3 := air.cols.values.instruction.op_c_access_3 row 0
    (opcode ∈ Finset.Icc (10 : FKB) 17 ∨ opcode ∈ Finset.Icc (45 : FKB) 47) ∧
    b_0.val < 65536 ∧ b_1.val < 65536 ∧ b_2.val < 65536 ∧ b_3.val < 65536 ∧
    c_0.val < 65536 ∧ c_1.val < 65536 ∧ c_2.val < 65536 ∧ c_3.val < 65536 ∧
    (opcode = 10 →
      is_lb = 1 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 11 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 1 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 12 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 1 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 13 →
      is_lb = 0 ∧ is_lbu = 1 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 14 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 1 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 15 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 1 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 16 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 1 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 17 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 1 ∧ is_sd = 0) ∧
    (opcode = 45 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 1 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 46 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 1 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 0) ∧
    (opcode = 47 →
      is_lb = 0 ∧ is_lbu = 0 ∧ is_lh = 0 ∧ is_lhu = 0 ∧ is_lw = 0 ∧
      is_lwu = 0 ∧ is_ld = 0 ∧ is_sb = 0 ∧ is_sh = 0 ∧ is_sw = 0 ∧ is_sd = 1)
  := by
    simp [AbsBuses, bus_row, bus_row_ext_asm, h_is_real,
          MemoryBusEntryInstance, MemoryBusEntry.deserialise] at h_ext
    grind

end MemoryReadWriteChip.Interpretations
