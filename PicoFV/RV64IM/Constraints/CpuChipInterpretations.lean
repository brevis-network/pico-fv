import PicoFV.RV64IM.Constraints.CpuChip

open Plonky3

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 2_000_000
set_option linter.constructorNameAsVariable false

namespace CpuChip.Interpretations

  open CpuChip.ConstraintsAndBuses
  open RV64IM_Interactions

  /-- The CPU chip's typed bus row, obtained by `deserialise_bus_row` from the
  chip's raw bus interactions. Lets downstream proofs take the canonical
  `bus_row_wf_asm (bus_row air row)` hypothesis (analogous to the MRW chip). -/
  def bus_row (air : Valid_CpuChip FKB ExtF) (row : ℕ) : BusRow :=
    deserialise_bus_row (CpuChip.ConstraintsAndBuses.raw_bus_row air row)

  /-- The Program-bus entry the CPU chip consumes on each row: the
  `(multiplicity, payload)` tuple deserialisable into `ProgramBusEntry FKB`.
  Mirrors the raw bus row's first entry (line ~2309 of `CpuChip.lean`). -/
  def program_bus_entry (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      FKB × Vector FKB 43 :=
    ( air.cols.is_real row 0
    , #v[ air.cols.pc_0 row 0
        , air.cols.pc_1 row 0
        , air.cols.pc_2 row 0
        , air.cols.instruction.opcode row 0
        , air.cols.instruction.opcode row 0
        , air.cols.instruction.op_a_0 row 0
        , air.cols.instruction.op_a_1 row 0
        , air.cols.instruction.op_a_2 row 0
        , air.cols.instruction.op_a_3 row 0
        , air.cols.instruction.op_b_0 row 0
        , air.cols.instruction.op_b_1 row 0
        , air.cols.instruction.op_b_2 row 0
        , air.cols.instruction.op_b_3 row 0
        , air.cols.instruction.op_c_0 row 0
        , air.cols.instruction.op_c_1 row 0
        , air.cols.instruction.op_c_2 row 0
        , air.cols.instruction.op_c_3 row 0
        , air.cols.instruction.op_a_is_x0 row 0
        , air.cols.opcode_selector.imm_b row 0
        , air.cols.opcode_selector.imm_c row 0
        , air.cols.opcode_selector.is_alu row 0
        , air.cols.opcode_selector.is_ecall row 0
        , air.cols.opcode_selector.is_lb row 0
        , air.cols.opcode_selector.is_lbu row 0
        , air.cols.opcode_selector.is_lh row 0
        , air.cols.opcode_selector.is_lhu row 0
        , air.cols.opcode_selector.is_lw row 0
        , air.cols.opcode_selector.is_lwu row 0
        , air.cols.opcode_selector.is_ld row 0
        , air.cols.opcode_selector.is_sb row 0
        , air.cols.opcode_selector.is_sh row 0
        , air.cols.opcode_selector.is_sw row 0
        , air.cols.opcode_selector.is_sd row 0
        , air.cols.opcode_selector.is_beq row 0
        , air.cols.opcode_selector.is_bne row 0
        , air.cols.opcode_selector.is_blt row 0
        , air.cols.opcode_selector.is_bge row 0
        , air.cols.opcode_selector.is_bltu row 0
        , air.cols.opcode_selector.is_bgeu row 0
        , air.cols.opcode_selector.is_jalr row 0
        , air.cols.opcode_selector.is_jal row 0
        , air.cols.opcode_selector.is_auipc row 0
        , air.cols.opcode_selector.is_unimpl row 0 ])

  /-- The chip's PC at `row`, packaged as a `U64w` with the top u16 limb
  hard-wired to `0` (RV64 PCs fit in 48 bits). The U64w form lets every PC
  equality be stated as a 64-bit `BitVec` addition, matching the Sail spec
  and the ALU bus's `execute_RTYPE_pure .ADD` shape. -/
  def pc (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
    #v[air.cols.pc_0 row 0, air.cols.pc_1 row 0, air.cols.pc_2 row 0, 0#16]

  /-- The chip's next PC at `row`, packaged as a `U64w` with the top u16 limb
  hard-wired to `0` (RV64 PCs fit in 48 bits). -/
  def next_pc (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
    #v[air.cols.next_pc_0 row 0, air.cols.next_pc_1 row 0, air.cols.next_pc_2 row 0, 0#16]

  -- ============================================================================
  -- Column rotation invariance: `cols.X row rotation = cols.X ((row + rotation)
  -- % (last_row + 1)) 0` for each chip column. Falls out of `air.isValid`'s
  -- `valid_circuit` clause specialised to the column's `main` index. Pattern
  -- copied from RV32IM's `pc_rotation` (PicoFV/RV32IM/Equivalence/Equivalence.lean).
  -- ============================================================================

  /-- `pc_0` column rotation invariance (column 5 in the chip's main grid). -/
  lemma pc_0_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.pc_0 row rotation = air.cols.pc_0 ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.pc_0 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 5 row rotation
      have valid_col_5 : ∀ row rotation, air.col_5 row rotation := by aesop
      unfold Raw_CpuChip.col_5 at valid_col_5
      iterate 2 rw [valid_col_5] at valid_circuit
      clear valid_col_5
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_5 row rotation := by aesop
      unfold Raw_CpuCols.col_5 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `pc_1` column rotation invariance (column 6). -/
  lemma pc_1_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.pc_1 row rotation = air.cols.pc_1 ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.pc_1 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 6 row rotation
      have valid_col_6 : ∀ row rotation, air.col_6 row rotation := by aesop
      unfold Raw_CpuChip.col_6 at valid_col_6
      iterate 2 rw [valid_col_6] at valid_circuit
      clear valid_col_6
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_6 row rotation := by aesop
      unfold Raw_CpuCols.col_6 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `pc_2` column rotation invariance (column 7). -/
  lemma pc_2_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.pc_2 row rotation = air.cols.pc_2 ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.pc_2 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 7 row rotation
      have valid_col_7 : ∀ row rotation, air.col_7 row rotation := by aesop
      unfold Raw_CpuChip.col_7 at valid_col_7
      iterate 2 rw [valid_col_7] at valid_circuit
      clear valid_col_7
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_7 row rotation := by aesop
      unfold Raw_CpuCols.col_7 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `next_pc_0` column rotation invariance (column 8). -/
  lemma next_pc_0_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.next_pc_0 row rotation =
        air.cols.next_pc_0 ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.next_pc_0 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 8 row rotation
      have valid_col_8 : ∀ row rotation, air.col_8 row rotation := by aesop
      unfold Raw_CpuChip.col_8 at valid_col_8
      iterate 2 rw [valid_col_8] at valid_circuit
      clear valid_col_8
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_8 row rotation := by aesop
      unfold Raw_CpuCols.col_8 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `next_pc_1` column rotation invariance (column 9). -/
  lemma next_pc_1_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.next_pc_1 row rotation =
        air.cols.next_pc_1 ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.next_pc_1 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 9 row rotation
      have valid_col_9 : ∀ row rotation, air.col_9 row rotation := by aesop
      unfold Raw_CpuChip.col_9 at valid_col_9
      iterate 2 rw [valid_col_9] at valid_circuit
      clear valid_col_9
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_9 row rotation := by aesop
      unfold Raw_CpuCols.col_9 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `next_pc_2` column rotation invariance (column 10). -/
  lemma next_pc_2_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.next_pc_2 row rotation =
        air.cols.next_pc_2 ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.next_pc_2 Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 10 row rotation
      have valid_col_10 : ∀ row rotation, air.col_10 row rotation := by aesop
      unfold Raw_CpuChip.col_10 at valid_col_10
      iterate 2 rw [valid_col_10] at valid_circuit
      clear valid_col_10
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_10 row rotation := by aesop
      unfold Raw_CpuCols.col_10 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `is_real` column rotation invariance (column 117 in the chip's main grid). -/
  lemma is_real_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.is_real row rotation = air.cols.is_real ((row + rotation) % (air.last_row + 1)) 0
    := by
      obtain ⟨ air, is_valid ⟩ := air
      unfold Valid_CpuCols.is_real Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit 117 row rotation
      have valid_col_117 : ∀ row rotation, air.col_117 row rotation := by aesop
      unfold Raw_CpuChip.col_117 at valid_col_117
      iterate 2 rw [valid_col_117] at valid_circuit
      clear valid_col_117
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_117 row rotation := by aesop
      unfold Raw_CpuCols.col_117 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- Helper: from `bus_row_wf_asm (bus_row air row)` and `is_real = 1`, derive
  the Program-bus entry's `operand_properties`: there exists a Sail instruction
  whose RV64 transpilation produces this row.

  The chip looks up the Program-bus entry with multiplicity `is_real`; under
  `is_real = 1` the consumer-side `wf_assume_cond` (multiplicity = 1) fires
  and gives `wf_properties = operand_properties` of the entry. -/
  lemma program_bus_operand_properties
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    ProgramBusEntry.operand_properties
      (ProgramBusEntry.deserialise (program_bus_entry air row))
  := by
    -- The Program-bus list inside `bus_row air row` is the singleton produced
    -- by `deserialise_bus_row` from `raw_bus_row`'s first (bus-id `2`) entry.
    -- `bus_row_wf_asm` is `List.Forall id` over a concatenation; its leading
    -- conjunct is the Program entry's `wf_assume` = `multiplicity = 1 →
    -- operand_properties`. Under `is_real = 1`, the multiplicity (`+is_real`)
    -- becomes `1`.
    simp [bus_row_wf_asm] at h_wf; replace h_wf := h_wf.1
    simp [bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf
    simpa [program_bus_entry, ProgramBusEntry.deserialise, h_is_real]

  /-- `selector_breakdown`: from `bus_row_wf_asm (bus_row air row)` and `is_real = 1`,
  the opcode lies in the valid RV64 set `[0..37] ∪ [40..47] ∪ [48..52]`, with
  `{26, 29, 38, 39}` explicitly excluded. Thin wrapper around
  `ProgramBusEntry.inversion_opcode_bounds`. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    ((air.cols.instruction.opcode row 0).val ≤ 37 ∨
     (40 ≤ (air.cols.instruction.opcode row 0).val ∧
      (air.cols.instruction.opcode row 0).val ≤ 47) ∨
     (48 ≤ (air.cols.instruction.opcode row 0).val ∧
      (air.cols.instruction.opcode row 0).val ≤ 52)) ∧
    (air.cols.instruction.opcode row 0).val ≠ 26 ∧
    (air.cols.instruction.opcode row 0).val ≠ 29 ∧
    (air.cols.instruction.opcode row 0).val ≠ 38 ∧
    (air.cols.instruction.opcode row 0).val ≠ 39
  := by
    have h_prog := program_bus_operand_properties air row h_is_real (by grind)
    obtain ⟨ instr, data, props, h_trans, h_deser, _ ⟩ := h_prog
    have h := ProgramBusEntry.inversion_opcode_bounds h_trans h_deser
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h
    assumption

  /-- `selector_exclusivity`: from `bus_row_wf_asm (bus_row air row)` and
  `is_real = 1`, for each valid opcode value `N`, the entire opcode-selector
  tuple is fixed to a specific pattern (with at most one selector equal to `1`).
  Thin wrapper around `ProgramBusEntry.inversion_opcode_selectors`. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    let entry := ProgramBusEntry.deserialise (program_bus_entry air row)
    -- Opcodes 0..9 (R-type / ITYPE / SHIFTIOP / LUI).
    (entry.opcode = 0 → ( entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 1 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 2 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 3 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 4 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 5 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 6 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 7 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 8 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 9 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- RV32-shared loads (10..14).
    (entry.opcode = 10 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 11 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 12 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 13 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 14 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- RV32-shared stores (15..17).
    (entry.opcode = 15 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 16 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 17 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- Branches (18..23).
    (entry.opcode = 18 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 19 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 20 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 21 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 22 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 23 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 )) ∧
    -- JAL (24), JALR (25), AUIPC (27), ECALL (28).
    (entry.opcode = 24 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 )) ∧
    (entry.opcode = 25 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 )) ∧
    (entry.opcode = 27 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 )) ∧
    (entry.opcode = 28 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- MUL family (30..33).
    (entry.opcode = 30 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 31 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 32 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 33 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- DIV/REM (34..37).
    (entry.opcode = 34 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 35 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 36 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 37 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- W-variants (40..44).
    (entry.opcode = 40 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 41 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 42 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 43 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 44 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- RV64-only memory ops (45..47).
    (entry.opcode = 45 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 46 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 47 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    -- RV64-only ALU ops (48..52).
    (entry.opcode = 48 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 49 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 50 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 51 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
    (entry.opcode = 52 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ))
  := by
    have h_prog := program_bus_operand_properties air row h_is_real (by grind)
    obtain ⟨ instr, data, props, h_trans, h_deser, _ ⟩ := h_prog
    exact ProgramBusEntry.inversion_opcode_selectors h_trans h_deser

  -- ============================================================================
  -- Compound-selector inversion: each "is_X = 1" pins the opcode to a specific set
  -- ============================================================================

  /-- `is_ecall = 1 ↔ opcode = 28`. -/
  lemma is_ecall_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_ecall row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 28
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_ecall; grind (splits := 64)
    . intro h_op; grind

  /-- `is_alu = 1 ↔ opcode ∈ {0..9, 30..37, 40..44, 48..52}` (R-type/ITYPE/SHIFTIOP/LUI,
  MUL family, DIV/REM, W-variants, RV64 DIV/REM-W). -/
  lemma is_alu_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_alu row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 0  ∨ (air.cols.instruction.opcode row 0).val = 1  ∨
    (air.cols.instruction.opcode row 0).val = 2  ∨ (air.cols.instruction.opcode row 0).val = 3  ∨
    (air.cols.instruction.opcode row 0).val = 4  ∨ (air.cols.instruction.opcode row 0).val = 5  ∨
    (air.cols.instruction.opcode row 0).val = 6  ∨ (air.cols.instruction.opcode row 0).val = 7  ∨
    (air.cols.instruction.opcode row 0).val = 8  ∨ (air.cols.instruction.opcode row 0).val = 9  ∨
    (air.cols.instruction.opcode row 0).val = 30 ∨ (air.cols.instruction.opcode row 0).val = 31 ∨
    (air.cols.instruction.opcode row 0).val = 32 ∨ (air.cols.instruction.opcode row 0).val = 33 ∨
    (air.cols.instruction.opcode row 0).val = 34 ∨ (air.cols.instruction.opcode row 0).val = 35 ∨
    (air.cols.instruction.opcode row 0).val = 36 ∨ (air.cols.instruction.opcode row 0).val = 37 ∨
    (air.cols.instruction.opcode row 0).val = 40 ∨ (air.cols.instruction.opcode row 0).val = 41 ∨
    (air.cols.instruction.opcode row 0).val = 42 ∨ (air.cols.instruction.opcode row 0).val = 43 ∨
    (air.cols.instruction.opcode row 0).val = 44 ∨ (air.cols.instruction.opcode row 0).val = 48 ∨
    (air.cols.instruction.opcode row 0).val = 49 ∨ (air.cols.instruction.opcode row 0).val = 50 ∨
    (air.cols.instruction.opcode row 0).val = 51 ∨ (air.cols.instruction.opcode row 0).val = 52
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_alu; grind (splits := 64)
    . intro h_op; grind (splits := 64)

  /-- `is_jal = 1 ↔ opcode = 24`. -/
  lemma is_jal_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_jal row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 24
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_jal; grind (splits := 64)
    . intro h_op; grind

  /-- `is_jalr = 1 ↔ opcode = 25`. -/
  lemma is_jalr_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_jalr row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 25
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_jalr; grind (splits := 64)
    . intro h_op; grind

  /-- `is_auipc = 1 ↔ opcode = 27`. -/
  lemma is_auipc_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_auipc row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 27
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_auipc; grind (splits := 64)
    . intro h_op; grind

  /-- Branch sum `is_beq + ... + is_bgeu = 1 ↔ opcode ∈ {18..23}` (the six conditional
  branches). -/
  lemma is_branch_sum_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_beq row 0 +
      air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 +
      air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 +
      air.cols.opcode_selector.is_bgeu row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 18 ∨ (air.cols.instruction.opcode row 0).val = 19 ∨
    (air.cols.instruction.opcode row 0).val = 20 ∨ (air.cols.instruction.opcode row 0).val = 21 ∨
    (air.cols.instruction.opcode row 0).val = 22 ∨ (air.cols.instruction.opcode row 0).val = 23
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_sum; grind (splits := 64)
    . intro h_op; grind (splits := 64)

  /-- Load sum `is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld = 1 ↔ opcode ∈
  {10, 11, 12, 13, 14, 45, 46}` (RV32 loads + RV64 LWU/LD). -/
  lemma is_load_sum_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_lb row 0 +
      air.cols.opcode_selector.is_lbu row 0 +
      air.cols.opcode_selector.is_lh row 0 +
      air.cols.opcode_selector.is_lhu row 0 +
      air.cols.opcode_selector.is_lw row 0 +
      air.cols.opcode_selector.is_lwu row 0 +
      air.cols.opcode_selector.is_ld row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 10 ∨ (air.cols.instruction.opcode row 0).val = 11 ∨
    (air.cols.instruction.opcode row 0).val = 12 ∨ (air.cols.instruction.opcode row 0).val = 13 ∨
    (air.cols.instruction.opcode row 0).val = 14 ∨ (air.cols.instruction.opcode row 0).val = 45 ∨
    (air.cols.instruction.opcode row 0).val = 46
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_sum; grind (splits := 64)
    . intro h_op; grind (splits := 64)

  /-- Store sum `is_sb + is_sh + is_sw + is_sd = 1 ↔ opcode ∈ {15, 16, 17, 47}`
  (RV32 stores + RV64 SD). -/
  lemma is_store_sum_eq_one_iff
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_sb row 0 +
      air.cols.opcode_selector.is_sh row 0 +
      air.cols.opcode_selector.is_sw row 0 +
      air.cols.opcode_selector.is_sd row 0 = 1 ↔
    (air.cols.instruction.opcode row 0).val = 15 ∨ (air.cols.instruction.opcode row 0).val = 16 ∨
    (air.cols.instruction.opcode row 0).val = 17 ∨ (air.cols.instruction.opcode row 0).val = 47
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    constructor
    . intro h_sum; grind (splits := 64)
    . intro h_op; grind (splits := 64)

  -- ============================================================================
  -- Instruction-class characterisations: under each `*_sum = 1` (or `jump_sum`),
  -- exactly one selector in the class fires (others are 0). Mirrors RV32's
  -- `is_branch_instruction_characterisation` / `is_jump_instruction_characterisation`
  -- / `is_store_instruction_characterisation` (CpuAir.lean:3100/3151/3171).
  -- ============================================================================

  /-- `branch_sum = 1` ⟹ exactly one of the 6 branch selectors is 1 (others 0). -/
  lemma branch_sum_picks_selector
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_branch_sum : air.cols.opcode_selector.is_beq row 0 +
                    air.cols.opcode_selector.is_bne row 0 +
                    air.cols.opcode_selector.is_blt row 0 +
                    air.cols.opcode_selector.is_bge row 0 +
                    air.cols.opcode_selector.is_bltu row 0 +
                    air.cols.opcode_selector.is_bgeu row 0 = 1)
  :
    let beq := air.cols.opcode_selector.is_beq row 0
    let bne := air.cols.opcode_selector.is_bne row 0
    let blt := air.cols.opcode_selector.is_blt row 0
    let bge := air.cols.opcode_selector.is_bge row 0
    let bltu := air.cols.opcode_selector.is_bltu row 0
    let bgeu := air.cols.opcode_selector.is_bgeu row 0
    (beq = 1 ∧ bne = 0 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 0) ∨
    (beq = 0 ∧ bne = 1 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 0) ∨
    (beq = 0 ∧ bne = 0 ∧ blt = 1 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 0) ∨
    (beq = 0 ∧ bne = 0 ∧ blt = 0 ∧ bge = 1 ∧ bltu = 0 ∧ bgeu = 0) ∨
    (beq = 0 ∧ bne = 0 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 1 ∧ bgeu = 0) ∨
    (beq = 0 ∧ bne = 0 ∧ blt = 0 ∧ bge = 0 ∧ bltu = 0 ∧ bgeu = 1)
  := by
    have h_op := (is_branch_sum_eq_one_iff air row h_is_real (by grind)).mp h_branch_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    grind (splits := 64)

  /-- `is_jal + is_jalr = 1` ⟹ exactly one of `is_jal, is_jalr` is 1. -/
  lemma jump_sum_picks_selector
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_jump_sum : air.cols.opcode_selector.is_jal row 0 +
                  air.cols.opcode_selector.is_jalr row 0 = 1)
  :
    (air.cols.opcode_selector.is_jal row 0 = 1 ∧ air.cols.opcode_selector.is_jalr row 0 = 0) ∨
    (air.cols.opcode_selector.is_jal row 0 = 0 ∧ air.cols.opcode_selector.is_jalr row 0 = 1)
  := by
    have h_bound := selector_breakdown air row h_is_real (by grind)
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    grind (splits := 64)

  /-- `store_sum = 1` ⟹ exactly one of the 4 store selectors is 1 (others 0). -/
  lemma store_sum_picks_selector
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_store_sum : air.cols.opcode_selector.is_sb row 0 +
                   air.cols.opcode_selector.is_sh row 0 +
                   air.cols.opcode_selector.is_sw row 0 +
                   air.cols.opcode_selector.is_sd row 0 = 1)
  :
    let sb := air.cols.opcode_selector.is_sb row 0
    let sh := air.cols.opcode_selector.is_sh row 0
    let sw := air.cols.opcode_selector.is_sw row 0
    let sd := air.cols.opcode_selector.is_sd row 0
    (sb = 1 ∧ sh = 0 ∧ sw = 0 ∧ sd = 0) ∨
    (sb = 0 ∧ sh = 1 ∧ sw = 0 ∧ sd = 0) ∨
    (sb = 0 ∧ sh = 0 ∧ sw = 1 ∧ sd = 0) ∨
    (sb = 0 ∧ sh = 0 ∧ sw = 0 ∧ sd = 1)
  := by
    have h_op := (is_store_sum_eq_one_iff air row h_is_real (by grind)).mp h_store_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    grind (splits := 64)

  /-- `load_sum = 1` ⟹ exactly one of the 7 load selectors is 1 (others 0). -/
  lemma load_sum_picks_selector
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_load_sum : air.cols.opcode_selector.is_lb row 0 +
                  air.cols.opcode_selector.is_lbu row 0 +
                  air.cols.opcode_selector.is_lh row 0 +
                  air.cols.opcode_selector.is_lhu row 0 +
                  air.cols.opcode_selector.is_lw row 0 +
                  air.cols.opcode_selector.is_lwu row 0 +
                  air.cols.opcode_selector.is_ld row 0 = 1)
  :
    let lb := air.cols.opcode_selector.is_lb row 0
    let lbu := air.cols.opcode_selector.is_lbu row 0
    let lh := air.cols.opcode_selector.is_lh row 0
    let lhu := air.cols.opcode_selector.is_lhu row 0
    let lw := air.cols.opcode_selector.is_lw row 0
    let lwu := air.cols.opcode_selector.is_lwu row 0
    let ld := air.cols.opcode_selector.is_ld row 0
    (lb = 1 ∧ lbu = 0 ∧ lh = 0 ∧ lhu = 0 ∧ lw = 0 ∧ lwu = 0 ∧ ld = 0) ∨
    (lb = 0 ∧ lbu = 1 ∧ lh = 0 ∧ lhu = 0 ∧ lw = 0 ∧ lwu = 0 ∧ ld = 0) ∨
    (lb = 0 ∧ lbu = 0 ∧ lh = 1 ∧ lhu = 0 ∧ lw = 0 ∧ lwu = 0 ∧ ld = 0) ∨
    (lb = 0 ∧ lbu = 0 ∧ lh = 0 ∧ lhu = 1 ∧ lw = 0 ∧ lwu = 0 ∧ ld = 0) ∨
    (lb = 0 ∧ lbu = 0 ∧ lh = 0 ∧ lhu = 0 ∧ lw = 1 ∧ lwu = 0 ∧ ld = 0) ∨
    (lb = 0 ∧ lbu = 0 ∧ lh = 0 ∧ lhu = 0 ∧ lw = 0 ∧ lwu = 1 ∧ ld = 0) ∨
    (lb = 0 ∧ lbu = 0 ∧ lh = 0 ∧ lhu = 0 ∧ lw = 0 ∧ lwu = 0 ∧ ld = 1)
  := by
    have h_op := (is_load_sum_eq_one_iff air row h_is_real (by grind)).mp h_load_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    grind (splits := 128)

  -- ============================================================================
  -- Background facts on real rows (chip row constraints + bus u16 bounds on PC)
  -- ============================================================================

  /-- Constraints that are non-vacuous and **independent of the opcode selectors**
  when `is_real = 1`. This is the common background that every per-opcode
  characterisation (ALU, Branch, Load, ...) inherits.

  Outputs (in conjunction order):
    * **x0 zeroing** of `op_a_access.access.value_i` (c16-c19) — no `is_real` gate,
      always hold.
    * **op_a memory access** (c21-c23 with `is_real = 1` substituted):
      `compare_clk` boolean, chunk continuity when `compare_clk = 1`, and the
      clock-difference range-check decomposition into 16+8-bit limbs.
    * **Clock limb decomposition** (c156 specialised): `clk = clk_16bit_limb +
      clk_8bit_limb · 65536`.
    * **pc_carry booleans** (c184-c192) — both carry chains in `{0, 1}`.

  (The bus-side `pc / next_pc < 2^48` facts are intentionally NOT in the
  conclusion: under the `U48w` packing they become vacuous, and the per-limb
  u16 bounds are available on demand from `h_wf` via the Byte-bus lookups.) -/
  lemma is_real_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- x0 zeroing (c16-c19)
    (¬ air.cols.instruction.op_a_is_x0 row 0 = 0 → air.cols.op_a_access.access.value_0 row 0 = 0) ∧
    (¬ air.cols.instruction.op_a_is_x0 row 0 = 0 → air.cols.op_a_access.access.value_1 row 0 = 0) ∧
    (¬ air.cols.instruction.op_a_is_x0 row 0 = 0 → air.cols.op_a_access.access.value_2 row 0 = 0) ∧
    (¬ air.cols.instruction.op_a_is_x0 row 0 = 0 → air.cols.op_a_access.access.value_3 row 0 = 0) ∧
    -- op_a memory access bookkeeping (c21-c23, two-case form)
    -- (c21) compare_clk boolean
    (air.cols.op_a_access.access.compare_clk row 0 = 0 ∨
     air.cols.op_a_access.access.compare_clk row 0 = 1) ∧
    -- Same-chunk case: chunk stays, clk strictly advances by (diff + 1)
    (air.cols.op_a_access.access.compare_clk row 0 = 1 →
      air.cols.chunk row 0 = air.cols.op_a_access.access.prev_chunk row 0 ∧
      air.cols.op_a_access.access.diff_16bit_limb row 0 +
        air.cols.op_a_access.access.diff_8bit_limb row 0 * 65536 +
        air.cols.op_a_access.access.prev_clk row 0 + 1 =
        air.cols.clk row 0 + 3) ∧
    -- New-chunk case: chunk strictly advances by (diff + 1)
    (air.cols.op_a_access.access.compare_clk row 0 = 0 →
      air.cols.op_a_access.access.diff_16bit_limb row 0 +
        air.cols.op_a_access.access.diff_8bit_limb row 0 * 65536 +
        air.cols.op_a_access.access.prev_chunk row 0 + 1 =
        air.cols.chunk row 0) ∧
    -- Clock limb decomposition (c156)
    air.cols.clk row 0 = air.cols.clk_16bit_limb row 0 + air.cols.clk_8bit_limb row 0 * 65536 ∧
    -- pc_carry booleans (c184-c192)
    (air.cols.pc_carry_a_0 row 0 = 0 ∨ air.cols.pc_carry_a_0 row 0 = 1) ∧
    (air.cols.pc_carry_a_1 row 0 = 0 ∨ air.cols.pc_carry_a_1 row 0 = 1) ∧
    (air.cols.pc_carry_a_2 row 0 = 0 ∨ air.cols.pc_carry_a_2 row 0 = 1) ∧
    (air.cols.pc_carry_a_3 row 0 = 0 ∨ air.cols.pc_carry_a_3 row 0 = 1) ∧
    (air.cols.pc_carry_a_4 row 0 = 0 ∨ air.cols.pc_carry_a_4 row 0 = 1) ∧
    (air.cols.pc_carry_b_0 row 0 = 0 ∨ air.cols.pc_carry_b_0 row 0 = 1) ∧
    (air.cols.pc_carry_b_1 row 0 = 0 ∨ air.cols.pc_carry_b_1 row 0 = 1) ∧
    (air.cols.pc_carry_b_2 row 0 = 0 ∨ air.cols.pc_carry_b_2 row 0 = 1) ∧
    (air.cols.pc_carry_b_3 row 0 = 0 ∨ air.cols.pc_carry_b_3 row 0 = 1) ∧
    -- pc and next_pc ranges
    (air.cols.pc_0 row 0).val < 65536 ∧ (air.cols.pc_1 row 0).val < 65536 ∧ (air.cols.pc_2 row 0).val < 65536 ∧
    (air.cols.next_pc_0 row 0).val < 65536 ∧ (air.cols.next_pc_1 row 0).val < 65536 ∧ (air.cols.next_pc_2 row 0).val < 65536
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c16, h_c17, h_c18, h_c19, h_c21, h_c22, h_c23, h_c156,
             h_c184, h_c185, h_c186, h_c187, h_c188,
             h_c189, h_c190, h_c191, h_c192 ⟩
    : constraint_16 air row ∧ constraint_17 air row ∧
      constraint_18 air row ∧ constraint_19 air row ∧
      constraint_21 air row ∧ constraint_22 air row ∧ constraint_23 air row ∧
      constraint_156 air row ∧
      constraint_184 air row ∧ constraint_185 air row ∧ constraint_186 air row ∧
      constraint_187 air row ∧ constraint_188 air row ∧
      constraint_189 air row ∧ constraint_190 air row ∧ constraint_191 air row ∧
      constraint_192 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_is_real, one_mul, sub_eq_zero]
      at h_c16 h_c17 h_c18 h_c19 h_c21 h_c22 h_c23 h_c156
         h_c184 h_c185 h_c186 h_c187 h_c188 h_c189 h_c190 h_c191 h_c192
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real,
          ByteBus.Spec] at h_wf
    simp [*]
    -- The pc ranges came from `h_wf`; the rest follows from the constraints alone, and
    -- `grind` wanders on `h_wf`'s unrelated bus implications.
    clear h_wf
    grind

  -- ============================================================================
  -- Carry-chain → BV-sum (pure arithmetic + a chip-specialised wrapper)
  -- ============================================================================

  /-- Pure-arithmetic carry-chain → BV-sum lemma. Given three u16-bounded input
  limbs, three u16-bounded output limbs, and `{0, 1}`-bounded low carry bits
  satisfying the `output = input + 4` carry-chain over the field, conclude the
  64-bit BV equation `U64w.toBV #v[output, 0#16] = U64w.toBV #v[input, 0#16] +
  4#64` (the limbs coerce from FKB to BitVec 16 via the global `Coe` instance;
  the top u16 of each side is `0#16`, so the equation is faithful precisely
  under the u16 bounds passed in). No chip dependencies — takes carry booleans
  as hypotheses so it can sit above `is_real_active_constraints`. -/
  lemma carry_chain_plus_four_implies_sum
    (input_0 input_1 input_2 output_0 output_1 output_2
       carry_0 carry_1 carry_2 carry_3 : FKB)
    (h_in_0  : input_0.val  < 65536)
    (h_in_1  : input_1.val  < 65536)
    (h_in_2  : input_2.val  < 65536)
    (h_out_0 : output_0.val < 65536)
    (h_out_1 : output_1.val < 65536)
    (h_out_2 : output_2.val < 65536)
    (h_cb_0  : carry_0 = 0 ∨ carry_0 = 1)
    (h_cb_1  : carry_1 = 0 ∨ carry_1 = 1)
    (h_chain :
      input_0 + 4 = output_0 + carry_0 * 65536 ∧
      carry_0 + input_1 = output_1 + carry_1 * 65536 ∧
      carry_1 + input_2 = output_2 + carry_2 * 65536 ∧
      carry_2 = carry_3 * 65536 ∧
      carry_3 = 0)
  :
    U64w.toBV #v[output_0, output_1, output_2, 0#16] =
      U64w.toBV #v[input_0, input_1, input_2, 0#16] + 4#64
  := by
    simp [← BitVec.toNat_inj, U64w.toNat]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    grind

  /-- Specialised carry-chain → sum for the same-row `pc + 4 = next_pc` chain
  (the `pc_carry_b_*` family). Takes carry booleans as explicit hypotheses so it
  sits above `is_real_active_constraints`; u16 bounds come from `bus_row_wf_asm`. -/
  lemma next_pc_eq_pc_plus_four_of_pc_carry_b_chain
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_cb_0 : air.cols.pc_carry_b_0 row 0 = 0 ∨ air.cols.pc_carry_b_0 row 0 = 1)
    (h_cb_1 : air.cols.pc_carry_b_1 row 0 = 0 ∨ air.cols.pc_carry_b_1 row 0 = 1)
    (h_chain :
      air.cols.pc_0 row 0 + 4 =
        air.cols.next_pc_0 row 0 + air.cols.pc_carry_b_0 row 0 * 65536 ∧
      air.cols.pc_carry_b_0 row 0 + air.cols.pc_1 row 0 =
        air.cols.next_pc_1 row 0 + air.cols.pc_carry_b_1 row 0 * 65536 ∧
      air.cols.pc_carry_b_1 row 0 + air.cols.pc_2 row 0 =
        air.cols.next_pc_2 row 0 + air.cols.pc_carry_b_2 row 0 * 65536 ∧
      air.cols.pc_carry_b_2 row 0 = air.cols.pc_carry_b_3 row 0 * 65536 ∧
      air.cols.pc_carry_b_3 row 0 = 0)
  :
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64
  := by
    -- u16 bounds on pc_0..2 and next_pc_0..2 are the second through seventh
    -- entries of `raw_bus_row` (each a Byte-bus u16 range check at multiplicity
    -- `+is_real`). Unfold `bus_row_wf_asm` over `bus_row`, substitute `is_real
    -- = 1`, and read off the `ByteBus.Spec _ 8 _ _ _ _` conjuncts.
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real,
          ByteBus.Spec] at h_wf
    simp only [next_pc, pc]
    apply carry_chain_plus_four_implies_sum
      (air.cols.pc_0 row 0) (air.cols.pc_1 row 0) (air.cols.pc_2 row 0)
      (air.cols.next_pc_0 row 0) (air.cols.next_pc_1 row 0) (air.cols.next_pc_2 row 0)
      (air.cols.pc_carry_b_0 row 0) (air.cols.pc_carry_b_1 row 0)
      (air.cols.pc_carry_b_2 row 0) (air.cols.pc_carry_b_3 row 0)
      (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
      h_cb_0 h_cb_1 h_chain

  /-- Specialised carry-chain → sum for the JAL/JALR `op_a = pc + 4` chain (the
  `pc_carry_a_*` family with op_a value as output, 3 effective limbs after
  `value_3 = 0`). Takes the same 5-equation chain as
  `next_pc_eq_pc_plus_four_of_pc_carry_b_chain` (callers collapse the chip's
  6-equation form via `value_3 = 0` from c70 before applying). Op_a value limbs
  are on the State-bus **producer** side of the row, so `value_0..2 < 2^16` comes
  from `bus_row_wf_asrt`, not `bus_row_wf_asm`. pc bounds come from `h_wf`. -/
  lemma op_a_eq_pc_plus_four_of_pc_carry_a_chain
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_wf_asrt : bus_row_wf_asrt (bus_row air row))
    (h_ca_0 : air.cols.pc_carry_a_0 row 0 = 0 ∨ air.cols.pc_carry_a_0 row 0 = 1)
    (h_ca_1 : air.cols.pc_carry_a_1 row 0 = 0 ∨ air.cols.pc_carry_a_1 row 0 = 1)
    (h_chain :
      air.cols.pc_0 row 0 + 4 =
        air.cols.op_a_access.access.value_0 row 0 + air.cols.pc_carry_a_0 row 0 * 65536 ∧
      air.cols.pc_carry_a_0 row 0 + air.cols.pc_1 row 0 =
        air.cols.op_a_access.access.value_1 row 0 + air.cols.pc_carry_a_1 row 0 * 65536 ∧
      air.cols.pc_carry_a_1 row 0 + air.cols.pc_2 row 0 =
        air.cols.op_a_access.access.value_2 row 0 + air.cols.pc_carry_a_2 row 0 * 65536 ∧
      air.cols.pc_carry_a_2 row 0 = air.cols.pc_carry_a_3 row 0 * 65536 ∧
      air.cols.pc_carry_a_3 row 0 = 0)
  :
    U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  0#16 ] =
      U64w.toBV (pc air row) + 4#64
  := by
    -- pc_0..2 < 2^16 from h_wf (Byte-bus consumer entries)
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real,
          ByteBus.Spec] at h_wf
    -- op_a value_0..3 < 2^16 from h_wf_asrt (State-bus producer entry, mult = -is_real = -1)
    simp [bus_row_wf_asrt, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf_asrt
    simp only [pc]
    apply carry_chain_plus_four_implies_sum
      (air.cols.pc_0 row 0) (air.cols.pc_1 row 0) (air.cols.pc_2 row 0)
      (air.cols.op_a_access.access.value_0 row 0)
      (air.cols.op_a_access.access.value_1 row 0)
      (air.cols.op_a_access.access.value_2 row 0)
      (air.cols.pc_carry_a_0 row 0) (air.cols.pc_carry_a_1 row 0)
      (air.cols.pc_carry_a_2 row 0) (air.cols.pc_carry_a_3 row 0)
      (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
      h_ca_0 h_ca_1 h_chain

  /-- Specialised carry-chain → sum for the **cross-row** `pc + 4 = pc(row+1)`
  chain (the `pc_carry_a_*` family in `is_sequential_active_constraints`).
  The output limbs `pc_i row 1` are bridged to `pc_i (row + 1) 0` via the
  rotation lemmas (`pc_0_rotation`, `pc_1_rotation`, `pc_2_rotation`), so we
  can read their u16 bounds off `h_wf_next` (= `bus_row_wf_asm (bus_row air
  (row + 1))`). Requires `row + 1 ≤ air.last_row` so the modular rotation
  collapses to a plain addition. -/
  lemma pc_next_row_eq_pc_plus_four_of_pc_carry_a_chain
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row_next : row + 1 ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real_next : air.cols.is_real row 1 = 1)
    (h_wf_next : bus_row_wf_asm (bus_row air (row + 1)))
    (h_ca_0 : air.cols.pc_carry_a_0 row 0 = 0 ∨ air.cols.pc_carry_a_0 row 0 = 1)
    (h_ca_1 : air.cols.pc_carry_a_1 row 0 = 0 ∨ air.cols.pc_carry_a_1 row 0 = 1)
    (h_chain :
      air.cols.pc_0 row 0 + 4 =
        air.cols.pc_0 row 1 + air.cols.pc_carry_a_0 row 0 * 65536 ∧
      air.cols.pc_carry_a_0 row 0 + air.cols.pc_1 row 0 =
        air.cols.pc_1 row 1 + air.cols.pc_carry_a_1 row 0 * 65536 ∧
      air.cols.pc_carry_a_1 row 0 + air.cols.pc_2 row 0 =
        air.cols.pc_2 row 1 + air.cols.pc_carry_a_2 row 0 * 65536 ∧
      air.cols.pc_carry_a_2 row 0 = air.cols.pc_carry_a_3 row 0 * 65536 ∧
      air.cols.pc_carry_a_3 row 0 = 0)
  :
    U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ] =
      U64w.toBV (pc air row) + 4#64
  := by
    -- Current-row pc u16 bounds.
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real, ByteBus.Spec] at h_wf
    -- Next-row pc u16 bounds, exposed in `(row + 1) 0` form.
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, ByteBus.Spec] at h_wf_next
    -- Bridge: rewrite `h_wf_next`'s `pc_i (row + 1) 0` bounds into `pc_i row 1`
    -- form via rotation invariance (mod no-op under `row + 1 ≤ air.last_row`).
    have h_mod : (row + 1) % (air.last_row + 1) = row + 1 := Nat.mod_eq_of_lt (by omega)
    have h_pc_0_eq : air.cols.pc_0 (row + 1) 0 = air.cols.pc_0 row 1 := by
      (conv => rhs; rw [pc_0_rotation]); simp [h_mod]
    have h_pc_1_eq : air.cols.pc_1 (row + 1) 0 = air.cols.pc_1 row 1 := by
      (conv => rhs; rw [pc_1_rotation]); simp [h_mod]
    have h_pc_2_eq : air.cols.pc_2 (row + 1) 0 = air.cols.pc_2 row 1 := by
      (conv => rhs; rw [pc_2_rotation]); simp [h_mod]
    have h_is_real_eq : air.cols.is_real (row + 1) 0 = air.cols.is_real row 1 := by
      (conv => rhs; rw [is_real_rotation]); simp [h_mod]
    rw [h_pc_0_eq, h_pc_1_eq, h_pc_2_eq, h_is_real_eq] at h_wf_next
    simp only [pc]
    apply carry_chain_plus_four_implies_sum
      (air.cols.pc_0 row 0) (air.cols.pc_1 row 0) (air.cols.pc_2 row 0)
      (air.cols.pc_0 row 1) (air.cols.pc_1 row 1) (air.cols.pc_2 row 1)
      (air.cols.pc_carry_a_0 row 0) (air.cols.pc_carry_a_1 row 0)
      (air.cols.pc_carry_a_2 row 0) (air.cols.pc_carry_a_3 row 0)
      (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)
      h_ca_0 h_ca_1 h_chain

  -- ============================================================================
  -- Program-bus alignment: on every real row the PC is divisible by 4.
  -- `ProgramBus.axioms` asserts `multiplicity ≠ 0 → pc_0.val % 4 = 0`; the
  -- chip consumes the entry with multiplicity `+is_real`, so under `is_real = 1`
  -- the axiom fires. Since `pc.toNat % 4 = pc_0.val % 4`, the U48w-packed PC
  -- is 4-aligned too.
  -- ============================================================================

  /-- `is_real = 1` + Program-bus axioms ⟹ `pc.toNat % 4 = 0`. -/
  lemma pc_mod_four_eq_zero
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_axioms : bus_row_axioms (bus_row air row))
  :
    U64w.toNat (pc air row) % 4 = 0
  := by
    simp [bus_row_axioms, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_axioms
    simp [pc, U64w.toNat]
    grind

  /-- u16 bounds on each PC and next_pc limb on a real row. Thin wrapper over
  the trailing 6 conjuncts of `is_real_active_constraints` (Byte-bus u16
  range checks emitted with multiplicity `is_real`). -/
  lemma pc_next_pc_u16_bounds
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    (air.cols.pc_0 row 0).val < 65536 ∧
    (air.cols.pc_1 row 0).val < 65536 ∧
    (air.cols.pc_2 row 0).val < 65536 ∧
    (air.cols.next_pc_0 row 0).val < 65536 ∧
    (air.cols.next_pc_1 row 0).val < 65536 ∧
    (air.cols.next_pc_2 row 0).val < 65536
  := by
    have h_ra := is_real_active_constraints air row h_is_real (by grind) h_constraints
    grind

  -- ============================================================================
  -- Instruction-class dispatch: under `is_real = 1`, every row falls into one
  -- of five mutually exclusive classes — sequential, branch, JAL, JALR, or
  -- ECALL-halt. Mirrors RV32's `instruction_breakdown` (CpuAir.lean:3200).
  -- ============================================================================

  /-- Each opcode selector is a boolean (in `{0, 1}`), and the sum of the 23
  class selectors (excluding modifiers `imm_b, imm_c`) equals 1. Mirrors RV32's
  `opcode_selectors_breakdown` (CpuAir.lean:3013). Proof structure: unpack
  Program-bus `operand_properties` → invoke `inversion_opcode_bounds` and
  `inversion_opcode_selectors` directly → pull c8 + c12 (imm_b/imm_c boolean) →
  `interval_cases` on opcode. -/
  lemma opcode_selectors_breakdown
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    (air.cols.opcode_selector.imm_b row 0 = 0 ∨ air.cols.opcode_selector.imm_b row 0 = 1) ∧
    (air.cols.opcode_selector.imm_c row 0 = 0 ∨ air.cols.opcode_selector.imm_c row 0 = 1) ∧
    (air.cols.opcode_selector.is_alu row 0 = 0 ∨ air.cols.opcode_selector.is_alu row 0 = 1) ∧
    (air.cols.opcode_selector.is_ecall row 0 = 0 ∨ air.cols.opcode_selector.is_ecall row 0 = 1) ∧
    (air.cols.opcode_selector.is_lb row 0 = 0 ∨ air.cols.opcode_selector.is_lb row 0 = 1) ∧
    (air.cols.opcode_selector.is_lbu row 0 = 0 ∨ air.cols.opcode_selector.is_lbu row 0 = 1) ∧
    (air.cols.opcode_selector.is_lh row 0 = 0 ∨ air.cols.opcode_selector.is_lh row 0 = 1) ∧
    (air.cols.opcode_selector.is_lhu row 0 = 0 ∨ air.cols.opcode_selector.is_lhu row 0 = 1) ∧
    (air.cols.opcode_selector.is_lw row 0 = 0 ∨ air.cols.opcode_selector.is_lw row 0 = 1) ∧
    (air.cols.opcode_selector.is_lwu row 0 = 0 ∨ air.cols.opcode_selector.is_lwu row 0 = 1) ∧
    (air.cols.opcode_selector.is_ld row 0 = 0 ∨ air.cols.opcode_selector.is_ld row 0 = 1) ∧
    (air.cols.opcode_selector.is_sb row 0 = 0 ∨ air.cols.opcode_selector.is_sb row 0 = 1) ∧
    (air.cols.opcode_selector.is_sh row 0 = 0 ∨ air.cols.opcode_selector.is_sh row 0 = 1) ∧
    (air.cols.opcode_selector.is_sw row 0 = 0 ∨ air.cols.opcode_selector.is_sw row 0 = 1) ∧
    (air.cols.opcode_selector.is_sd row 0 = 0 ∨ air.cols.opcode_selector.is_sd row 0 = 1) ∧
    (air.cols.opcode_selector.is_beq row 0 = 0 ∨ air.cols.opcode_selector.is_beq row 0 = 1) ∧
    (air.cols.opcode_selector.is_bne row 0 = 0 ∨ air.cols.opcode_selector.is_bne row 0 = 1) ∧
    (air.cols.opcode_selector.is_blt row 0 = 0 ∨ air.cols.opcode_selector.is_blt row 0 = 1) ∧
    (air.cols.opcode_selector.is_bge row 0 = 0 ∨ air.cols.opcode_selector.is_bge row 0 = 1) ∧
    (air.cols.opcode_selector.is_bltu row 0 = 0 ∨ air.cols.opcode_selector.is_bltu row 0 = 1) ∧
    (air.cols.opcode_selector.is_bgeu row 0 = 0 ∨ air.cols.opcode_selector.is_bgeu row 0 = 1) ∧
    (air.cols.opcode_selector.is_jalr row 0 = 0 ∨ air.cols.opcode_selector.is_jalr row 0 = 1) ∧
    (air.cols.opcode_selector.is_jal row 0 = 0 ∨ air.cols.opcode_selector.is_jal row 0 = 1) ∧
    (air.cols.opcode_selector.is_auipc row 0 = 0 ∨ air.cols.opcode_selector.is_auipc row 0 = 1) ∧
    (air.cols.opcode_selector.is_unimpl row 0 = 0 ∨ air.cols.opcode_selector.is_unimpl row 0 = 1) ∧
    (air.cols.opcode_selector.is_alu row 0 + air.cols.opcode_selector.is_ecall row 0 +
       air.cols.opcode_selector.is_lb row 0 + air.cols.opcode_selector.is_lbu row 0 +
       air.cols.opcode_selector.is_lh row 0 + air.cols.opcode_selector.is_lhu row 0 +
       air.cols.opcode_selector.is_lw row 0 + air.cols.opcode_selector.is_lwu row 0 +
       air.cols.opcode_selector.is_ld row 0 +
       air.cols.opcode_selector.is_sb row 0 + air.cols.opcode_selector.is_sh row 0 +
       air.cols.opcode_selector.is_sw row 0 + air.cols.opcode_selector.is_sd row 0 +
       air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
       air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
       air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 +
       air.cols.opcode_selector.is_jalr row 0 + air.cols.opcode_selector.is_jal row 0 +
       air.cols.opcode_selector.is_auipc row 0 + air.cols.opcode_selector.is_unimpl row 0 = 1)
  := by
    have h_prog := program_bus_operand_properties air row h_is_real (by grind)
    obtain ⟨ instr, data, props, h_trans, h_deser, h_props ⟩ := h_prog
    have h_opcode_bounds := ProgramBusEntry.inversion_opcode_bounds h_trans h_deser
    have h_opcode_selectors := ProgramBusEntry.inversion_opcode_selectors h_trans h_deser
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_opcode_bounds h_opcode_selectors
    obtain ⟨ h_op_range, h_op_not_26, h_op_not_29, h_op_not_38, h_op_not_39 ⟩
      := h_opcode_bounds
    obtain ⟨ h_c8, h_c12 ⟩ : constraint_8 air row ∧ constraint_12 air row := by
      rw [allHold_iff_allHold_simplified] at h_constraints
      simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
      clear *- h_constraints; aesop
    simp [constraint_and_interaction_simplification, sub_eq_zero, mul_eq_zero]
      at h_c8 h_c12
    rw [or_comm, eq_comm (a := (1 : FKB))] at h_c8 h_c12
    simp [h_c8, h_c12]; clear h_c8 h_c12 h_deser h_trans
    have h_op_upper : (air.cols.instruction.opcode row 0).val ≤ 52 := by omega
    repeat rw [Fin.ext_iff (a := air.cols.instruction.opcode row 0)] at h_opcode_selectors
    interval_cases (air.cols.instruction.opcode row 0).val <;>
      simp at h_opcode_selectors <;>
      (try simp [h_opcode_selectors]) <;>
      (try exfalso; omega)

  /-- `is_real = 1` row dispatch: exactly one of the 5 classes is active.
  Mirrors RV32's `instruction_breakdown` (CpuAir.lean:3200), using c160
  (sequential characterisation) + c142 (ecall-halt boolean) +
  `opcode_selectors_breakdown`. -/
  lemma instruction_breakdown
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_sequential_instr row 0 = 1 ∨
    air.cols.opcode_selector.is_beq row 0 +
      air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 +
      air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 +
      air.cols.opcode_selector.is_bgeu row 0 = 1 ∨
    air.cols.opcode_selector.is_jal row 0 = 1 ∨
    air.cols.opcode_selector.is_jalr row 0 = 1 ∨
    (air.cols.opcode_selector.is_ecall row 0 = 1 ∧
     air.cols.opcode_specific.specific_9 row 0 = 1)
  := by
    have opcode_range := opcode_selectors_breakdown air row h_is_real (by grind) h_constraints
    have to_lt : ∀ (x : FKB), x = 0 ∨ x = 1 ↔ x < 2 := by clear *-; omega
    simp [to_lt] at opcode_range
    have ⟨ h_c160, h_c142 ⟩ : constraint_160 air row ∧ constraint_142 air row := by
      rw [allHold_iff_allHold_simplified] at h_constraints
      simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
      clear *- h_constraints; aesop
    simp [
      pico_encapsulation,
      constraint_and_interaction_simplification,
      sub_eq_zero,
      *
    ] at h_c160 h_c142
    rw [h_c160]
    grind

  -- ============================================================================
  -- Same-row next_pc value: bus-derived `next_pc = pc + op_*` form for the
  -- branching / JAL / JALR ALU lookups. The CPU chip consumes an ALU ADD
  -- entry for each (raw_bus_row lines 2330 / 2333 / 2335), so
  -- `bus_row_wf_asm` exposes the `ALUBus.Spec` ADD assertion, which after
  -- unfolding `execute_RTYPE_pure .ADD` is plain BV addition.
  -- ============================================================================

  /-- Characterisation of `branching = 1` under `is_real = 1`. Forces:
    * (c57) one of the 6 branch selectors (`is_beq, is_bne, is_blt, is_bge,
      is_bltu, is_bgeu`) is active;
    * (c42) `not_branching = 0`;
    * (c24-c27) op_a value = prev value (no register write on branches);
    * (c28-c30) on transition rows with `is_real (row+1) = 1`, `next_pc = pc(row+1)`
      as a U48w sum (the branch target is installed at the next row's pc). -/
  lemma branching_eq_one_characterisation
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_branching : air.cols.branching row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- (c57) one of the 6 branch selectors is active
    air.cols.opcode_selector.is_beq row 0 +
      air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 +
      air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 +
      air.cols.opcode_selector.is_bgeu row 0 = 1 ∧
    -- (c42) not_branching = 0
    air.cols.not_branching row 0 = 0 ∧
    -- (selector_exclusivity at opcode ∈ {18..23}) imm_c = 1 (op_c is the branch offset)
    air.cols.opcode_selector.imm_c row 0 = 1 ∧
    -- (c24-c27) op_a value = prev value
    air.cols.op_a_access.access.value_0 row 0 = air.cols.op_a_access.prev_value_0 row 0 ∧
    air.cols.op_a_access.access.value_1 row 0 = air.cols.op_a_access.prev_value_1 row 0 ∧
    air.cols.op_a_access.access.value_2 row 0 = air.cols.op_a_access.prev_value_2 row 0 ∧
    air.cols.op_a_access.access.value_3 row 0 = air.cols.op_a_access.prev_value_3 row 0 ∧
    -- (c28-c30) cross-row branch target propagation as a U48w sum
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV (next_pc air row) =
        U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ])
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c24, h_c25, h_c26, h_c27, h_c28, h_c29, h_c30, h_c42, h_c57 ⟩
    : constraint_24 air row ∧ constraint_25 air row ∧
      constraint_26 air row ∧ constraint_27 air row ∧
      constraint_28 air row ∧ constraint_29 air row ∧ constraint_30 air row ∧
      constraint_42 air row ∧ constraint_57 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    -- c57 + h_branching ⟹ branch_sum = 1; then c42 ⟹ not_branching = 0.
    simp [constraint_and_interaction_simplification, h_branching, sub_eq_zero, mul_eq_zero]
      at h_c42 h_c57
    have h_branch_sum :
      air.cols.opcode_selector.is_beq row 0 +
        air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 +
        air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 +
        air.cols.opcode_selector.is_bgeu row 0 = 1 := h_c57
    have h_not_branching : air.cols.not_branching row 0 = 0 := by
      rcases h_c42 with h | h
      . exfalso; rw [h] at h_branch_sum; exact absurd h_branch_sum (by decide)
      . exact h
    -- c24-c27 simplify under (branch_sum = 1) and (store_sum = 0).
    have h_opcode := (is_branch_sum_eq_one_iff air row h_is_real (by grind)).mp h_branch_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have h_no_store_sum :
      air.cols.opcode_selector.is_sb row 0 +
        air.cols.opcode_selector.is_sh row 0 +
        air.cols.opcode_selector.is_sw row 0 +
        air.cols.opcode_selector.is_sd row 0 = 0 := by grind (splits := 64)
    have h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1 := by grind (splits := 64)
    simp [constraint_and_interaction_simplification, h_branch_sum, h_no_store_sum,
          one_mul, sub_eq_zero]
      at h_c24 h_c25 h_c26 h_c27
    refine ⟨h_branch_sum, h_not_branching, h_imm_c, h_c24, h_c25, h_c26, h_c27, ?_⟩
    -- c28-c30 under h_branching + transition + real_next give next_pc_i = pc_i@1.
    intro h_trans h_real_next
    simp [constraint_and_interaction_simplification, h_branching, h_trans, h_real_next,
          sub_eq_zero] at h_c28 h_c29 h_c30
    simp only [next_pc]
    grind

  /-- `branching = 1` → the ALU ADD lookup emitted by the chip
  (raw_bus_row line 2330, mult = `-branching`) gives
  `[next_pc_0, next_pc_1, next_pc_2, 0] = [pc_0, pc_1, pc_2, 0] + op_c` as a
  48-bit BV addition. -/
  lemma branching_next_pc_eq_pc_plus_op_c
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_branching : air.cols.branching row 0 = 1)
  :
    U64w.toBV (next_pc air row) =
      U64w.toBV (pc air row) +
      U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                    air.cols.op_c_access.access.value_1 row 0,
                    air.cols.op_c_access.access.value_2 row 0,
                    air.cols.op_c_access.access.value_3 row 0 ]
  := by
    simp only [next_pc, pc]
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_branching, h_is_real] at h_wf
    replace h_wf := h_wf.2.2.1; simp [ALUBus.Spec, RV64IM.execute_RTYPE_pure] at h_wf
    exact h_wf.2

  /-- `is_jal = 1` → the ALU ADD lookup emitted by the chip
  (raw_bus_row line 2333, mult = `-is_jal`) gives
  `[next_pc_0, next_pc_1, next_pc_2, 0] = [pc_0, pc_1, pc_2, 0] + op_b` as a
  64-bit BV addition. -/
  lemma jal_next_pc_eq_pc_plus_op_b
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_jal : air.cols.opcode_selector.is_jal row 0 = 1)
  :
    U64w.toBV (next_pc air row) =
      U64w.toBV (pc air row) +
      U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                    air.cols.op_b_access.access.value_1 row 0,
                    air.cols.op_b_access.access.value_2 row 0,
                    air.cols.op_b_access.access.value_3 row 0 ]
  := by
    simp only [next_pc, pc]
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_jal, h_is_real] at h_wf
    replace h_wf := h_wf.2.2.2.2.2.1; simp [ALUBus.Spec, RV64IM.execute_RTYPE_pure] at h_wf
    exact h_wf.2

  /-- `is_jalr = 1` → the ALU ADD lookup emitted by the chip
  (raw_bus_row line 2335, mult = `-is_jalr`) gives
  `[next_pc_0 + specific_0, next_pc_1, next_pc_2, 0] = op_b + op_c` as a
  64-bit BV addition. The `+ specific_0` term reflects the JALR low-bit
  clear: `specific_0` is the displaced low bit (parity-checked separately
  by the byte-bus u16 lookup on `next_pc_0 * 1065353217 = next_pc_0 / 2`,
  raw_bus_row line 2334). -/
  lemma jalr_next_pc_plus_specific_eq_op_b_plus_op_c
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_jalr : air.cols.opcode_selector.is_jalr row 0 = 1)
  :
    U64w.toBV #v[ ((air.cols.next_pc_0 row 0 + air.cols.opcode_specific.specific_0 row 0
                    : FKB) : BitVec 16),
                  air.cols.next_pc_1 row 0,
                  air.cols.next_pc_2 row 0,
                  0#16 ] =
      U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                    air.cols.op_b_access.access.value_1 row 0,
                    air.cols.op_b_access.access.value_2 row 0,
                    air.cols.op_b_access.access.value_3 row 0 ] +
      U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                    air.cols.op_c_access.access.value_1 row 0,
                    air.cols.op_c_access.access.value_2 row 0,
                    air.cols.op_c_access.access.value_3 row 0 ]
  := by
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_jalr, h_is_real] at h_wf
    replace h_wf := h_wf.2.2.2.2.2.2.1; simp [ALUBus.Spec, RV64IM.execute_RTYPE_pure] at h_wf
    exact h_wf.2

  /-- `is_auipc = 1` → the ALU ADD lookup emitted by the chip
  (raw_bus_row line 2336, mult = `-is_auipc`) gives
  `op_a = [pc_0, pc_1, pc_2, 0] + op_b` as a 64-bit BV addition. -/
  lemma auipc_op_a_eq_pc_plus_op_b
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_auipc : air.cols.opcode_selector.is_auipc row 0 = 1)
  :
    U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
      U64w.toBV (pc air row) +
      U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                    air.cols.op_b_access.access.value_1 row 0,
                    air.cols.op_b_access.access.value_2 row 0,
                    air.cols.op_b_access.access.value_3 row 0 ]
  := by
    simp only [pc]
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_auipc, h_is_real] at h_wf
    replace h_wf := h_wf.2.2.2.2.2.2.2.1; simp [ALUBus.Spec, RV64IM.execute_RTYPE_pure] at h_wf
    exact h_wf.2

  -- ============================================================================
  -- Layer 1: operand-immediate validation (imm_b / imm_c)
  -- ============================================================================

  /-- `imm_b = 1`: operand b is the literal immediate. c0-c3 substitute to
  `op_b_access.access.value_i = instruction.op_b_i`. -/
  lemma imm_b_eq_1_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.op_b_access.access.value_0 row 0 = air.cols.instruction.op_b_0 row 0 ∧
    air.cols.op_b_access.access.value_1 row 0 = air.cols.instruction.op_b_1 row 0 ∧
    air.cols.op_b_access.access.value_2 row 0 = air.cols.instruction.op_b_2 row 0 ∧
    air.cols.op_b_access.access.value_3 row 0 = air.cols.instruction.op_b_3 row 0
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c0, h_c1, h_c2, h_c3 ⟩
    : constraint_0 air row ∧ constraint_1 air row ∧
      constraint_2 air row ∧ constraint_3 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_imm_b, one_mul, sub_eq_zero]
      at h_c0 h_c1 h_c2 h_c3
    exact ⟨h_c0, h_c1, h_c2, h_c3⟩

  /-- `imm_b = 0`: operand b comes from a register access. c9-c11 give the
  op_b memory-access bookkeeping (compare_clk boolean, chunk continuity,
  clock-difference range-check decomposition into 16+8-bit limbs). The op_b
  access happens at `clk + 2`. -/
  lemma imm_b_eq_0_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- (c9) compare_clk boolean
    (air.cols.op_b_access.access.compare_clk row 0 = 0 ∨
     air.cols.op_b_access.access.compare_clk row 0 = 1) ∧
    -- (c10 + c11, compare_clk = 1) same-chunk case: chunk stays, clk advances by (diff + 1)
    (air.cols.op_b_access.access.compare_clk row 0 = 1 →
      air.cols.chunk row 0 = air.cols.op_b_access.access.prev_chunk row 0 ∧
      air.cols.op_b_access.access.diff_16bit_limb row 0 +
        air.cols.op_b_access.access.diff_8bit_limb row 0 * 65536 +
        air.cols.op_b_access.access.prev_clk row 0 + 1 =
        air.cols.clk row 0 + 2) ∧
    -- (c11, compare_clk = 0) new-chunk case: chunk advances by (diff + 1)
    (air.cols.op_b_access.access.compare_clk row 0 = 0 →
      air.cols.op_b_access.access.diff_16bit_limb row 0 +
        air.cols.op_b_access.access.diff_8bit_limb row 0 * 65536 +
        air.cols.op_b_access.access.prev_chunk row 0 + 1 =
        air.cols.chunk row 0)
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c9, h_c10, h_c11 ⟩
    : constraint_9 air row ∧ constraint_10 air row ∧ constraint_11 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_imm_b, one_mul, sub_eq_zero]
      at h_c9 h_c10 h_c11
    simp [*]
    grind

  /-- `imm_c = 1`: operand c is the literal immediate. c4-c7 substitute to
  `op_c_access.access.value_i = instruction.op_c_i`. -/
  lemma imm_c_eq_1_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.op_c_access.access.value_0 row 0 = air.cols.instruction.op_c_0 row 0 ∧
    air.cols.op_c_access.access.value_1 row 0 = air.cols.instruction.op_c_1 row 0 ∧
    air.cols.op_c_access.access.value_2 row 0 = air.cols.instruction.op_c_2 row 0 ∧
    air.cols.op_c_access.access.value_3 row 0 = air.cols.instruction.op_c_3 row 0
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c4, h_c5, h_c6, h_c7 ⟩
    : constraint_4 air row ∧ constraint_5 air row ∧
      constraint_6 air row ∧ constraint_7 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_imm_c, one_mul, sub_eq_zero]
      at h_c4 h_c5 h_c6 h_c7
    exact ⟨h_c4, h_c5, h_c6, h_c7⟩

  /-- `imm_c = 0`: operand c comes from a register access. c13-c15 give the
  op_c memory-access bookkeeping. The op_c access happens at `clk + 1`. -/
  lemma imm_c_eq_0_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- (c13) compare_clk boolean
    (air.cols.op_c_access.access.compare_clk row 0 = 0 ∨
     air.cols.op_c_access.access.compare_clk row 0 = 1) ∧
    -- (c14 + c15, compare_clk = 1) same-chunk case
    (air.cols.op_c_access.access.compare_clk row 0 = 1 →
      air.cols.chunk row 0 = air.cols.op_c_access.access.prev_chunk row 0 ∧
      air.cols.op_c_access.access.diff_16bit_limb row 0 +
        air.cols.op_c_access.access.diff_8bit_limb row 0 * 65536 +
        air.cols.op_c_access.access.prev_clk row 0 + 1 =
        air.cols.clk row 0 + 1) ∧
    -- (c15, compare_clk = 0) new-chunk case
    (air.cols.op_c_access.access.compare_clk row 0 = 0 →
      air.cols.op_c_access.access.diff_16bit_limb row 0 +
        air.cols.op_c_access.access.diff_8bit_limb row 0 * 65536 +
        air.cols.op_c_access.access.prev_chunk row 0 + 1 =
        air.cols.chunk row 0)
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c13, h_c14, h_c15 ⟩
    : constraint_13 air row ∧ constraint_14 air row ∧ constraint_15 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_imm_c, one_mul, sub_eq_zero]
      at h_c13 h_c14 h_c15
    simp [*]
    grind

  -- ============================================================================
  -- Layer 2: per-opcode-class active constraints
  -- ============================================================================

  /-- `is_jal = 1`: JAL row. `is_jalr = 0` is derived from `is_jal = 1` via the
  inversion lemmas (`is_jal = 1 → opcode = 24`, then `selector_exclusivity` at
  `opcode = 24` gives `is_jalr = 0`).
    * (c58-c63 + c70) when `op_a_is_x0 = 0`, op_a = PC + 4 (sum form, with
      `value_3 = 0` from c70 collapsing the 6-equation chain to the 5-equation
      shape consumed by `op_a_eq_pc_plus_four_of_pc_carry_a_chain`).
    * (c70) value_3 = 0 (top u16 limb of op_a fits in 0 since PC + 4 < 2^48).
    * (c67-c69) on a transition row with `is_real (row+1) = 1`,
      `next_pc_i = pc_i (row+1)` (jump target gets installed). -/
  lemma is_jal_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
    (h_is_jal : air.cols.opcode_selector.is_jal row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- PC + 4 → op_a sum form, gated on `op_a_is_x0 = 0`
    (air.cols.instruction.op_a_is_x0 row 0 = 0 →
      U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                    air.cols.op_a_access.access.value_1 row 0,
                    air.cols.op_a_access.access.value_2 row 0,
                    0#16 ] =
        U64w.toBV (pc air row) + 4#64) ∧
    -- (c70) `(is_jal + is_jalr) * value_3 = 0` → value_3 = 0
    air.cols.op_a_access.access.value_3 row 0 = 0 ∧
    -- (c67-c69) on transition rows with the next row real, next_pc gets carried over
    -- as a U48w sum: `next_pc row = pc (row+1)` (the jump target was installed).
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV (next_pc air row) =
        U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ])
  := by
    have h_opcode : (air.cols.instruction.opcode row 0).val = 24 :=
      (is_jal_eq_one_iff air row h_is_real (by grind)).mp h_is_jal
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have h_is_jalr : air.cols.opcode_selector.is_jalr row 0 = 0 := by grind
    -- Carry-bit booleans for pc_carry_a_0/1 come from `is_real_active_constraints`.
    have h_ra := is_real_active_constraints air row h_is_real (by grind) h_constraints
    obtain ⟨_, _, _, _, _, _, _, _, h_ca_0, h_ca_1, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h_ra
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c58, h_c59, h_c60, h_c61, h_c62, h_c63,
             h_c67, h_c68, h_c69, h_c70 ⟩
    : constraint_58 air row ∧ constraint_59 air row ∧ constraint_60 air row ∧
      constraint_61 air row ∧ constraint_62 air row ∧ constraint_63 air row ∧
      constraint_67 air row ∧ constraint_68 air row ∧ constraint_69 air row ∧
      constraint_70 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_is_jal, h_is_jalr,
          one_mul, sub_eq_zero, mul_eq_zero]
      at h_c58 h_c59 h_c60 h_c61 h_c62 h_c63 h_c67 h_c68 h_c69 h_c70
    refine ⟨?_, h_c70, ?_⟩
    . intro h_x0
      simp [h_x0] at h_c58 h_c59 h_c60 h_c61 h_c62 h_c63
      -- Build the 5-equation chain from the 6-equation form + c70 (value_3 = 0)
      have h_chain :
        air.cols.pc_0 row 0 + 4 =
          air.cols.op_a_access.access.value_0 row 0 + air.cols.pc_carry_a_0 row 0 * 65536 ∧
        air.cols.pc_carry_a_0 row 0 + air.cols.pc_1 row 0 =
          air.cols.op_a_access.access.value_1 row 0 + air.cols.pc_carry_a_1 row 0 * 65536 ∧
        air.cols.pc_carry_a_1 row 0 + air.cols.pc_2 row 0 =
          air.cols.op_a_access.access.value_2 row 0 + air.cols.pc_carry_a_2 row 0 * 65536 ∧
        air.cols.pc_carry_a_2 row 0 = air.cols.pc_carry_a_3 row 0 * 65536 ∧
        air.cols.pc_carry_a_3 row 0 = 0 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind
      exact op_a_eq_pc_plus_four_of_pc_carry_a_chain air row h_is_real (by grind) (by grind)
        h_ca_0 h_ca_1 h_chain
    . intro h_trans h_real_next
      simp [h_trans, h_real_next] at h_c67 h_c68 h_c69
      simp only [next_pc]
      grind

  /-- `is_jalr = 1`: JALR row. `is_jal = 0` is derived via the inversion lemmas.
    * (c58-c63) when `op_a_is_x0 = 0`, op_a = PC + 4 carry chain (same as JAL).
    * (c70) value_3 = 0.
    * (c67-c69) on a transition row with `is_real (row+1) = 1`, next_pc gets carried.
    * (c71) `specific_0` is boolean (JALR's "low bit cleared" flag witness). -/
  lemma is_jalr_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
    (h_is_jalr : air.cols.opcode_selector.is_jalr row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- PC + 4 → op_a sum form, gated on `op_a_is_x0 = 0` (c58-c63 + c70)
    (air.cols.instruction.op_a_is_x0 row 0 = 0 →
      U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                    air.cols.op_a_access.access.value_1 row 0,
                    air.cols.op_a_access.access.value_2 row 0,
                    0#16 ] =
        U64w.toBV (pc air row) + 4#64) ∧
    -- (c70) value_3 = 0
    air.cols.op_a_access.access.value_3 row 0 = 0 ∧
    -- (c67-c69) next_pc carried over on transition + real next (U48w sum form)
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV (next_pc air row) =
        U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ]) ∧
    -- (c71) JALR-specific `specific_0` ∈ {0, 1}
    (air.cols.opcode_specific.specific_0 row 0 = 0 ∨
     air.cols.opcode_specific.specific_0 row 0 = 1)
  := by
    have h_opcode : (air.cols.instruction.opcode row 0).val = 25 :=
      (is_jalr_eq_one_iff air row h_is_real (by grind)).mp h_is_jalr
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have h_is_jal : air.cols.opcode_selector.is_jal row 0 = 0 := by grind
    -- Carry-bit booleans for pc_carry_a_0/1 come from `is_real_active_constraints`.
    have h_ra := is_real_active_constraints air row h_is_real (by grind) h_constraints
    obtain ⟨_, _, _, _, _, _, _, _, h_ca_0, h_ca_1, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h_ra
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c58, h_c59, h_c60, h_c61, h_c62, h_c63,
             h_c67, h_c68, h_c69, h_c70, h_c71 ⟩
    : constraint_58 air row ∧ constraint_59 air row ∧ constraint_60 air row ∧
      constraint_61 air row ∧ constraint_62 air row ∧ constraint_63 air row ∧
      constraint_67 air row ∧ constraint_68 air row ∧ constraint_69 air row ∧
      constraint_70 air row ∧ constraint_71 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_is_jal, h_is_jalr,
          one_mul, sub_eq_zero, mul_eq_zero]
      at h_c58 h_c59 h_c60 h_c61 h_c62 h_c63 h_c67 h_c68 h_c69 h_c70 h_c71
    refine ⟨?_, h_c70, ?_, ?_⟩
    . intro h_x0
      simp [h_x0] at h_c58 h_c59 h_c60 h_c61 h_c62 h_c63
      have h_chain :
        air.cols.pc_0 row 0 + 4 =
          air.cols.op_a_access.access.value_0 row 0 + air.cols.pc_carry_a_0 row 0 * 65536 ∧
        air.cols.pc_carry_a_0 row 0 + air.cols.pc_1 row 0 =
          air.cols.op_a_access.access.value_1 row 0 + air.cols.pc_carry_a_1 row 0 * 65536 ∧
        air.cols.pc_carry_a_1 row 0 + air.cols.pc_2 row 0 =
          air.cols.op_a_access.access.value_2 row 0 + air.cols.pc_carry_a_2 row 0 * 65536 ∧
        air.cols.pc_carry_a_2 row 0 = air.cols.pc_carry_a_3 row 0 * 65536 ∧
        air.cols.pc_carry_a_3 row 0 = 0 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind
      exact op_a_eq_pc_plus_four_of_pc_carry_a_chain air row h_is_real (by grind) (by grind)
        h_ca_0 h_ca_1 h_chain
    . intro h_trans h_real_next
      simp [h_trans, h_real_next] at h_c67 h_c68 h_c69
      simp only [next_pc]
      grind
    . grind

  /-- Branch row: exactly one of `is_beq / is_bne / is_blt / is_bge / is_bltu / is_bgeu` is 1
  and no store selector is 1. Produces the chip-level branch invariants:
    * (c24-c27) `op_a` value = prev value (no register write on branches);
    * (c42-c44) `branching, not_branching ∈ {0, 1}` and `branching + not_branching = 1`;
    * (c28-c30) when `branching = 1` on a transition row with the next row real,
      `next_pc_i = pc_i (row+1)` (branch target is installed);
    * (c37-c41) when `not_branching = 1`, `next_pc = pc + 4` (carry form).
  Per-branch witness equations (c45-c56 picking the right `specific_*` flag) are
  left for downstream per-opcode lemmas. -/
  lemma is_branching_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_branch_sum : air.cols.opcode_selector.is_beq row 0 +
                    air.cols.opcode_selector.is_bne row 0 +
                    air.cols.opcode_selector.is_blt row 0 +
                    air.cols.opcode_selector.is_bge row 0 +
                    air.cols.opcode_selector.is_bltu row 0 +
                    air.cols.opcode_selector.is_bgeu row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    -- (c24-c27) op_a value = prev value
    air.cols.op_a_access.access.value_0 row 0 = air.cols.op_a_access.prev_value_0 row 0 ∧
    air.cols.op_a_access.access.value_1 row 0 = air.cols.op_a_access.prev_value_1 row 0 ∧
    air.cols.op_a_access.access.value_2 row 0 = air.cols.op_a_access.prev_value_2 row 0 ∧
    air.cols.op_a_access.access.value_3 row 0 = air.cols.op_a_access.prev_value_3 row 0 ∧
    -- (c42-c44) branching / not_branching booleans + mutex
    (air.cols.branching row 0 = 0 ∨ air.cols.branching row 0 = 1) ∧
    (air.cols.not_branching row 0 = 0 ∨ air.cols.not_branching row 0 = 1) ∧
    air.cols.branching row 0 + air.cols.not_branching row 0 = 1 ∧
    -- (c28-c30) branching = 1 + transition row + real next row → next_pc = pc (row+1)
    -- as a U48w sum (the branch target is installed at the next row's pc).
    (air.cols.branching row 0 = 1 →
      Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV (next_pc air row) =
        U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ]) ∧
    -- not_branching = 1 → same-row sum form: `next_pc = pc + 4`
    (air.cols.not_branching row 0 = 1 →
      U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64)
  := by
    have h_opcode := (is_branch_sum_eq_one_iff air row h_is_real (by grind)).mp h_branch_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have h_no_store_sum :
      air.cols.opcode_selector.is_sb row 0 +
        air.cols.opcode_selector.is_sh row 0 +
        air.cols.opcode_selector.is_sw row 0 +
        air.cols.opcode_selector.is_sd row 0 = 0 := by grind (splits := 64)
    -- Pull carry-bit booleans for the pc_carry_b chain.
    have h_ra := is_real_active_constraints air row h_is_real (by grind) h_constraints
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
            h_cb_b0, h_cb_b1, _, _, _, _, _, _, _, _⟩ := h_ra
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c24, h_c25, h_c26, h_c27,
             h_c28, h_c29, h_c30,
             h_c37, h_c38, h_c39, h_c40, h_c41,
             h_c42, h_c43, h_c44 ⟩
    : constraint_24 air row ∧ constraint_25 air row ∧
      constraint_26 air row ∧ constraint_27 air row ∧
      constraint_28 air row ∧ constraint_29 air row ∧ constraint_30 air row ∧
      constraint_37 air row ∧ constraint_38 air row ∧ constraint_39 air row ∧
      constraint_40 air row ∧ constraint_41 air row ∧
      constraint_42 air row ∧ constraint_43 air row ∧ constraint_44 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_is_real, h_branch_sum, h_no_store_sum,
          one_mul, zero_add, sub_eq_zero, mul_eq_zero]
      at h_c24 h_c25 h_c26 h_c27 h_c28 h_c29 h_c30
         h_c37 h_c38 h_c39 h_c40 h_c41 h_c42 h_c43 h_c44
    refine ⟨h_c24, h_c25, h_c26, h_c27, ?_, ?_, ?_, ?_, ?_⟩
    . grind
    . grind
    . grind
    . intro h_branching h_trans h_real_next
      simp [h_branching, h_trans, h_real_next] at h_c28 h_c29 h_c30
      simp only [next_pc]
      grind
    . intro h_not_branching
      simp [h_not_branching] at h_c37 h_c38 h_c39 h_c40 h_c41
      have h_chain :
        air.cols.pc_0 row 0 + 4 =
          air.cols.next_pc_0 row 0 + air.cols.pc_carry_b_0 row 0 * 65536 ∧
        air.cols.pc_carry_b_0 row 0 + air.cols.pc_1 row 0 =
          air.cols.next_pc_1 row 0 + air.cols.pc_carry_b_1 row 0 * 65536 ∧
        air.cols.pc_carry_b_1 row 0 + air.cols.pc_2 row 0 =
          air.cols.next_pc_2 row 0 + air.cols.pc_carry_b_2 row 0 * 65536 ∧
        air.cols.pc_carry_b_2 row 0 = air.cols.pc_carry_b_3 row 0 * 65536 ∧
        air.cols.pc_carry_b_3 row 0 = 0 := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind
      apply next_pc_eq_pc_plus_four_of_pc_carry_b_chain
      all_goals grind

  /-- When `is_real = 1` and the row is non-branchy / non-jumpy / non-ecall-halt,
  PC advances by 4. Used by every non-branch, non-jump opcode class (ALU / load /
  store / AUIPC / non-halting ECALL). Derives `is_sequential_instr = 1` from c160
  internally (no separate helper needed — the no-branchy facts already come from
  the selector breakdown in the caller).

  Outputs:
    * `is_sequential_instr = 1` (from c160 + h_is_real + no-branchy hyps);
    * **Same-row sum form**: `U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64`
      (via `next_pc_eq_pc_plus_four_of_pc_carry_b_chain`);
    * (c161-c165) **Cross-row carry chain** (on transition rows with the next
      row real): `pc (row+1) = pc + 4` via `pc_carry_a_*`. Kept in carry-chain
      form — converting to a Nat sum needs a `pc_i (row + 1) 0 = pc_i row 1`
      rotation bridge from `air.isValid`, which isn't yet written for the
      RV64 chip. -/
  lemma is_sequential_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_no_branch_sum : air.cols.opcode_selector.is_beq row 0 +
                       air.cols.opcode_selector.is_bne row 0 +
                       air.cols.opcode_selector.is_blt row 0 +
                       air.cols.opcode_selector.is_bge row 0 +
                       air.cols.opcode_selector.is_bltu row 0 +
                       air.cols.opcode_selector.is_bgeu row 0 = 0)
    (h_no_jal : air.cols.opcode_selector.is_jal row 0 = 0)
    (h_no_jalr : air.cols.opcode_selector.is_jalr row 0 = 0)
    (h_no_ecall_halt :
      air.cols.opcode_specific.specific_9 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_sequential_instr row 0 = 1 ∧
    -- same-row sum form: `next_pc = pc + 4`
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64 ∧
    -- (c161-c165) cross-row sum form: `pc (row+1) = pc + 4` under transition+real_next
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ] =
        U64w.toBV (pc air row) + 4#64)
  := by
    -- Carry-bit booleans for the same-row chain (pc_carry_b_0/1) and cross-row
    -- chain (pc_carry_a_0/1) come from `is_real_active_constraints`. c160 →
    -- h_is_seq. c161-c170 → carry chains.
    have h_ra := is_real_active_constraints air row h_is_real (by grind) h_constraints
    obtain ⟨_, _, _, _, _, _, _, _, h_ca_0, h_ca_1, _, _, _,
            h_cb_b0, h_cb_b1, _, _, _, _, _, _, _, _⟩ := h_ra
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c160, h_c161, h_c162, h_c163, h_c164, h_c165,
             h_c166, h_c167, h_c168, h_c169, h_c170 ⟩
    : constraint_160 air row ∧
      constraint_161 air row ∧ constraint_162 air row ∧ constraint_163 air row ∧
      constraint_164 air row ∧ constraint_165 air row ∧
      constraint_166 air row ∧ constraint_167 air row ∧ constraint_168 air row ∧
      constraint_169 air row ∧ constraint_170 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_is_real, h_no_branch_sum,
          h_no_jal, h_no_jalr, h_no_ecall_halt, sub_eq_zero] at h_c160
    -- h_c160 is now `air.cols.is_sequential_instr row 0 = 1`.
    simp [constraint_and_interaction_simplification, h_is_real, h_c160,
          one_mul, sub_eq_zero]
      at h_c161 h_c162 h_c163 h_c164 h_c165 h_c166 h_c167 h_c168 h_c169 h_c170
    have h_chain_b :
      air.cols.pc_0 row 0 + 4 =
        air.cols.next_pc_0 row 0 + air.cols.pc_carry_b_0 row 0 * 65536 ∧
      air.cols.pc_carry_b_0 row 0 + air.cols.pc_1 row 0 =
        air.cols.next_pc_1 row 0 + air.cols.pc_carry_b_1 row 0 * 65536 ∧
      air.cols.pc_carry_b_1 row 0 + air.cols.pc_2 row 0 =
        air.cols.next_pc_2 row 0 + air.cols.pc_carry_b_2 row 0 * 65536 ∧
      air.cols.pc_carry_b_2 row 0 = air.cols.pc_carry_b_3 row 0 * 65536 ∧
      air.cols.pc_carry_b_3 row 0 = 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind
    have h_sum :=
      next_pc_eq_pc_plus_four_of_pc_carry_b_chain air row h_is_real (by grind)
        h_cb_b0 h_cb_b1 h_chain_b
    refine ⟨h_c160, h_sum, ?_⟩
    intro h_trans h_real_next
    simp [h_trans, h_real_next] at h_c161 h_c162 h_c163 h_c164 h_c165
    have h_chain_a :
      air.cols.pc_0 row 0 + 4 =
        air.cols.pc_0 row 1 + air.cols.pc_carry_a_0 row 0 * 65536 ∧
      air.cols.pc_carry_a_0 row 0 + air.cols.pc_1 row 0 =
        air.cols.pc_1 row 1 + air.cols.pc_carry_a_1 row 0 * 65536 ∧
      air.cols.pc_carry_a_1 row 0 + air.cols.pc_2 row 0 =
        air.cols.pc_2 row 1 + air.cols.pc_carry_a_2 row 0 * 65536 ∧
      air.cols.pc_carry_a_2 row 0 = air.cols.pc_carry_a_3 row 0 * 65536 ∧
      air.cols.pc_carry_a_3 row 0 = 0 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind
    -- Cross-row sum: needs `h_wf` at `row + 1`. Derive `row + 1 ≤ air.last_row`
    -- from `Circuit.isTransitionRow air row = 1` + `h_row`.
    have h_row_next : row + 1 ≤ air.last_row := by
      simp [Circuit.isTransitionRow] at h_trans
      simp [Circuit.last_row] at h_trans
      omega
    exact pc_next_row_eq_pc_plus_four_of_pc_carry_a_chain air row h_row_next h_is_real
      (by grind) h_real_next (by grind) h_ca_0 h_ca_1 h_chain_a

  /-- ALU row: `is_alu = 1`. All branchy / jumpy / ecall-halt absences are derived
  internally from `is_alu = 1` via `is_alu_eq_one_iff` + `selector_exclusivity`.
  Inherits `is_sequential_instr = 1` (c160) and PC + 4 progression (c161-c170)
  via `is_sequential_active_constraints`. The ALU semantics themselves are
  enforced by the ALU bus interaction, not by direct row constraints. -/
  lemma is_alu_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_is_alu : air.cols.opcode_selector.is_alu row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_sequential_instr row 0 = 1 ∧
    -- same-row sum form: `next_pc = pc + 4`
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64 ∧
    -- cross-row sum form: `pc (row+1) = pc + 4`
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ] =
        U64w.toBV (pc air row) + 4#64)
  := by
    have h_opcode := (is_alu_eq_one_iff air row h_is_real (by grind)).mp h_is_alu
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have ⟨h_no_branch_sum, h_no_jal, h_no_jalr, h_no_ecall⟩ :
      (air.cols.opcode_selector.is_beq row 0 +
         air.cols.opcode_selector.is_bne row 0 +
         air.cols.opcode_selector.is_blt row 0 +
         air.cols.opcode_selector.is_bge row 0 +
         air.cols.opcode_selector.is_bltu row 0 +
         air.cols.opcode_selector.is_bgeu row 0 = 0) ∧
      air.cols.opcode_selector.is_jal row 0 = 0 ∧
      air.cols.opcode_selector.is_jalr row 0 = 0 ∧
      air.cols.opcode_selector.is_ecall row 0 = 0 := by grind (splits := 96)
    have h_no_ecall_halt :
      air.cols.opcode_specific.specific_9 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0 := by
      simp [h_no_ecall]
    clear h_opcode h_excl
    exact is_sequential_active_constraints air row h_row h_is_real (by grind) h_no_branch_sum
      h_no_jal h_no_jalr h_no_ecall_halt h_constraints

  /-- Load row: `is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld = 1`.
  Branchy / jumpy / ecall-halt absences are derived internally. Same PC
  progression as ALU; load semantics are enforced via the Memory bus interaction. -/
  lemma is_load_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_load_sum : air.cols.opcode_selector.is_lb row 0 +
                  air.cols.opcode_selector.is_lbu row 0 +
                  air.cols.opcode_selector.is_lh row 0 +
                  air.cols.opcode_selector.is_lhu row 0 +
                  air.cols.opcode_selector.is_lw row 0 +
                  air.cols.opcode_selector.is_lwu row 0 +
                  air.cols.opcode_selector.is_ld row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_sequential_instr row 0 = 1 ∧
    -- same-row sum form: `next_pc = pc + 4`
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64 ∧
    -- cross-row sum form: `pc (row+1) = pc + 4`
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ] =
        U64w.toBV (pc air row) + 4#64)
  := by
    have h_opcode := (is_load_sum_eq_one_iff air row h_is_real (by grind)).mp h_load_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have ⟨h_no_branch_sum, h_no_jal, h_no_jalr, h_no_ecall⟩ :
      (air.cols.opcode_selector.is_beq row 0 +
         air.cols.opcode_selector.is_bne row 0 +
         air.cols.opcode_selector.is_blt row 0 +
         air.cols.opcode_selector.is_bge row 0 +
         air.cols.opcode_selector.is_bltu row 0 +
         air.cols.opcode_selector.is_bgeu row 0 = 0) ∧
      air.cols.opcode_selector.is_jal row 0 = 0 ∧
      air.cols.opcode_selector.is_jalr row 0 = 0 ∧
      air.cols.opcode_selector.is_ecall row 0 = 0 := by grind (splits := 96)
    have h_no_ecall_halt :
      air.cols.opcode_specific.specific_9 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0 := by
      simp [h_no_ecall]
    exact is_sequential_active_constraints air row h_row h_is_real (by grind) h_no_branch_sum
      h_no_jal h_no_jalr h_no_ecall_halt h_constraints

  /-- AUIPC row: `is_auipc = 1`. Branchy / jumpy / ecall-halt absences are derived
  internally. Same PC progression as ALU; AUIPC semantics (adding the immediate
  upper-20-bit-shifted to PC) are enforced via the ALU bus lookup. -/
  lemma is_auipc_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_is_auipc : air.cols.opcode_selector.is_auipc row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_sequential_instr row 0 = 1 ∧
    -- same-row sum form: `next_pc = pc + 4`
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64 ∧
    -- cross-row sum form: `pc (row+1) = pc + 4`
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ] =
        U64w.toBV (pc air row) + 4#64)
  := by
    have h_opcode := (is_auipc_eq_one_iff air row h_is_real (by grind)).mp h_is_auipc
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have h_no_branch_sum :
      air.cols.opcode_selector.is_beq row 0 +
        air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 +
        air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 +
        air.cols.opcode_selector.is_bgeu row 0 = 0 := by grind (splits := 64)
    have h_no_jal : air.cols.opcode_selector.is_jal row 0 = 0 := by grind (splits := 64)
    have h_no_jalr : air.cols.opcode_selector.is_jalr row 0 = 0 := by grind (splits := 64)
    have h_no_ecall : air.cols.opcode_selector.is_ecall row 0 = 0 := by grind (splits := 64)
    have h_no_ecall_halt :
      air.cols.opcode_specific.specific_9 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0 := by
      simp [h_no_ecall]
    exact is_sequential_active_constraints air row h_row h_is_real (by grind) h_no_branch_sum
      h_no_jal h_no_jalr h_no_ecall_halt h_constraints

  /-- Store row: `is_sb + is_sh + is_sw + is_sd = 1`. Branchy / jumpy /
  ecall-halt absences are derived internally. Same sequential PC progression
  as ALU / load / auipc; store semantics (writing to memory at `pc + op_c`)
  are enforced via the Memory bus interaction. The chip also forces op_a's
  value to match its previous value (stores don't write to rd). -/
  lemma is_store_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_store_sum : air.cols.opcode_selector.is_sb row 0 +
                   air.cols.opcode_selector.is_sh row 0 +
                   air.cols.opcode_selector.is_sw row 0 +
                   air.cols.opcode_selector.is_sd row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_sequential_instr row 0 = 1 ∧
    -- same-row sum form: `next_pc = pc + 4`
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64 ∧
    -- cross-row sum form: `pc (row+1) = pc + 4`
    (Circuit.isTransitionRow air row = 1 →
      air.cols.is_real row 1 = 1 →
      U64w.toBV #v[ air.cols.pc_0 row 1, air.cols.pc_1 row 1, air.cols.pc_2 row 1, 0#16 ] =
        U64w.toBV (pc air row) + 4#64) ∧
    -- (c24-c27) op_a value = prev value (no register write on stores)
    air.cols.op_a_access.access.value_0 row 0 = air.cols.op_a_access.prev_value_0 row 0 ∧
    air.cols.op_a_access.access.value_1 row 0 = air.cols.op_a_access.prev_value_1 row 0 ∧
    air.cols.op_a_access.access.value_2 row 0 = air.cols.op_a_access.prev_value_2 row 0 ∧
    air.cols.op_a_access.access.value_3 row 0 = air.cols.op_a_access.prev_value_3 row 0
  := by
    have h_opcode := (is_store_sum_eq_one_iff air row h_is_real (by grind)).mp h_store_sum
    have h_excl := selector_exclusivity air row h_is_real (by grind)
    simp [program_bus_entry, ProgramBusEntry.deserialise] at h_excl
    have ⟨h_no_branch_sum, h_no_jal, h_no_jalr, h_no_ecall⟩ :
      (air.cols.opcode_selector.is_beq row 0 +
         air.cols.opcode_selector.is_bne row 0 +
         air.cols.opcode_selector.is_blt row 0 +
         air.cols.opcode_selector.is_bge row 0 +
         air.cols.opcode_selector.is_bltu row 0 +
         air.cols.opcode_selector.is_bgeu row 0 = 0) ∧
      air.cols.opcode_selector.is_jal row 0 = 0 ∧
      air.cols.opcode_selector.is_jalr row 0 = 0 ∧
      air.cols.opcode_selector.is_ecall row 0 = 0 := by grind (splits := 96)
    have h_no_ecall_halt :
      air.cols.opcode_specific.specific_9 row 0 * air.cols.opcode_selector.is_ecall row 0 = 0 := by
      simp [h_no_ecall]
    -- Sequential PC progression via is_sequential_active_constraints.
    have h_seq := is_sequential_active_constraints air row h_row h_is_real h_wf h_no_branch_sum
      h_no_jal h_no_jalr h_no_ecall_halt h_constraints
    -- (c24-c27) op_a unchanged: c24-c27 fire when (branch_sum + store_sum) ≠ 0.
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    obtain ⟨ h_c24, h_c25, h_c26, h_c27 ⟩
    : constraint_24 air row ∧ constraint_25 air row ∧
      constraint_26 air row ∧ constraint_27 air row := by
      clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_and_interaction_simplification, h_no_branch_sum, h_store_sum,
          one_mul, zero_add, sub_eq_zero]
      at h_c24 h_c25 h_c26 h_c27
    exact ⟨h_seq.1, h_seq.2.1, h_seq.2.2, h_c24, h_c25, h_c26, h_c27⟩

  -- ============================================================================
  -- Branch comparison interpretations: under `branch_sum = 1`, the chip's two
  -- ALU SLT/SLTU lookups (raw_bus_row lines 2331-2332) expose `specific_2 =
  -- 1[op_a < op_b]` and `specific_1 = 1[op_b < op_a]`. The comparison is signed
  -- when `is_blt + is_bge = 1`, unsigned otherwise. Mirrors RV32's
  -- `branch_instruction_a_lt_b` / `branch_instruction_a_gt_b`
  -- (CpuAir.lean:3548 / 3600). -/
  -- ============================================================================

  /-- `specific_2 = 1[op_a < op_b]`: signed when `is_blt ∨ is_bge`, unsigned otherwise.
  ALU bus position .2.2.2.1 (third ALU entry = branch_compare_a, raw_bus_row line 2331). -/
  lemma branch_instruction_a_lt_b
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_branch_sum : air.cols.opcode_selector.is_beq row 0 +
                    air.cols.opcode_selector.is_bne row 0 +
                    air.cols.opcode_selector.is_blt row 0 +
                    air.cols.opcode_selector.is_bge row 0 +
                    air.cols.opcode_selector.is_bltu row 0 +
                    air.cols.opcode_selector.is_bgeu row 0 = 1)
  :
    air.cols.opcode_specific.specific_2 row 0 =
      if (air.cols.opcode_selector.is_blt row 0 = 1 ∨ air.cols.opcode_selector.is_bge row 0 = 1) then
        (if U64w.toInt #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ] <
            U64w.toInt #v[ air.cols.op_b_access.access.value_0 row 0,
                          air.cols.op_b_access.access.value_1 row 0,
                          air.cols.op_b_access.access.value_2 row 0,
                          air.cols.op_b_access.access.value_3 row 0 ]
         then 1 else 0)
      else
        (if U64w.toNat #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ] <
            U64w.toNat #v[ air.cols.op_b_access.access.value_0 row 0,
                          air.cols.op_b_access.access.value_1 row 0,
                          air.cols.op_b_access.access.value_2 row 0,
                          air.cols.op_b_access.access.value_3 row 0 ]
         then 1 else 0)
  := by
    have h_cases := branch_sum_picks_selector air row h_is_real (by grind) h_branch_sum
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_branch_sum, h_is_real]
      at h_wf
    replace h_wf := h_wf.2.2.2.1
    simp [ALUBus.Spec, RV64IM.execute_RTYPE_pure] at h_wf
    obtain h | h | h | h | h | h := h_cases
    all_goals
      simp [h] at h_wf ⊢; clear *- h_wf
      obtain ⟨ ub_sp2, h_wf ⟩ := h_wf
      simp [← BitVec.toNat_inj, U64w.toNat] at h_wf ⊢
      rw [Nat.mod_eq_of_lt ub_sp2] at h_wf
      simp [Fin.ext_iff, h_wf]
      split_ifs <;> simp

  /-- `specific_1 = 1[op_b < op_a]`: signed when `is_blt ∨ is_bge`, unsigned otherwise.
  ALU bus position .2.2.2.2.1 (fourth ALU entry = branch_compare_b, raw_bus_row line 2332). -/
  lemma branch_instruction_a_gt_b
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_branch_sum : air.cols.opcode_selector.is_beq row 0 +
                    air.cols.opcode_selector.is_bne row 0 +
                    air.cols.opcode_selector.is_blt row 0 +
                    air.cols.opcode_selector.is_bge row 0 +
                    air.cols.opcode_selector.is_bltu row 0 +
                    air.cols.opcode_selector.is_bgeu row 0 = 1)
  :
    air.cols.opcode_specific.specific_1 row 0 =
      if (air.cols.opcode_selector.is_blt row 0 = 1 ∨ air.cols.opcode_selector.is_bge row 0 = 1) then
        (if U64w.toInt #v[ air.cols.op_b_access.access.value_0 row 0,
                          air.cols.op_b_access.access.value_1 row 0,
                          air.cols.op_b_access.access.value_2 row 0,
                          air.cols.op_b_access.access.value_3 row 0 ] <
            U64w.toInt #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
         then 1 else 0)
      else
        (if U64w.toNat #v[ air.cols.op_b_access.access.value_0 row 0,
                          air.cols.op_b_access.access.value_1 row 0,
                          air.cols.op_b_access.access.value_2 row 0,
                          air.cols.op_b_access.access.value_3 row 0 ] <
            U64w.toNat #v[ air.cols.op_a_access.access.value_0 row 0,
                          air.cols.op_a_access.access.value_1 row 0,
                          air.cols.op_a_access.access.value_2 row 0,
                          air.cols.op_a_access.access.value_3 row 0 ]
         then 1 else 0)
  := by
    have h_cases := branch_sum_picks_selector air row h_is_real (by grind) h_branch_sum
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_branch_sum, h_is_real]
      at h_wf
    replace h_wf := h_wf.2.2.2.2.1
    simp [ALUBus.Spec, RV64IM.execute_RTYPE_pure] at h_wf
    obtain h | h | h | h | h | h := h_cases
    all_goals
      simp [h] at h_wf ⊢; clear *- h_wf
      obtain ⟨ ub_sp2, h_wf ⟩ := h_wf
      simp [← BitVec.toNat_inj, U64w.toNat] at h_wf ⊢
      rw [Nat.mod_eq_of_lt ub_sp2] at h_wf
      simp [Fin.ext_iff, h_wf]
      split_ifs <;> simp

  /-- u16 bounds on op_a / op_b / op_c access values:
    * **op_a value** (4 limbs) — from `h_wf_asrt` (State-bus producer, mult = -is_real)
    * **op_a prev_value** (4 limbs) — from `h_wf` (State-bus consumer for the
      read entry, mult = +is_real)
    * **op_b value** (4 limbs) — from `h_wf` *gated on `imm_b = 0`* (State-bus
      consumer for op_b register read, mult = 1 - imm_b)
    * **op_c value** (4 limbs) — from `h_wf` *gated on `imm_c = 0`* (analogous).
  Loose RV64 analog of RV32's unconditional `operand_range` (CpuAir.lean:3342);
  the immediate cases (`imm_b = 1` / `imm_c = 1`) are intentionally deferred —
  callers can pull those bounds from `program_bus_operand_properties` if needed. -/
  lemma operand_range
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_wf_asrt : bus_row_wf_asrt (bus_row air row))
  :
    (air.cols.op_a_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_3 row 0).val < 65536 ∧
    (air.cols.op_a_access.prev_value_0 row 0).val < 65536 ∧
    (air.cols.op_a_access.prev_value_1 row 0).val < 65536 ∧
    (air.cols.op_a_access.prev_value_2 row 0).val < 65536 ∧
    (air.cols.op_a_access.prev_value_3 row 0).val < 65536 ∧
    (air.cols.opcode_selector.imm_b row 0 = 0 →
      (air.cols.op_b_access.access.value_0 row 0).val < 65536 ∧
      (air.cols.op_b_access.access.value_1 row 0).val < 65536 ∧
      (air.cols.op_b_access.access.value_2 row 0).val < 65536 ∧
      (air.cols.op_b_access.access.value_3 row 0).val < 65536) ∧
    (air.cols.opcode_selector.imm_c row 0 = 0 →
      (air.cols.op_c_access.access.value_0 row 0).val < 65536 ∧
      (air.cols.op_c_access.access.value_1 row 0).val < 65536 ∧
      (air.cols.op_c_access.access.value_2 row 0).val < 65536 ∧
      (air.cols.op_c_access.access.value_3 row 0).val < 65536)
  := by
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf
    simp [bus_row_wf_asrt, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf_asrt
    grind

end CpuChip.Interpretations
