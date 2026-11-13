import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.RVSail.BusesV3

open Plonky3

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 2_000_000
set_option linter.constructorNameAsVariable false

/-!
# CpuChip interpretations (RV64, Pico v3.1.1)

Readable facts about one row of the v3.1.1 `CpuChip`, derived from the restated constraints of
`Constraints/CpuChip.lean` and the bus contracts of `RVSail/BusesV3.lean`. This file holds the
part every instruction class needs; the lemmas only the U-type, load, store, branch and jump
theorems use come with those classes.

The v3.1.1 chip checks much less itself than the 2.x one did, so the facts come from different
places:

- **The pc** is no longer range-checked by the chip. Its two 16-bit pieces, its alignment, the
  `0x7800_0000` bound and the meaning of `pc_carry` all come from the Program table, through
  `ProgramBusEntry.operand_properties` and `inversion_pc_facts` (`pc_facts` below).
- **The next pc** is not checked either. On an internal row it is the next row's pc, which the
  Program table bounds; on the chunk's last real row it is public values 43 and 44, which only
  the whole-trace assumption bounds. `next_pc_facts` takes that assumption's four parts as
  hypotheses, and `Equivalence/Common.lean` packages them as
  `pico_CpuChip_control_flow_assumptions`.
- **The class selectors** come from the Program message as functions of the opcode
  (`class_selectors_of_opcode`, `imm_b_of_opcode`, `imm_c_of_opcode`), not from chip
  constraints.
- **`next_pc = pc + 4`** on a sequential row is the single field equation of constraint 37,
  with no carry witness; reading it as a 64-bit addition needs the pc and next-pc bounds above.

Names are the 2.x ones wherever the meaning is unchanged, so the instruction-theorem files have
less to rewrite.
-/

namespace CpuChip.Interpretations

  open CpuChip.ConstraintsAndBuses
  open RV64IM_Interactions.V3

  -- ============================================================================
  -- The row's messages, its pc and its next pc
  -- ============================================================================

  /-- The CPU chip's typed bus row, sorted out of the chip's raw messages by
      `deserialise_bus_row`. Downstream proofs take the canonical
      `bus_row_wf_asm (bus_row air row)` hypothesis, as the other chips do. -/
  def bus_row {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : BusRow :=
    deserialise_bus_row (CpuChip.ConstraintsAndBuses.raw_bus_row air row)

  /-- The Program-bus message the chip sends on each row: the `(multiplicity, payload)` pair
      that `ProgramBusEntry.deserialise` reads. It mirrors the first entry of `raw_bus_row`,
      `pc(2) ++ [opcode] ++ InstructionCols(9) ++ OpcodeSelectorCols(13) ++ [pc_carry]`. -/
  def program_bus_entry {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      FKB × Vector FKB 26 :=
    ( air.cols.is_real row 0
    , #v[ air.cols.pc_0 row 0
        , air.cols.pc_1 row 0
        , air.cols.instruction.opcode row 0
        , air.cols.instruction.opcode row 0
        , air.cols.instruction.op_a row 0
        , air.cols.instruction.op_b_0 row 0
        , air.cols.instruction.op_b_1 row 0
        , air.cols.instruction.op_b_sign row 0
        , air.cols.instruction.op_c_0 row 0
        , air.cols.instruction.op_c_1 row 0
        , air.cols.instruction.op_c_sign row 0
        , air.cols.instruction.op_a_is_x0 row 0
        , air.cols.opcode_selector.imm_b row 0
        , air.cols.opcode_selector.imm_c row 0
        , air.cols.opcode_selector.is_ecall row 0
        , air.cols.opcode_selector.is_memory row 0
        , air.cols.opcode_selector.is_store row 0
        , air.cols.opcode_selector.is_beq row 0
        , air.cols.opcode_selector.is_bne row 0
        , air.cols.opcode_selector.is_blt row 0
        , air.cols.opcode_selector.is_bge row 0
        , air.cols.opcode_selector.is_bltu row 0
        , air.cols.opcode_selector.is_bgeu row 0
        , air.cols.opcode_selector.is_jalr row 0
        , air.cols.opcode_selector.is_jal row 0
        , air.cols.pc_carry row 0 ] )

  /-- The Program message as a `ProgramBusEntry`, with its 26 fields written out: rewriting
      with this once saves every later proof from unfolding `deserialise` again. -/
  lemma deserialise_program_bus_entry {ExtF : Type} [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      ProgramBusEntry.deserialise (program_bus_entry air row) =
        ⟨ air.cols.is_real row 0
        , air.cols.pc_0 row 0
        , air.cols.pc_1 row 0
        , air.cols.instruction.opcode row 0
        , air.cols.instruction.opcode row 0
        , air.cols.instruction.op_a row 0
        , air.cols.instruction.op_b_0 row 0
        , air.cols.instruction.op_b_1 row 0
        , air.cols.instruction.op_b_sign row 0
        , air.cols.instruction.op_c_0 row 0
        , air.cols.instruction.op_c_1 row 0
        , air.cols.instruction.op_c_sign row 0
        , air.cols.instruction.op_a_is_x0 row 0
        , air.cols.opcode_selector.imm_b row 0
        , air.cols.opcode_selector.imm_c row 0
        , air.cols.opcode_selector.is_ecall row 0
        , air.cols.opcode_selector.is_memory row 0
        , air.cols.opcode_selector.is_store row 0
        , air.cols.opcode_selector.is_beq row 0
        , air.cols.opcode_selector.is_bne row 0
        , air.cols.opcode_selector.is_blt row 0
        , air.cols.opcode_selector.is_bge row 0
        , air.cols.opcode_selector.is_bltu row 0
        , air.cols.opcode_selector.is_bgeu row 0
        , air.cols.opcode_selector.is_jalr row 0
        , air.cols.opcode_selector.is_jal row 0
        , air.cols.pc_carry row 0 ⟩ := rfl

  /-- The row's pc as a `U64w`. The chip keeps it in two 16-bit pieces, so the top two limbs
      are zero; the packing is faithful exactly when the two pieces are 16-bit, which
      `pc_facts` gives on a real row. -/
  def pc {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
    #v[air.cols.pc_0 row 0, air.cols.pc_1 row 0, 0#16, 0#16]

  /-- The row's next pc as a `U64w`, in the same two-piece packing as `pc`. -/
  def next_pc {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
    #v[air.cols.next_pc_0 row 0, air.cols.next_pc_1 row 0, 0#16, 0#16]

  -- ============================================================================
  -- Column rotation invariance
  --
  -- `cols.X row rotation = cols.X ((row + rotation) % (last_row + 1)) 0`, from `air.isValid`'s
  -- `valid_circuit` clause at the column's index in the main grid. Only the three columns the
  -- cross-row arguments read are needed: `pc_0` (2), `pc_1` (3) and `is_real` (53).
  -- ============================================================================

  /-- `pc_0` rotation invariance (column 2). -/
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
      specialize valid_circuit 2 row rotation
      have valid_col_2 : ∀ row rotation, air.col_2 row rotation := by aesop
      unfold Raw_CpuChip.col_2 at valid_col_2
      iterate 2 rw [valid_col_2] at valid_circuit
      clear valid_col_2
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_2 row rotation := by aesop
      unfold Raw_CpuCols.col_2 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `pc_1` rotation invariance (column 3). -/
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
      specialize valid_circuit 3 row rotation
      have valid_col_3 : ∀ row rotation, air.col_3 row rotation := by aesop
      unfold Raw_CpuChip.col_3 at valid_col_3
      iterate 2 rw [valid_col_3] at valid_circuit
      clear valid_col_3
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_3 row rotation := by aesop
      unfold Raw_CpuCols.col_3 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  /-- `is_real` rotation invariance (column 53). -/
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
      specialize valid_circuit 53 row rotation
      have valid_col_53 : ∀ row rotation, air.col_53 row rotation := by aesop
      unfold Raw_CpuChip.col_53 at valid_col_53
      iterate 2 rw [valid_col_53] at valid_circuit
      clear valid_col_53
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), cols.col_53 row rotation := by aesop
      unfold Raw_CpuCols.col_53 at valid_cols
      clear *- valid_circuit valid_cols
      grind

  -- ============================================================================
  -- The Program message
  -- ============================================================================

  /-- On a real row the chip's Program message carries the Program table's promise: it is the
      row the table holds for some instruction at some 4-aligned address below
      `0x7800_0000`. -/
  lemma program_bus_operand_properties
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    ProgramBusEntry.operand_properties
      (ProgramBusEntry.deserialise (program_bus_entry air row))
  := by
    simp [bus_row_wf_asm] at h_wf; replace h_wf := h_wf.1
    simp [bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf
    simpa [program_bus_entry, ProgramBusEntry.deserialise, h_is_real]

  /-- The two opcode fields agree, and the opcode is one the decoder produces: 0 to 25, 28,
      30 to 37, or 40 to 52. In particular no row carries the 2.x `AUIPC` opcode 27. -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    (air.cols.instruction.opcode row 0).val ≤ 25 ∨
    (air.cols.instruction.opcode row 0).val = 28 ∨
    (30 ≤ (air.cols.instruction.opcode row 0).val ∧
     (air.cols.instruction.opcode row 0).val ≤ 37) ∨
    (40 ≤ (air.cols.instruction.opcode row 0).val ∧
     (air.cols.instruction.opcode row 0).val ≤ 52)
  := by
    have h_prog := program_bus_operand_properties air row h_is_real h_wf
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ := h_prog
    have h := ProgramBusEntry.inversion_opcode_bounds h_trans h_deser
    rw [deserialise_program_bus_entry] at h
    simpa using h

  /-- The row's class selectors and immediate flags, as functions of its opcode. With
      `h : opcode = k` a caller rewrites and reads off the entry for `k`: for an ALU opcode
      every class selector is zero, and `imm_b_of_opcode` / `imm_c_of_opcode` pin the flag
      wherever the opcode determines it. -/
  lemma selector_exclusivity
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    #v[ air.cols.opcode_selector.is_ecall row 0
      , air.cols.opcode_selector.is_memory row 0
      , air.cols.opcode_selector.is_store row 0
      , air.cols.opcode_selector.is_beq row 0
      , air.cols.opcode_selector.is_bne row 0
      , air.cols.opcode_selector.is_blt row 0
      , air.cols.opcode_selector.is_bge row 0
      , air.cols.opcode_selector.is_bltu row 0
      , air.cols.opcode_selector.is_bgeu row 0
      , air.cols.opcode_selector.is_jalr row 0
      , air.cols.opcode_selector.is_jal row 0 ] =
      class_selectors_of_opcode (air.cols.instruction.opcode row 0).val ∧
    (∀ f, imm_b_of_opcode (air.cols.instruction.opcode row 0).val = some f →
      air.cols.opcode_selector.imm_b row 0 = f) ∧
    (∀ f, imm_c_of_opcode (air.cols.instruction.opcode row 0).val = some f →
      air.cols.opcode_selector.imm_c row 0 = f)
  := by
    have h_prog := program_bus_operand_properties air row h_is_real h_wf
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ := h_prog
    have h := ProgramBusEntry.inversion_opcode_selectors h_trans h_deser
    rw [deserialise_program_bus_entry] at h
    simpa [ProgramBusEntry.class_selectors] using h

  /-- The ALU case of `selector_exclusivity`, the one the first wave of instruction theorems
      needs: an opcode whose class selectors are all zero leaves every class selector zero, so
      the row is a sequential one. A caller discharges `h_class` by `rw [h_opcode]; rfl`. -/
  lemma alu_class_selectors_zero
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_class : class_selectors_of_opcode (air.cols.instruction.opcode row 0).val =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  :
    air.cols.opcode_selector.is_ecall row 0 = 0 ∧
    air.cols.opcode_selector.is_memory row 0 = 0 ∧
    air.cols.opcode_selector.is_store row 0 = 0 ∧
    air.cols.opcode_selector.is_beq row 0 = 0 ∧
    air.cols.opcode_selector.is_bne row 0 = 0 ∧
    air.cols.opcode_selector.is_blt row 0 = 0 ∧
    air.cols.opcode_selector.is_bge row 0 = 0 ∧
    air.cols.opcode_selector.is_bltu row 0 = 0 ∧
    air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
    air.cols.opcode_selector.is_jalr row 0 = 0 ∧
    air.cols.opcode_selector.is_jal row 0 = 0
  := by
    have h := (selector_exclusivity air row h_is_real h_wf).1
    rw [h_class] at h
    refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    · simpa using congrArg (fun v => v[0]) h
    · simpa using congrArg (fun v => v[1]) h
    · simpa using congrArg (fun v => v[2]) h
    · simpa using congrArg (fun v => v[3]) h
    · simpa using congrArg (fun v => v[4]) h
    · simpa using congrArg (fun v => v[5]) h
    · simpa using congrArg (fun v => v[6]) h
    · simpa using congrArg (fun v => v[7]) h
    · simpa using congrArg (fun v => v[8]) h
    · simpa using congrArg (fun v => v[9]) h
    · simpa using congrArg (fun v => v[10]) h

  /-- The Sail instruction the row's Program message was decoded from, as a function of the
      opcode (`ProgramBusEntry.decoded_from`). -/
  lemma operand_properties_inversion
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    ∃ instr pc_value,
      (ProgramBusEntry.deserialise (program_bus_entry air row)).decoded_from instr pc_value
        (air.cols.instruction.opcode row 0).val
  := by
    have h_prog := program_bus_operand_properties air row h_is_real h_wf
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ := h_prog
    refine ⟨ instr, pc', ?_ ⟩
    have h := ProgramBusEntry.operand_properties_inversion h_trans h_deser
    rw [deserialise_program_bus_entry] at h ⊢
    exact h

  -- ============================================================================
  -- The pc and the next pc
  -- ============================================================================

  /-- Everything the Program table says about a real row's address: the two pieces are 16-bit,
      the high one is at most `0x77FF`, the low one is 4-aligned, together they make an address
      below `0x7800_0000`, and `pc_carry` is `[pc[0] >= 0xFFFC]`. -/
  lemma pc_facts
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    (air.cols.pc_0 row 0).val < 65536 ∧
    (air.cols.pc_1 row 0).val ≤ 0x77FF ∧
    (air.cols.pc_0 row 0).val % 4 = 0 ∧
    (air.cols.pc_0 row 0).val + 65536 * (air.cols.pc_1 row 0).val < 0x7800_0000 ∧
    air.cols.pc_carry row 0 = (if 0xFFFC ≤ (air.cols.pc_0 row 0).val then 1 else 0)
  := by
    have h_prog := program_bus_operand_properties air row h_is_real h_wf
    obtain ⟨ instr, pc', data, props, h_al, h_lt, h_trans, h_deser, _ ⟩ := h_prog
    have h := ProgramBusEntry.inversion_pc_facts h_trans h_deser h_al h_lt
    rw [deserialise_program_bus_entry] at h
    obtain ⟨ h0, h1, h4, hsum, hcarry ⟩ := h
    refine ⟨ h0, h1, h4, ?_, hcarry ⟩
    rw [hsum]
    simpa [Transpiler.V3.code_address_bound] using h_lt

  /-- `pc_facts` in the packed form the equivalence proofs use: the row's `U64w` pc really is
      the address the Program table holds, and it is 4-aligned. -/
  lemma pc_mod_four_eq_zero
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    U64w.toNat (pc air row) % 4 = 0
  := by
    obtain ⟨ h0, h1, h4, _, _ ⟩ := pc_facts air row h_is_real h_wf
    simp [pc, U64w.toNat]
    omega

  /-- The next pc's two pieces are 16-bit and make an address below `0x7800_0000`.
      The chip does not check this: on an internal row the next pc is the next row's pc, which
      the Program table bounds (constraints 46 and 47); on the chunk's last real row it is
      public values 43 and 44 (constraints 41 and 42, through `is_last` from 50 and 51), which
      only the whole-trace assumption bounds. The four `h_pv_*` hypotheses are that assumption;
      `Equivalence/Common.lean` packages them. -/
  lemma next_pc_facts
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (h_pv_lo : (air.public_values 43).val < 65536)
    (h_pv_hi : (air.public_values 44).val < 65536)
    (h_pv_bound : (air.public_values 43).val + 65536 * (air.public_values 44).val < 0x7800_0000)
  :
    (air.cols.next_pc_0 row 0).val < 65536 ∧
    (air.cols.next_pc_1 row 0).val < 65536 ∧
    (air.cols.next_pc_0 row 0).val + 65536 * (air.cols.next_pc_1 row 0).val < 0x7800_0000
  := by
    have h_cs := h_constraints row h_row
    rw [allHold_iff_allHold_simplified] at h_cs
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_cs
    -- The chunk's final pc: `is_last = 1` pins `next_pc` to public values 43 and 44.
    have h_final :
        air.cols.is_last row 0 = 1 →
        air.cols.next_pc_0 row 0 = air.public_values 43 ∧
        air.cols.next_pc_1 row 0 = air.public_values 44 := by
      intro h_last
      obtain ⟨ h_c41, h_c42 ⟩ : constraint_41 air row ∧ constraint_42 air row := by
        clear *- h_cs; aesop
      simp [constraint_and_interaction_simplification, h_last, sub_eq_zero] at h_c41 h_c42
      exact ⟨ h_c41.symm, h_c42.symm ⟩
    by_cases h_transition : Circuit.isTransitionRow air row = 0
    · -- Last physical row: constraint 51 makes it the last real row.
      have h_c51 : constraint_51 air row := by clear *- h_cs; aesop
      simp [Circuit.isTransitionRow] at h_transition
      simp [constraint_and_interaction_simplification, Circuit.isLastRow, ← h_transition,
            h_is_real, sub_eq_zero] at h_c51
      obtain ⟨ h0, h1 ⟩ := h_final h_c51
      rw [h0, h1]; exact ⟨ h_pv_lo, h_pv_hi, h_pv_bound ⟩
    · have h_trans : Circuit.isTransitionRow air row = 1 := by
        simp [Circuit.isTransitionRow] at h_transition ⊢; grind
      have h_row_next : row + 1 ≤ air.last_row := by
        simp [Circuit.isTransitionRow, Circuit.last_row] at h_transition; omega
      have h_mod : (row + 1) % (air.last_row + 1) = row + 1 := Nat.mod_eq_of_lt (by omega)
      by_cases h_real_next : air.cols.is_real row 1 = 0
      · -- The last real row: constraint 50 makes `is_last` the drop in `is_real`.
        have h_c50 : constraint_50 air row := by clear *- h_cs; aesop
        simp [constraint_and_interaction_simplification, h_trans, h_is_real, h_real_next,
              sub_eq_zero] at h_c50
        obtain ⟨ h0, h1 ⟩ := h_final (by simpa using h_c50)
        rw [h0, h1]; exact ⟨ h_pv_lo, h_pv_hi, h_pv_bound ⟩
      · -- An internal row: the next row is real, and its pc is this row's next pc.
        have h_real_next' : air.cols.is_real row 1 = 1 := by
          have h_c44 : constraint_44 air (row + 1) := by
            have h := h_constraints (row + 1) h_row_next
            rw [allHold_iff_allHold_simplified] at h
            simp only [allHold_simplified, row_constraint_list, List.Forall] at h
            clear *- h; aesop
          have h_eq : air.cols.is_real row 1 = air.cols.is_real (row + 1) 0 := by
            rw [is_real_rotation]; simp [h_mod]
          rw [h_eq] at h_real_next ⊢
          simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c44
          grind
        obtain ⟨ h_c46, h_c47 ⟩ : constraint_46 air row ∧ constraint_47 air row := by
          clear *- h_cs; aesop
        simp [constraint_and_interaction_simplification, h_trans, h_real_next',
              sub_eq_zero] at h_c46 h_c47
        -- `h_c46 : pc_0 row 1 = next_pc_0 row 0`, and the same for piece 1.
        have h_pc_next := pc_facts air (row + 1) (by rw [← h_mod, ← is_real_rotation]; exact h_real_next')
          (h_wf (row + 1) h_row_next)
        rw [pc_0_rotation, h_mod] at h_c46
        rw [pc_1_rotation, h_mod] at h_c47
        rw [← h_c46, ← h_c47]
        exact ⟨ h_pc_next.1, by omega, h_pc_next.2.2.2.1 ⟩

  -- ============================================================================
  -- Immediate operands
  -- ============================================================================

  /-- `imm_b = 1`: the `op_b` value is the instruction's immediate, in the `SignExtImm` shape
      the decoder writes — two 16-bit pieces and a sign fill `sign * 65535` in limbs 2 and 3
      (constraints 0 to 3, `register/constraints.rs:29-42`). -/
  lemma imm_b_eq_1_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.op_b_access.access.value_0 row 0 = air.cols.instruction.op_b_0 row 0 ∧
    air.cols.op_b_access.access.value_1 row 0 = air.cols.instruction.op_b_1 row 0 ∧
    air.cols.op_b_access.access.value_2 row 0 = air.cols.instruction.op_b_sign row 0 * 65535 ∧
    air.cols.op_b_access.access.value_3 row 0 = air.cols.instruction.op_b_sign row 0 * 65535
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
    exact ⟨ h_c0, h_c1, h_c2, h_c3 ⟩

  /-- `imm_c = 1`: the `op_c` value is the instruction's immediate (constraints 4 to 7). -/
  lemma imm_c_eq_1_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.op_c_access.access.value_0 row 0 = air.cols.instruction.op_c_0 row 0 ∧
    air.cols.op_c_access.access.value_1 row 0 = air.cols.instruction.op_c_1 row 0 ∧
    air.cols.op_c_access.access.value_2 row 0 = air.cols.instruction.op_c_sign row 0 * 65535 ∧
    air.cols.op_c_access.access.value_3 row 0 = air.cols.instruction.op_c_sign row 0 * 65535
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
    exact ⟨ h_c4, h_c5, h_c6, h_c7 ⟩

  -- ============================================================================
  -- Operand ranges
  -- ============================================================================

  /-- Every operand piece the row reads from or writes to the register file is 16-bit. The
      `op_a` value comes from the chip's own write message (`h_wf_asrt`), its previous value
      and the two register operands from the read messages (`h_wf`), the latter two only when
      the operand is not an immediate. The immediate case is in `imm_b_eq_1_constraints` /
      `imm_c_eq_1_constraints` together with the decoder's `imm_operand_limbs`. -/
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

  -- ============================================================================
  -- Sequential rows
  -- ============================================================================

  /-- Pure arithmetic: a two-piece address and its successor four bytes on, both inside the
      guest address space, satisfy the field equation of constraint 37 exactly when they
      satisfy the 64-bit addition. No chip dependencies. -/
  lemma two_piece_plus_four_implies_sum
    (p_0 p_1 n_0 n_1 : FKB)
    (h_p_0 : p_0.val < 65536) (h_p_1 : p_1.val < 65536)
    (h_n_0 : n_0.val < 65536) (h_n_1 : n_1.val < 65536)
    (h_p_bound : p_0.val + 65536 * p_1.val < 0x7800_0000)
    (h_n_bound : n_0.val + 65536 * n_1.val < 0x7800_0000)
    (h_eq : 1 * n_0 + 65536 * n_1 = 1 * p_0 + 65536 * p_1 + 4)
  :
    U64w.toBV #v[n_0, n_1, 0#16, 0#16] = U64w.toBV #v[p_0, p_1, 0#16, 0#16] + 4#64
  := by
    simp [← BitVec.toNat_inj, U64w.toNat]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    grind

  /-- Off an ecall row the halt flag is zero (constraint 31). -/
  lemma is_halt_eq_zero_of_no_ecall
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_no_ecall : air.cols.opcode_selector.is_ecall row 0 = 0)
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_halt row 0 = 0
  := by
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall] at h_constraints
    have h_c31 : constraint_31 air row := by clear *- h_constraints; aesop
    simp [constraint_and_interaction_simplification, h_no_ecall] at h_c31
    exact h_c31

  /-- A row that takes no branch and is neither a jump nor a halt advances the pc by four:
      constraint 37's gate is `is_real` and its field equation reads as a 64-bit addition once
      the pc and next-pc pieces are bounded. `pc_facts` and `next_pc_facts` supply the bounds,
      so this lemma inherits the whole-trace assumption through `h_pv_*`. -/
  lemma is_sequential_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (h_pv_lo : (air.public_values 43).val < 65536)
    (h_pv_hi : (air.public_values 44).val < 65536)
    (h_pv_bound : (air.public_values 43).val + 65536 * (air.public_values 44).val < 0x7800_0000)
    (h_no_branch : air.cols.opcode_selector.is_beq row 0 = 0 ∧
                   air.cols.opcode_selector.is_bne row 0 = 0 ∧
                   air.cols.opcode_selector.is_blt row 0 = 0 ∧
                   air.cols.opcode_selector.is_bge row 0 = 0 ∧
                   air.cols.opcode_selector.is_bltu row 0 = 0 ∧
                   air.cols.opcode_selector.is_bgeu row 0 = 0)
    (h_no_jal : air.cols.opcode_selector.is_jal row 0 = 0)
    (h_no_jalr : air.cols.opcode_selector.is_jalr row 0 = 0)
    (h_no_halt : air.cols.is_halt row 0 = 0)
  :
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64
  := by
    obtain ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ := h_no_branch
    have h_cs := h_constraints row h_row
    have h_c37 : constraint_37 air row := by
      rw [allHold_iff_allHold_simplified] at h_cs
      simp only [allHold_simplified, row_constraint_list, List.Forall] at h_cs
      clear *- h_cs; aesop
    simp [constraint_and_interaction_simplification, h_is_real, h_beq, h_bne, h_blt, h_bge,
          h_bltu, h_bgeu, h_no_jal, h_no_jalr, h_no_halt, sub_eq_zero] at h_c37
    -- `h_c37` is the field equation `next_pc_0 + 65536 * next_pc_1 = pc_0 + 65536 * pc_1 + 4`.
    obtain ⟨ h_pc_0, h_pc_1, _, h_pc_bound, _ ⟩ := pc_facts air row h_is_real (h_wf row h_row)
    obtain ⟨ h_np_0, h_np_1, h_np_bound ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints h_pv_lo h_pv_hi h_pv_bound
    simp only [next_pc, pc]
    exact two_piece_plus_four_implies_sum _ _ _ _ h_pc_0 (by omega) h_np_0 h_np_1
      (by omega) h_np_bound (by linear_combination h_c37)

end CpuChip.Interpretations
