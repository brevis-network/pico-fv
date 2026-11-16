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
  the whole-trace assumption bounds. That assumption,
  `Equivalence.pico_CpuChip_control_flow_assumptions`, is defined at the top of this file so
  that `next_pc_facts` and the lemmas built on it can take it whole; the instruction theorems
  name it in their statements.
- **The class selectors** come from the Program message as functions of the opcode
  (`class_selectors_of_opcode`, `imm_b_of_opcode`, `imm_c_of_opcode`), not from chip
  constraints.
- **`next_pc = pc + 4`** on a sequential row is the single field equation of constraint 37,
  with no carry witness; reading it as a 64-bit addition needs the pc and next-pc bounds above.
- **Which promises a lemma assumes.** A lemma that needs only the Program table's promise or
  the register file's takes `bus_row_reads_asm`, that part of `bus_row_wf_asm`; the sender
  theorem `CpuChip.Spec.ext_asrt` can then use it without assuming the promises of the chips
  it sends to. A caller holding `bus_row_wf_asm` passes `bus_row_reads_asm_of_wf_asm h_wf`.

Names are the 2.x ones wherever the meaning is unchanged, so the instruction-theorem files have
less to rewrite.
-/

namespace Equivalence

  /-- The one assumption the instruction theorems make about the whole trace: the chunk's
      final pc, public values 43 and 44, is a 4-aligned address of two 16-bit pieces inside
      the guest address space. The chip pins public value 45 to zero itself (constraint 43)
      and range-checks none of the three.

      Pico enforces this outside the chips, in the recursion circuit
      (`vm/src/mle/compiler/recursion/lowering.rs`): each chunk's final pc is the next
      chunk's first pc (`assert_child_continuity`, 1081-1090), a chunk with no CPU rows
      passes its pc through (1436-1440), and the root requires the last chunk's final pc to
      be zero (`assert_root_complete`, 1748-1754). A chunk's first pc is its row 0's pc
      (`riscv_cpu/public_values/constraints.rs:26-33`), row 0 is real
      (`riscv_cpu/constraints.rs:340-341`), and its fetch matches the Program table, whose
      addresses are 4-aligned and below `0x7800_0000` (`riscv_program/traces.rs:83-110`). So
      in an accepted recursive proof the final pc is either zero or a Program-table address,
      and either satisfies this. With it the theorems describe a chunk inside an accepted
      proof, not a chunk proof checked on its own.

      It lives here, under its `Equivalence` name, so that the interpretations lemmas below
      can take it as one hypothesis. -/
  def pico_CpuChip_control_flow_assumptions {ExtF : Type} [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) : Prop :=
    (air.public_values 43).val % 4 = 0 ∧
    (air.public_values 43).val < 65536 ∧
    (air.public_values 44).val < 65536 ∧
    (air.public_values 43).val + 65536 * (air.public_values 44).val < 0x7800_0000

end Equivalence

namespace CpuChip.Interpretations

  open CpuChip.ConstraintsAndBuses
  open RV64IM_Interactions.V3

  -- ============================================================================
  -- One constraint of a row
  -- ============================================================================

  /-- Constraint `k` of a row whose constraints all hold. `constraint_at h 37 (by norm_num)`
      has type `constraint_37 air row` up to unfolding the list, so a proof reads one
      constraint without searching all 65. -/
  lemma constraint_at
    [Field ExtF]
    {air : Valid_CpuChip FKB ExtF} {row : ℕ}
    (h : CpuChip.Extraction.allHold air row) (k : ℕ) (hk : k < 65)
  :
    (row_constraint_list air row)[k]'(by simpa [row_constraint_list] using hk)
  := by
    rw [allHold_iff_allHold_simplified] at h
    exact List.forall_iff_forall_mem.mp h.2 _ (List.getElem_mem _)

  -- ============================================================================
  -- The row's messages, its pc and its next pc
  -- ============================================================================

  /-- The CPU chip's typed bus row, sorted out of the chip's raw messages by
      `deserialise_bus_row`. Downstream proofs take the canonical
      `bus_row_wf_asm (bus_row air row)` hypothesis, as the other chips do. -/
  def bus_row {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : BusRow :=
    deserialise_bus_row (CpuChip.ConstraintsAndBuses.raw_bus_row air row)

  /-- The part of `bus_row_wf_asm` that a row's own facts rest on: the Program table's promise
      on the Program message and the register file's promise on the register-access messages.
      It leaves out the ALU and memory chips' promises on the dispatch and comparison
      messages, so a theorem about what the CPU sends on those messages
      (`CpuChip.Spec.ext_asrt`) can take it without assuming what their receivers prove. -/
  def bus_row_reads_asm (r : BusRow) : Prop :=
    List.Forall id
      (r.Program.map (Interaction.BusEntry.wf_assume FKB) ++
       r.State.map (Interaction.BusEntry.wf_assume FKB))

  /-- The whole-row assumption contains the reads assumption. -/
  lemma bus_row_reads_asm_of_wf_asm {r : BusRow} (h : bus_row_wf_asm r) :
      bus_row_reads_asm r := by
    simp only [bus_row_wf_asm, bus_row_reads_asm, List.forall_iff_forall_mem,
      List.mem_append] at h ⊢
    intro x hx
    exact h x (by tauto)

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
  -- cross-row arguments read are needed: `pc_0` (2), `pc_1` (3) and `is_real` (53). A branch
  -- or jump class that needs another column adds one line with `column_rotation`.
  -- ============================================================================

  set_option hygiene false in
  open Lean in
  /-- Proves `cols.X row rotation = cols.X ((row + rotation) % (last_row + 1)) 0` for the
      column `X` (given as its `Valid_CpuCols` accessor) at index `n` of the main grid. The
      proof needs the binders to be named `air`, `row` and `rotation`. -/
  local macro "column_rotation " field:ident n:num : tactic => do
    let col := s!"col_{n.getNat}"
    let rawChipCol := mkIdent (Name.mkStr `Raw_CpuChip col)
    let rawColsCol := mkIdent (Name.mkStr `Raw_CpuCols col)
    `(tactic| (
      obtain ⟨ air, is_valid ⟩ := air
      unfold $field:ident Valid_CpuChip.cols Valid_CpuChip.last_row; simp
      obtain ⟨ valid_circuit, valid_cols, _ ⟩ := is_valid
      replace valid_circuit : ∀ (column row rotation : ℕ),
        air.main column row rotation = air.main column ((row + rotation) % (air.last_row + 1)) 0 :=
        by aesop
      specialize valid_circuit $n row rotation
      have valid_col : ∀ row rotation, $rawChipCol:ident air row rotation := by aesop
      unfold $rawChipCol:ident at valid_col
      iterate 2 rw [valid_col] at valid_circuit
      clear valid_col
      obtain ⟨ bus, challenge, main, permutation, preprocessed, public_values, last_row, cols ⟩ := air
      simp_all
      unfold Raw_CpuCols.isValid at valid_cols
      replace valid_cols : ∀ (row rotation : ℕ), $rawColsCol:ident cols row rotation := by aesop
      unfold $rawColsCol:ident at valid_cols
      clear *- valid_circuit valid_cols
      grind))

  /-- `pc_0` rotation invariance (column 2). -/
  lemma pc_0_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.pc_0 row rotation = air.cols.pc_0 ((row + rotation) % (air.last_row + 1)) 0
    := by column_rotation Valid_CpuCols.pc_0 2

  /-- `pc_1` rotation invariance (column 3). -/
  lemma pc_1_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.pc_1 row rotation = air.cols.pc_1 ((row + rotation) % (air.last_row + 1)) 0
    := by column_rotation Valid_CpuCols.pc_1 3

  /-- `is_real` rotation invariance (column 53). -/
  lemma is_real_rotation
      (air : Valid_CpuChip FKB ExtF)
      (row rotation : ℕ)
    : air.cols.is_real row rotation = air.cols.is_real ((row + rotation) % (air.last_row + 1)) 0
    := by column_rotation Valid_CpuCols.is_real 53

  -- ============================================================================
  -- The Program message
  -- ============================================================================

  /-- On a real row the chip's Program message carries the Program table's promise: it is the
      row the table holds for some instruction at some 4-aligned address below
      `0x7800_0000`. -/
  lemma program_bus_operand_properties_of_reads
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
  :
    ProgramBusEntry.operand_properties
      (ProgramBusEntry.deserialise (program_bus_entry air row))
  := by
    simp [bus_row_reads_asm] at h_reads; replace h_reads := h_reads.1
    simp [bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_reads
    simpa [program_bus_entry, ProgramBusEntry.deserialise, h_is_real]

  /-- `program_bus_operand_properties_of_reads` from the whole-row assumption. -/
  lemma program_bus_operand_properties
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    ProgramBusEntry.operand_properties
      (ProgramBusEntry.deserialise (program_bus_entry air row))
  :=
    program_bus_operand_properties_of_reads air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)

  /-- The opcode is one the decoder produces: 0 to 25, 28, 30 to 37, or 40 to 52. In
      particular no row carries the 2.x `AUIPC` opcode 27. (The chip sends the same column as
      both opcode fields of the message, so their agreement says nothing about the row.) -/
  lemma selector_breakdown
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
  :
    (air.cols.instruction.opcode row 0).val ≤ 25 ∨
    (air.cols.instruction.opcode row 0).val = 28 ∨
    (30 ≤ (air.cols.instruction.opcode row 0).val ∧
     (air.cols.instruction.opcode row 0).val ≤ 37) ∨
    (40 ≤ (air.cols.instruction.opcode row 0).val ∧
     (air.cols.instruction.opcode row 0).val ≤ 52)
  := by
    have h_prog := program_bus_operand_properties_of_reads air row h_is_real h_reads
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
    (h_reads : bus_row_reads_asm (bus_row air row))
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
    have h_prog := program_bus_operand_properties_of_reads air row h_is_real h_reads
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ := h_prog
    have h := ProgramBusEntry.inversion_opcode_selectors h_trans h_deser
    rw [deserialise_program_bus_entry] at h
    simpa [ProgramBusEntry.class_selectors] using h

  /-- The row's class selectors one by one, as the Program table sets them for its opcode:
      the first part of `selector_exclusivity` split into its eleven entries. -/
  lemma selectors_by_opcode
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
  :
    air.cols.opcode_selector.is_ecall row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[0] ∧
    air.cols.opcode_selector.is_memory row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[1] ∧
    air.cols.opcode_selector.is_store row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[2] ∧
    air.cols.opcode_selector.is_beq row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[3] ∧
    air.cols.opcode_selector.is_bne row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[4] ∧
    air.cols.opcode_selector.is_blt row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[5] ∧
    air.cols.opcode_selector.is_bge row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[6] ∧
    air.cols.opcode_selector.is_bltu row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[7] ∧
    air.cols.opcode_selector.is_bgeu row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[8] ∧
    air.cols.opcode_selector.is_jalr row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[9] ∧
    air.cols.opcode_selector.is_jal row 0 =
      (class_selectors_of_opcode (air.cols.instruction.opcode row 0).val)[10]
  := by
    have h := (selector_exclusivity air row h_is_real h_reads).1
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

  /-- What the class-selector table says, read off once for every opcode the decoder produces.
      Entry 1 is `is_memory`, entry 2 `is_store`, entries 3 to 8 the six branch selectors
      (`BLT` and `BGE` at 5 and 6), and entries 0, 9 and 10 `ECALL`, `JALR` and `JAL`.

      - The memory selector is 0 or 1, and 1 only on a load or store opcode.
      - A store opcode sets `is_store` and no branch selector.
      - The six branch selectors add up to 0 or 1; when 1, `is_store` is 0 and `BLT` plus
        `BGE` is 0 or 1.
      - The ten class selectors other than `is_store`, added in the order of constraint 17,
        make 0 or 1, and 0 only on an ALU opcode. -/
  lemma class_selectors_facts (n : ℕ)
      (h_n : n ≤ 25 ∨ n = 28 ∨ (30 ≤ n ∧ n ≤ 37) ∨ (40 ≤ n ∧ n ≤ 52))
  :
    ((class_selectors_of_opcode n)[1] = 0 ∨ (class_selectors_of_opcode n)[1] = 1) ∧
    ((class_selectors_of_opcode n)[1] = 1 → (10 ≤ n ∧ n ≤ 17) ∨ (45 ≤ n ∧ n ≤ 47)) ∧
    ((15 ≤ n ∧ n ≤ 17) ∨ n = 47 →
      (class_selectors_of_opcode n)[2] = 1 ∧
      (class_selectors_of_opcode n)[3] = 0 ∧ (class_selectors_of_opcode n)[4] = 0 ∧
      (class_selectors_of_opcode n)[5] = 0 ∧ (class_selectors_of_opcode n)[6] = 0 ∧
      (class_selectors_of_opcode n)[7] = 0 ∧ (class_selectors_of_opcode n)[8] = 0) ∧
    ((class_selectors_of_opcode n)[3] + (class_selectors_of_opcode n)[4] +
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] +
       (class_selectors_of_opcode n)[7] + (class_selectors_of_opcode n)[8] = 0 ∨
     (class_selectors_of_opcode n)[3] + (class_selectors_of_opcode n)[4] +
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] +
       (class_selectors_of_opcode n)[7] + (class_selectors_of_opcode n)[8] = 1) ∧
    ((class_selectors_of_opcode n)[3] + (class_selectors_of_opcode n)[4] +
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] +
       (class_selectors_of_opcode n)[7] + (class_selectors_of_opcode n)[8] = 1 →
      (class_selectors_of_opcode n)[2] = 0 ∧
      ((class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] = 0 ∨
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] = 1)) ∧
    ((class_selectors_of_opcode n)[3] + (class_selectors_of_opcode n)[4] +
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] +
       (class_selectors_of_opcode n)[7] + (class_selectors_of_opcode n)[8] +
       (class_selectors_of_opcode n)[0] + (class_selectors_of_opcode n)[1] +
       (class_selectors_of_opcode n)[10] + (class_selectors_of_opcode n)[9] = 0 ∨
     (class_selectors_of_opcode n)[3] + (class_selectors_of_opcode n)[4] +
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] +
       (class_selectors_of_opcode n)[7] + (class_selectors_of_opcode n)[8] +
       (class_selectors_of_opcode n)[0] + (class_selectors_of_opcode n)[1] +
       (class_selectors_of_opcode n)[10] + (class_selectors_of_opcode n)[9] = 1) ∧
    ((class_selectors_of_opcode n)[3] + (class_selectors_of_opcode n)[4] +
       (class_selectors_of_opcode n)[5] + (class_selectors_of_opcode n)[6] +
       (class_selectors_of_opcode n)[7] + (class_selectors_of_opcode n)[8] +
       (class_selectors_of_opcode n)[0] + (class_selectors_of_opcode n)[1] +
       (class_selectors_of_opcode n)[10] + (class_selectors_of_opcode n)[9] = 0 →
      n ≤ 9 ∨ (30 ≤ n ∧ n ≤ 37) ∨ (40 ≤ n ∧ n ≤ 44) ∨ (48 ≤ n ∧ n ≤ 52))
  := by
    have h_le : n ≤ 52 := by omega
    interval_cases n <;> first | (exfalso; omega) | decide

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
    have h := selectors_by_opcode air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
    rw [h_class] at h
    simpa using h

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

  /-- The row's packed `U64w` pc is 4-aligned. Only the alignment: that the packed pc is the
      Program table's address needs `pc_facts`' bounds. -/
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
      only the whole-trace assumption bounds. Its alignment part is not used: this lemma gives
      the bounds only, not that the next pc is a multiple of 4. -/
  lemma next_pc_facts
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
  :
    (air.cols.next_pc_0 row 0).val < 65536 ∧
    (air.cols.next_pc_1 row 0).val < 65536 ∧
    (air.cols.next_pc_0 row 0).val + 65536 * (air.cols.next_pc_1 row 0).val < 0x7800_0000
  := by
    obtain ⟨ -, h_pv_lo, h_pv_hi, h_pv_bound ⟩ := pico_assumptions
    have h_cs := h_constraints row h_row
    -- The chunk's final pc: `is_last = 1` pins `next_pc` to public values 43 and 44.
    have h_final :
        air.cols.is_last row 0 = 1 →
        air.cols.next_pc_0 row 0 = air.public_values 43 ∧
        air.cols.next_pc_1 row 0 = air.public_values 44 := by
      intro h_last
      have h_c41 : constraint_41 air row := constraint_at h_cs 41 (by norm_num)
      have h_c42 : constraint_42 air row := constraint_at h_cs 42 (by norm_num)
      simp [constraint_and_interaction_simplification, h_last, sub_eq_zero] at h_c41 h_c42
      exact ⟨ h_c41.symm, h_c42.symm ⟩
    by_cases h_transition : Circuit.isTransitionRow air row = 0
    · -- Last physical row: constraint 51 makes it the last real row.
      have h_c51 : constraint_51 air row := constraint_at h_cs 51 (by norm_num)
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
        have h_c50 : constraint_50 air row := constraint_at h_cs 50 (by norm_num)
        simp [constraint_and_interaction_simplification, h_trans, h_is_real, h_real_next,
              sub_eq_zero] at h_c50
        obtain ⟨ h0, h1 ⟩ := h_final (by simpa using h_c50)
        rw [h0, h1]; exact ⟨ h_pv_lo, h_pv_hi, h_pv_bound ⟩
      · -- An internal row: the next row is real, and its pc is this row's next pc.
        have h_real_next' : air.cols.is_real row 1 = 1 := by
          have h_c44 : constraint_44 air (row + 1) :=
            constraint_at (h_constraints (row + 1) h_row_next) 44 (by norm_num)
          have h_eq : air.cols.is_real row 1 = air.cols.is_real (row + 1) 0 := by
            rw [is_real_rotation]; simp [h_mod]
          rw [h_eq] at h_real_next ⊢
          simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c44
          grind
        have h_c46 : constraint_46 air row := constraint_at h_cs 46 (by norm_num)
        have h_c47 : constraint_47 air row := constraint_at h_cs 47 (by norm_num)
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
    have h_c0 : constraint_0 air row := constraint_at h_constraints 0 (by norm_num)
    have h_c1 : constraint_1 air row := constraint_at h_constraints 1 (by norm_num)
    have h_c2 : constraint_2 air row := constraint_at h_constraints 2 (by norm_num)
    have h_c3 : constraint_3 air row := constraint_at h_constraints 3 (by norm_num)
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
    have h_c4 : constraint_4 air row := constraint_at h_constraints 4 (by norm_num)
    have h_c5 : constraint_5 air row := constraint_at h_constraints 5 (by norm_num)
    have h_c6 : constraint_6 air row := constraint_at h_constraints 6 (by norm_num)
    have h_c7 : constraint_7 air row := constraint_at h_constraints 7 (by norm_num)
    simp [constraint_and_interaction_simplification, h_imm_c, one_mul, sub_eq_zero]
      at h_c4 h_c5 h_c6 h_c7
    exact ⟨ h_c4, h_c5, h_c6, h_c7 ⟩

  -- ============================================================================
  -- Real and padding rows
  -- ============================================================================

  /-- `is_real` is 0 or 1 (constraint 12). -/
  lemma is_real_bool
    [Field ExtF]
    {air : Valid_CpuChip FKB ExtF} {row : ℕ}
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    air.cols.is_real row 0 = 0 ∨ air.cols.is_real row 0 = 1
  := by
    have h_c12 : constraint_12 air row := constraint_at h_constraints 12 (by norm_num)
    simp [constraint_and_interaction_simplification, sub_eq_zero] at h_c12
    exact h_c12

  /-- A padding row sends none of the three messages that ask anything of the sender:
      constraints 55 and 57 to 62 zero the memory and branch selectors, and with them and
      constraints 54, 63 and 64 constraint 17 zeroes `is_alu_not_x0`. -/
  lemma padding_row_silent
    [Field ExtF]
    {air : Valid_CpuChip FKB ExtF} {row : ℕ}
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_pad : air.cols.is_real row 0 = 0)
  :
    air.cols.opcode_selector.is_memory row 0 = 0 ∧
    air.cols.is_alu_not_x0 row 0 = 0 ∧
    air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 0
  := by
    have h_c17 : constraint_17 air row := constraint_at h_constraints 17 (by norm_num)
    have h_c54 : constraint_54 air row := constraint_at h_constraints 54 (by norm_num)
    have h_c55 : constraint_55 air row := constraint_at h_constraints 55 (by norm_num)
    have h_c57 : constraint_57 air row := constraint_at h_constraints 57 (by norm_num)
    have h_c58 : constraint_58 air row := constraint_at h_constraints 58 (by norm_num)
    have h_c59 : constraint_59 air row := constraint_at h_constraints 59 (by norm_num)
    have h_c60 : constraint_60 air row := constraint_at h_constraints 60 (by norm_num)
    have h_c61 : constraint_61 air row := constraint_at h_constraints 61 (by norm_num)
    have h_c62 : constraint_62 air row := constraint_at h_constraints 62 (by norm_num)
    have h_c63 : constraint_63 air row := constraint_at h_constraints 63 (by norm_num)
    have h_c64 : constraint_64 air row := constraint_at h_constraints 64 (by norm_num)
    simp [constraint_and_interaction_simplification, h_pad] at h_c54 h_c55 h_c57 h_c58 h_c59
    simp [constraint_and_interaction_simplification, h_pad] at h_c60 h_c61 h_c62 h_c63 h_c64
    simp [constraint_and_interaction_simplification, h_pad, h_c54, h_c55, h_c57, h_c58, h_c59,
      h_c60, h_c61, h_c62, h_c63, h_c64] at h_c17
    exact ⟨ h_c55, h_c17, by simp [h_c57, h_c58, h_c59, h_c60, h_c61, h_c62] ⟩

  /-- A row that sends a message with multiplicity `m = 1`, where `m` is zero on a padding row,
      is real. -/
  lemma is_real_of_send
    [Field ExtF]
    {air : Valid_CpuChip FKB ExtF} {row : ℕ}
    (h_constraints : CpuChip.Extraction.allHold air row)
    {m : FKB}
    (h_pad : air.cols.is_real row 0 = 0 → m = 0)
    (h_m : m = 1)
  :
    air.cols.is_real row 0 = 1
  := by
    rcases is_real_bool h_constraints with h | h
    · exact absurd (h_m.symm.trans (h_pad h)) one_ne_zero
    · exact h

  -- ============================================================================
  -- Operand ranges
  -- ============================================================================

  /-- The register values a real row reads are 16-bit: `op_a`'s previous value always, `op_b`
      and `op_c` when they are registers. The hypothesis holds only the Program table's and
      the register file's promises, so nothing else can be used. -/
  lemma read_ranges
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
  :
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
    simp [bus_row_reads_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_reads
    grind

  /-- The value a real row writes to `op_a` is 16-bit: the chip's own promise on its write
      message (`bus_row_wf_asrt`). -/
  lemma write_range
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf_asrt : bus_row_wf_asrt (bus_row air row))
  :
    (air.cols.op_a_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_3 row 0).val < 65536
  := by
    simp [bus_row_wf_asrt, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf_asrt
    grind

  /-- Every operand piece the row reads from or writes to the register file is 16-bit: the
      write from `write_range`, the reads from `read_ranges`. The immediate case is in
      `imm_b_eq_1_constraints` / `imm_c_eq_1_constraints` together with the decoder's
      `imm_operand_limbs`, and both cases together in `operand_ranges`. -/
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
  :=
    have h_w := write_range air row h_is_real h_wf_asrt
    have h_r := read_ranges air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
    ⟨ h_w.1, h_w.2.1, h_w.2.2.1, h_w.2.2.2, h_r ⟩

  /-- An operand that is an immediate (flag 1) has 16-bit pieces: two from the instruction
      and a sign fill of 0 or 65535. -/
  lemma immediate_pieces_range {v_0 v_1 v_2 v_3 p_0 p_1 s : FKB}
      (h_0 : v_0 = p_0) (h_1 : v_1 = p_1) (h_2 : v_2 = s * 65535) (h_3 : v_3 = s * 65535)
      (h_p_0 : p_0.val < 65536) (h_p_1 : p_1.val < 65536) (h_s : s = 0 ∨ s = 1)
  :
    v_0.val < 65536 ∧ v_1.val < 65536 ∧ v_2.val < 65536 ∧ v_3.val < 65536
  := by
    subst h_0 h_1 h_2 h_3
    rcases h_s with rfl | rfl <;> simp [h_p_0, h_p_1]

  /-- On a real row both operand values the row sends are 16-bit, whatever their immediate
      flags: a register by `read_ranges`, an immediate by constraints 0 to 7 and the Program
      table's operand facts (`ProgramBusEntry.inversion_operands`). -/
  lemma operand_ranges
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    (air.cols.op_b_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_b_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_b_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_b_access.access.value_3 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_3 row 0).val < 65536
  := by
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ :=
      program_bus_operand_properties_of_reads air row h_is_real h_reads
    have h_ops := ProgramBusEntry.inversion_operands h_trans h_deser
    have h_hot := ProgramBusEntry.inversion_selectors_one_hot h_trans h_deser
    rw [deserialise_program_bus_entry] at h_ops h_hot
    obtain ⟨ -, -, -, -, h_b_0, h_b_1, h_b_s, h_c_0, h_c_1, h_c_s ⟩ := h_ops
    obtain ⟨ h_imm_b, h_imm_c, - ⟩ := h_hot
    obtain ⟨ -, -, -, -, h_read_b, h_read_c ⟩ := read_ranges air row h_is_real h_reads
    have h_b :
        (air.cols.op_b_access.access.value_0 row 0).val < 65536 ∧
        (air.cols.op_b_access.access.value_1 row 0).val < 65536 ∧
        (air.cols.op_b_access.access.value_2 row 0).val < 65536 ∧
        (air.cols.op_b_access.access.value_3 row 0).val < 65536 := by
      rcases h_imm_b with h | h
      · exact h_read_b h
      · obtain ⟨ e_0, e_1, e_2, e_3 ⟩ := imm_b_eq_1_constraints air row h h_constraints
        exact immediate_pieces_range e_0 e_1 e_2 e_3 h_b_0 h_b_1 h_b_s
    have h_c :
        (air.cols.op_c_access.access.value_0 row 0).val < 65536 ∧
        (air.cols.op_c_access.access.value_1 row 0).val < 65536 ∧
        (air.cols.op_c_access.access.value_2 row 0).val < 65536 ∧
        (air.cols.op_c_access.access.value_3 row 0).val < 65536 := by
      rcases h_imm_c with h | h
      · exact h_read_c h
      · obtain ⟨ e_0, e_1, e_2, e_3 ⟩ := imm_c_eq_1_constraints air row h h_constraints
        exact immediate_pieces_range e_0 e_1 e_2 e_3 h_c_0 h_c_1 h_c_s
    exact ⟨ h_b.1, h_b.2.1, h_b.2.2.1, h_b.2.2.2, h_c.1, h_c.2.1, h_c.2.2.1, h_c.2.2.2 ⟩

  /-- On a branch or store row `op_a` keeps the value read (constraints 13 to 16), so its four
      pieces are 16-bit. -/
  lemma op_a_kept_range
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_gate : air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 +
      air.cols.opcode_selector.is_store row 0 = 1)
  :
    (air.cols.op_a_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_a_access.access.value_3 row 0).val < 65536
  := by
    obtain ⟨ h_p_0, h_p_1, h_p_2, h_p_3, -, - ⟩ := read_ranges air row h_is_real h_reads
    have h_c13 : constraint_13 air row := constraint_at h_constraints 13 (by norm_num)
    have h_c14 : constraint_14 air row := constraint_at h_constraints 14 (by norm_num)
    have h_c15 : constraint_15 air row := constraint_at h_constraints 15 (by norm_num)
    have h_c16 : constraint_16 air row := constraint_at h_constraints 16 (by norm_num)
    simp only [constraint_and_interaction_simplification, h_gate, one_mul, sub_eq_zero]
      at h_c13 h_c14 h_c15 h_c16
    rw [h_c13, h_c14, h_c15, h_c16]
    exact ⟨ h_p_0, h_p_1, h_p_2, h_p_3 ⟩

  /-- With `op_a_is_x0` set the four pieces of `op_a` are zero (constraints 8 to 11,
      `register/constraints.rs:73-76`). `op_a` is the instruction's first register field: the
      destination of a load or an ALU instruction, the source register of a store. -/
  lemma op_a_zero_of_x0
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_x0 : ¬ air.cols.instruction.op_a_is_x0 row 0 = 0)
  :
    air.cols.op_a_access.access.value_0 row 0 = 0 ∧
    air.cols.op_a_access.access.value_1 row 0 = 0 ∧
    air.cols.op_a_access.access.value_2 row 0 = 0 ∧
    air.cols.op_a_access.access.value_3 row 0 = 0
  := by
    have h_c8 : constraint_8 air row := constraint_at h_constraints 8 (by norm_num)
    have h_c9 : constraint_9 air row := constraint_at h_constraints 9 (by norm_num)
    have h_c10 : constraint_10 air row := constraint_at h_constraints 10 (by norm_num)
    have h_c11 : constraint_11 air row := constraint_at h_constraints 11 (by norm_num)
    simp [constraint_and_interaction_simplification, h_x0] at h_c8 h_c9 h_c10 h_c11
    exact ⟨ h_c8, h_c9, h_c10, h_c11 ⟩

  -- ============================================================================
  -- Sequential rows
  -- ============================================================================

  /-- Pure arithmetic: if two two-piece addresses inside the guest address space satisfy the
      field equation of constraint 37 (the second is the first plus four), they satisfy the
      64-bit addition. One direction only. No chip dependencies. -/
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
    have h_c31 : constraint_31 air row := constraint_at h_constraints 31 (by norm_num)
    simp [constraint_and_interaction_simplification, h_no_ecall] at h_c31
    exact h_c31

  /-- A row of an instruction outside the branch and jump classes, not a halt, advances the pc
      by four: constraint 37's gate is `is_real` and its field equation reads as a 64-bit
      addition once the pc and next-pc pieces are bounded. `pc_facts` and `next_pc_facts`
      supply the bounds, so this lemma inherits the whole-trace assumption.

      It needs all six branch selectors to be zero, so it does not cover a branch row whose
      branch is not taken, even though constraint 37 moves that row on by four as well; the
      branch theorems need their own not-taken lemma. -/
  lemma is_sequential_active_constraints
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
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
    have h_c37 : constraint_37 air row := constraint_at (h_constraints row h_row) 37 (by norm_num)
    simp [constraint_and_interaction_simplification, h_is_real, h_beq, h_bne, h_blt, h_bge,
          h_bltu, h_bgeu, h_no_jal, h_no_jalr, h_no_halt, sub_eq_zero] at h_c37
    -- `h_c37` is the field equation `next_pc_0 + 65536 * next_pc_1 = pc_0 + 65536 * pc_1 + 4`.
    obtain ⟨ h_pc_0, h_pc_1, _, h_pc_bound, _ ⟩ := pc_facts air row h_is_real (h_wf row h_row)
    obtain ⟨ h_np_0, h_np_1, h_np_bound ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    simp only [next_pc, pc]
    exact two_piece_plus_four_implies_sum _ _ _ _ h_pc_0 (by omega) h_np_0 h_np_1
      (by omega) h_np_bound (by linear_combination h_c37)

  -- ============================================================================
  -- ALU rows: the destination register and the ALU message
  -- ============================================================================

  /-- `op_a_is_x0` is `[op_a = 0]`: the Program table writes it so for every instruction. -/
  lemma op_a_is_x0_eq
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
  :
    air.cols.instruction.op_a_is_x0 row 0 =
      if air.cols.instruction.op_a row 0 = 0 then 1 else 0
  := by
    have h_prog := program_bus_operand_properties_of_reads air row h_is_real h_reads
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ := h_prog
    have h := (ProgramBusEntry.inversion_operands h_trans h_deser).2.1
    rw [deserialise_program_bus_entry] at h
    simpa using h

  /-- On a real row with no class selector set, the ALU message's multiplicity
      `is_alu_not_x0` is 1 when the destination is not `x0` and 0 when it is
      (constraint 17). The v3.1.1 chip sends no ALU message for a write to `x0`. -/
  lemma is_alu_not_x0_eq
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_class : class_selectors_of_opcode (air.cols.instruction.opcode row 0).val =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  :
    air.cols.is_alu_not_x0 row 0 = if air.cols.instruction.op_a row 0 = 0 then 0 else 1
  := by
    obtain ⟨ h_ecall, h_mem, -, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_jalr, h_jal ⟩ :=
      alu_class_selectors_zero air row h_is_real h_wf h_class
    have h_c17 : constraint_17 air row := constraint_at h_constraints 17 (by norm_num)
    simp [constraint_and_interaction_simplification, h_is_real, h_beq, h_bne, h_blt, h_bge,
          h_bltu, h_bgeu, h_ecall, h_mem, h_jal, h_jalr, sub_eq_zero] at h_c17
    rw [h_c17, op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
    split_ifs <;> simp

  /-- On a real ALU-class row whose destination is not `x0`, the chip sends its ALU message
      with multiplicity 1, so the ALU chip's promise `ALUBus.Spec` holds for the row's opcode,
      result (`op_a`) and operands (`op_b`, `op_c`). A row whose destination is `x0` sends no
      ALU message; its instruction theorem cancels the two writes to `x0` instead
      (`operation_list_effect_state_writeReg_x0`). -/
  lemma alu_message_spec
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_class : class_selectors_of_opcode (air.cols.instruction.opcode row 0).val =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    (h_rd : air.cols.instruction.op_a row 0 ≠ 0)
  :
    RV64IM_Interactions.ALUBus.Spec (air.cols.instruction.opcode row 0)
      (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
      (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
      (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
      (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
      (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
      (air.cols.op_c_access.access.value_2 row 0) (air.cols.op_c_access.access.value_3 row 0)
  := by
    have h_alu := is_alu_not_x0_eq air row h_is_real h_wf h_constraints h_class
    rw [if_neg h_rd] at h_alu
    have h := h_wf
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h
    exact h.2.1 (by simp [h_alu])

end CpuChip.Interpretations
