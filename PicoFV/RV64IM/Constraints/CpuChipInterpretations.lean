import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.RVSail.BusesV3

open Plonky3

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 2_000_000
set_option linter.constructorNameAsVariable false

/-!
# CpuChip interpretations (RV64, Pico v3.1.1)

Readable facts about one row of the v3.1.1 `CpuChip`, derived from the restated constraints of
`Constraints/CpuChip.lean` and the bus contracts of `RVSail/BusesV3.lean`: first what every
instruction class needs, then what one class does — the branch and jump targets, the JALR
addition, the comparison message and the memory dispatch. Pico line numbers are at v3.1.1
(`2acc7c1828fb`).

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
- **The branch and JAL targets** are single field equations too (constraints 19 and 24), with
  the sign-extended offset folded into one subtraction of `2^32`. Reading one as a 64-bit
  addition needs a bound on the offset as well, which the decoder gives the instruction
  theorem, so `two_piece_plus_offset_implies_sum` takes it as a hypothesis.
- **The two additions the chip still proves limb by limb** are the jump return address and
  the JALR target. The return address `op_a = pc + 4` (constraints 20 to 23) carries through
  `pc_carry`, which the Program table defines. The JALR target `op_b + op_c = next_pc +
  jalr_lsb` (constraints 27 to 30) has four carries that are expressions rather than columns;
  `next_pc`'s 4-alignment is what both bounds its low limb and clears bit 0 of the target.
- **Which promises a lemma assumes.** A lemma that needs only the Program table's promise or
  the register file's takes `bus_row_reads_asm`, that part of `bus_row_wf_asm`; the sender
  theorem `CpuChip.Spec.ext_asrt` can then use it without assuming the promises of the chips
  it sends to. A caller holding `bus_row_wf_asm` passes `bus_row_reads_asm_of_wf_asm h_wf`.

Names are the 2.x ones wherever the statement means the same, so the instruction-theorem files
have less to rewrite. A lemma whose statement changed has a new name, so that a 2.x caller fails
loudly rather than against a different statement:

| 2.x lemma | v3.1.1 replacement |
|-----------|--------------------|
| `pc_next_pc_u16_bounds` | `pc_facts`, `next_pc_facts` |
| `branching_next_pc_eq_pc_plus_op_c` | `branch_taken_next_pc` |
| `jal_next_pc_eq_pc_plus_op_b` | `jal_next_pc` |
| `op_a_eq_pc_plus_four_of_pc_carry_a_chain` | `jump_return_address` |
| `jalr_next_pc_plus_specific_eq_op_b_plus_op_c` | `jalr_sum`, `jalr_target` |
| `branch_instruction_a_lt_b`, `branch_instruction_a_gt_b` | `branch_compare_spec` |
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
      only the whole-trace assumption bounds.

      The alignment comes from the same two places — a Program-table address is 4-aligned, and
      the assumption says the chunk's final pc is — so this is where the 2.x
      `Equivalence.next_pc_mod_four_eq_zero` ends up. In 2.x it had to split over every
      instruction class, because each class had its own cross-row constraint; in v3.1.1
      constraints 46 and 47 hold whatever the row does. -/
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
    (air.cols.next_pc_0 row 0).val + 65536 * (air.cols.next_pc_1 row 0).val < 0x7800_0000 ∧
    (air.cols.next_pc_0 row 0).val % 4 = 0
  := by
    obtain ⟨ h_pv_al, h_pv_lo, h_pv_hi, h_pv_bound ⟩ := pico_assumptions
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
      rw [h0, h1]; exact ⟨ h_pv_lo, h_pv_hi, h_pv_bound, h_pv_al ⟩
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
        rw [h0, h1]; exact ⟨ h_pv_lo, h_pv_hi, h_pv_bound, h_pv_al ⟩
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
        exact ⟨ h_pc_next.1, by omega, h_pc_next.2.2.2.1, h_pc_next.2.2.1 ⟩

  /-- A real row's next pc is 4-aligned: the alignment part of `next_pc_facts`, as the low
      piece and as the whole value. This is the 2.x `Equivalence.next_pc_mod_four_eq_zero`,
      which `equivalence_JAL` and the parked branches call. Against 2.x it takes the arguments in
      this file's order (`air row h_row h_is_real h_wf h_constraints pico_assumptions`), drops
      the Program-bus axioms, and adds the whole-value conjunct. -/
  lemma next_pc_mod_four_eq_zero
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
  :
    (air.cols.next_pc_0 row 0).val % 4 = 0 ∧ U64w.toNat (next_pc air row) % 4 = 0
  := by
    obtain ⟨ h_0, h_1, -, h_al ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    refine ⟨ h_al, ?_ ⟩
    simp [next_pc, U64w.toNat]
    omega

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

  /-- The Program table's operand pieces: both halves of each immediate are 16-bit and each
      sign is 0 or 1 (`ProgramBusEntry.inversion_operands`). -/
  lemma instruction_operand_facts
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_reads : bus_row_reads_asm (bus_row air row))
  :
    (air.cols.instruction.op_b_0 row 0).val < 65536 ∧
    (air.cols.instruction.op_b_1 row 0).val < 65536 ∧
    (air.cols.instruction.op_b_sign row 0 = 0 ∨ air.cols.instruction.op_b_sign row 0 = 1) ∧
    (air.cols.instruction.op_c_0 row 0).val < 65536 ∧
    (air.cols.instruction.op_c_1 row 0).val < 65536 ∧
    (air.cols.instruction.op_c_sign row 0 = 0 ∨ air.cols.instruction.op_c_sign row 0 = 1)
  := by
    obtain ⟨ instr, pc', data, props, -, -, h_trans, h_deser, - ⟩ :=
      program_bus_operand_properties_of_reads air row h_is_real h_reads
    have h := ProgramBusEntry.inversion_operands h_trans h_deser
    rw [deserialise_program_bus_entry] at h
    obtain ⟨ -, -, -, -, h_b_0, h_b_1, h_b_s, h_c_0, h_c_1, h_c_s ⟩ := h
    simpa using ⟨ h_b_0, h_b_1, h_b_s, h_c_0, h_c_1, h_c_s ⟩

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
    obtain ⟨ instr, pc', data, props, -, -, h_trans, h_deser, - ⟩ :=
      program_bus_operand_properties_of_reads air row h_is_real h_reads
    have h_hot := ProgramBusEntry.inversion_selectors_one_hot h_trans h_deser
    rw [deserialise_program_bus_entry] at h_hot
    obtain ⟨ h_imm_b, h_imm_c, - ⟩ := h_hot
    obtain ⟨ h_b_0, h_b_1, h_b_s, h_c_0, h_c_1, h_c_s ⟩ :=
      instruction_operand_facts air row h_is_real h_reads
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

  /-- On a branch or store row `op_a` keeps the value it read (constraints 13 to 16,
      `register/constraints.rs:117-123`): the row writes the register back unchanged. The
      store theorems read the stored value off this. -/
  lemma op_a_kept
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_gate : air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 +
      air.cols.opcode_selector.is_store row 0 = 1)
  :
    air.cols.op_a_access.access.value_0 row 0 = air.cols.op_a_access.prev_value_0 row 0 ∧
    air.cols.op_a_access.access.value_1 row 0 = air.cols.op_a_access.prev_value_1 row 0 ∧
    air.cols.op_a_access.access.value_2 row 0 = air.cols.op_a_access.prev_value_2 row 0 ∧
    air.cols.op_a_access.access.value_3 row 0 = air.cols.op_a_access.prev_value_3 row 0
  := by
    have h_c13 : constraint_13 air row := constraint_at h_constraints 13 (by norm_num)
    have h_c14 : constraint_14 air row := constraint_at h_constraints 14 (by norm_num)
    have h_c15 : constraint_15 air row := constraint_at h_constraints 15 (by norm_num)
    have h_c16 : constraint_16 air row := constraint_at h_constraints 16 (by norm_num)
    simp only [constraint_and_interaction_simplification, h_gate, one_mul, sub_eq_zero]
      at h_c13 h_c14 h_c15 h_c16
    exact ⟨ h_c13, h_c14, h_c15, h_c16 ⟩

  /-- The value a branch or store row's `op_a` keeps is 16-bit, since it is the value read. -/
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
    obtain ⟨ h_c13, h_c14, h_c15, h_c16 ⟩ := op_a_kept air row h_constraints h_gate
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
  -- Sequential rows and branches not taken
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

  /-- The branch-taken predicate, the gate of constraints 19 and 37
      (`branch_taken_expr`, `riscv_cpu/constraints.rs:344-363`). v3.1.1 commits no column for
      it: `a_eq_b` is `1 - a_lt_b - a_gt_b`, and the column the 2.x `branching` used became
      `is_last`. -/
  def branch_taken {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : FKB :=
    air.cols.opcode_selector.is_beq row 0 *
        (1 - air.cols.a_lt_b row 0 - air.cols.a_gt_b row 0) +
      air.cols.opcode_selector.is_bne row 0 *
        (air.cols.a_lt_b row 0 + air.cols.a_gt_b row 0) +
      (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bltu row 0) *
        air.cols.a_lt_b row 0 +
      (air.cols.opcode_selector.is_bge row 0 + air.cols.opcode_selector.is_bgeu row 0) *
        (1 - air.cols.a_lt_b row 0)

  /-- A branch row whose branch is not taken moves on by four, like a sequential row: the gate
      of constraint 37 is `is_real` minus the taken predicate and the two jump selectors and
      the halt flag. -/
  lemma branch_not_taken_next_pc
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
    (h_not_taken : branch_taken air row = 0)
    (h_no_jal : air.cols.opcode_selector.is_jal row 0 = 0)
    (h_no_jalr : air.cols.opcode_selector.is_jalr row 0 = 0)
    (h_no_halt : air.cols.is_halt row 0 = 0)
  :
    U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64
  := by
    have h_cs := h_constraints row h_row
    have h_c37 : constraint_37 air row := constraint_at h_cs 37 (by norm_num)
    obtain ⟨ h_pc_0, h_pc_1, -, h_pc_bound, - ⟩ := pc_facts air row h_is_real (h_wf row h_row)
    obtain ⟨ h_np_0, h_np_1, h_np_bound, - ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    have h_pc_1' : (air.cols.pc_1 row 0).val < 65536 := Nat.lt_of_le_of_lt h_pc_1 (by norm_num)
    rcases mul_eq_zero.mp h_c37 with h_gate | h_eq
    · have h_one : air.cols.is_real row 0 - branch_taken air row -
          air.cols.opcode_selector.is_jal row 0 - air.cols.opcode_selector.is_jalr row 0 -
          air.cols.is_halt row 0 = 1 := by
        rw [h_is_real, h_not_taken, h_no_jal, h_no_jalr, h_no_halt]; ring
      exact absurd (h_one.symm.trans h_gate) one_ne_zero
    · rw [sub_eq_zero] at h_eq
      simp only [next_pc, pc]
      exact two_piece_plus_four_implies_sum _ _ _ _ h_pc_0 h_pc_1' h_np_0 h_np_1
        h_pc_bound h_np_bound h_eq

  /-- A row of an instruction outside the branch and jump classes, not a halt, advances the pc
      by four: constraint 37's gate is `is_real` and its field equation reads as a 64-bit
      addition once the pc and next-pc pieces are bounded. `pc_facts` and `next_pc_facts`
      supply the bounds, so this lemma inherits the whole-trace assumption.

      With all six branch selectors zero the taken predicate is zero, so this is
      `branch_not_taken_next_pc` on a row with no branch selector at all. -/
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
    exact branch_not_taken_next_pc air row h_row h_is_real h_wf h_constraints pico_assumptions
      (by simp [branch_taken, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu]) h_no_jal h_no_jalr
      h_no_halt

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

  /-- The receivers' promises for the three dispatch messages a real row can send, from one
      unfolding of `bus_row_wf_asm`: the ALU message (multiplicity `is_alu_not_x0`), the
      branch comparison (multiplicity the sum of the six branch selectors, opcode 264 for
      `BLT` and `BGE` and 265 otherwise) and the memory dispatch (multiplicity `is_memory`).
      `alu_message_spec`, `branch_compare_spec` and `memory_message_spec` read their part. -/
  lemma dispatch_specs
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    (air.cols.is_alu_not_x0 row 0 = 1 →
      RV64IM_Interactions.ALUBus.Spec (air.cols.instruction.opcode row 0)
        (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
        (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
        (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
        (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
        (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
        (air.cols.op_c_access.access.value_2 row 0)
        (air.cols.op_c_access.access.value_3 row 0)) ∧
    (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1 →
      RV64IM_Interactions.ALUBus.Spec
        ((air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0) * 8 +
          (1 - (air.cols.opcode_selector.is_blt row 0 +
            air.cols.opcode_selector.is_bge row 0)) * 9 + 256)
        (air.cols.a_lt_b row 0) (air.cols.a_gt_b row 0) 0 0
        (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
        (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
        (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
        (air.cols.op_b_access.access.value_2 row 0)
        (air.cols.op_b_access.access.value_3 row 0)) ∧
    (air.cols.opcode_selector.is_memory row 0 = 1 →
      MemoryBus.Spec (air.cols.instruction.opcode row 0)
        (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
        (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
        (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
        (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
        (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
        (air.cols.op_c_access.access.value_2 row 0) (air.cols.op_c_access.access.value_3 row 0)
        (air.cols.instruction.op_a_is_x0 row 0))
  := by
    have h := h_wf
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h
    -- The Program message, the ALU message, the comparison, then the six Byte checks, the
    -- four register-read ranges and the old `op_a` range, then the memory dispatch.
    obtain ⟨ -, h_alu, h_cmp, -, -, -, -, -, -, -, -, -, -, -, h_mem ⟩ := h
    exact ⟨ h_alu, h_cmp, h_mem ⟩

  /-- The ALU chip's specification `ALUBus.Spec` for opcode `op`, applied to the row's twelve
      operand columns: the result `op_a` and the operands `op_b` and `op_c`. -/
  def alu_spec_of_row {ExtF : Type} [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : FKB) : Prop :=
    RV64IM_Interactions.ALUBus.Spec op
      (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
      (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
      (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
      (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
      (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
      (air.cols.op_c_access.access.value_2 row 0) (air.cols.op_c_access.access.value_3 row 0)

  /-- On a real ALU-class row whose destination is not `x0`, the chip sends its ALU message
      with multiplicity 1, so the ALU chip's promise holds for the row's opcode, result
      (`op_a`) and operands (`op_b`, `op_c`): `alu_spec_of_row`. A row whose destination is
      `x0` sends no ALU message; its instruction theorem cancels the two writes to `x0` instead
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
    alu_spec_of_row air row (air.cols.instruction.opcode row 0)
  := by
    have h_alu := is_alu_not_x0_eq air row h_is_real h_wf h_constraints h_class
    rw [if_neg h_rd] at h_alu
    exact (dispatch_specs air row h_is_real h_wf).1 h_alu

  -- ============================================================================
  -- Branch and jump targets
  -- ============================================================================

  /-- A branch's 13-bit offset and a JAL's 21-bit one stay inside `2^20` of zero, so the two
      low pieces of the decoder's sign-extended operand are at most `0x10_0000` when its sign
      is 0 and at least `2^32 - 0x10_0000` when it is 1. This is the bound the target lemmas
      below take as a hypothesis, and this is what a branch or jump theorem discharges it
      with, from the immediate its Program message was decoded from. -/
  lemma imm_operand_offset_bounds {w : ℕ} (hw0 : 0 < w) (hw : w ≤ 21) (imm : BitVec w) :
      ((Transpiler.V3.imm_operand imm true)[2] = 0 →
        (Transpiler.V3.imm_operand imm true)[0].val +
          65536 * (Transpiler.V3.imm_operand imm true)[1].val ≤ 0x10_0000) ∧
      ((Transpiler.V3.imm_operand imm true)[2] = 1 →
        0x1_0000_0000 - 0x10_0000 ≤ (Transpiler.V3.imm_operand imm true)[0].val +
          65536 * (Transpiler.V3.imm_operand imm true)[1].val)
  := by
    obtain ⟨ h_0, h_1, h_s ⟩ := Transpiler.V3.imm_operand_sext imm hw0 (by omega)
    simp only at h_0 h_1 h_s
    have h_lt : imm.toNat < 2 ^ w := imm.isLt
    have h_pow : 2 ^ w ≤ 2 ^ 21 := Nat.pow_le_pow_right (by norm_num) hw
    have h_half : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have h_sx_lt : (BitVec.signExtend 64 imm).toNat < 2 ^ 64 := (BitVec.signExtend 64 imm).isLt
    -- The sign-extended value is the immediate, or the immediate `2 ^ w` below `2 ^ 64`.
    have h_sx : (BitVec.signExtend 64 imm).toNat =
        imm.toNat + if 2 ^ (w - 1) ≤ imm.toNat then 2 ^ 64 - 2 ^ w else 0 := by
      simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide,
        decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
    have h_key : (BitVec.signExtend 64 imm).toNat < 2 ^ 20 ∨
        2 ^ 64 - 2 ^ 20 ≤ (BitVec.signExtend 64 imm).toNat := by
      rcases Nat.lt_or_ge imm.toNat (2 ^ (w - 1)) with h | h
      · left; rw [h_sx, if_neg (by omega)]; omega
      · right; rw [h_sx, if_pos h]; omega
    rw [h_0, h_1]
    rcases h_s with ⟨ h_o2, h_bound ⟩ | ⟨ h_o2, h_low, - ⟩
    · exact ⟨ fun _ => by omega, fun h => by rw [h_o2] at h; exact absurd h (by decide) ⟩
    · exact ⟨ fun h => by rw [h_o2] at h; exact absurd h (by decide), fun _ => by omega ⟩

  /-- The branch and jump target equations, read over the integers: the single field equation
      of constraint 19 (a taken branch) or 24 (a JAL) is the 64-bit addition of the
      sign-extended offset. What makes the field arithmetic exact is the offset's size, so the
      caller passes that in: `0x10_0000` covers a branch's 13-bit offset and a JAL's 21-bit
      one, and the largest of those plus the address bound stays below the prime. -/
  lemma two_piece_plus_offset_implies_sum
    (p_0 p_1 n_0 n_1 d_0 d_1 d_2 d_3 s : FKB)
    (h_p_0 : p_0.val < 65536) (h_p_1 : p_1.val < 65536)
    (h_n_0 : n_0.val < 65536) (h_n_1 : n_1.val < 65536)
    (h_p_bound : p_0.val + 65536 * p_1.val < 0x7800_0000)
    (h_n_bound : n_0.val + 65536 * n_1.val < 0x7800_0000)
    (h_d_0 : d_0.val < 65536) (h_d_1 : d_1.val < 65536)
    (h_forward : s = 0 → d_0.val + 65536 * d_1.val ≤ 0x10_0000)
    (h_backward : s = 1 → 0x1_0000_0000 - 0x10_0000 ≤ d_0.val + 65536 * d_1.val)
    (h_s : s = 0 ∨ s = 1)
    (h_d_2 : d_2 = s * 65535) (h_d_3 : d_3 = s * 65535)
    (h_eq : 1 * n_0 + 65536 * n_1 = 1 * p_0 + 65536 * p_1 + d_0 + d_1 * 65536 - s * 33554430)
  :
    U64w.toBV #v[n_0, n_1, 0#16, 0#16] =
      U64w.toBV #v[p_0, p_1, 0#16, 0#16] + U64w.toBV #v[d_0, d_1, d_2, d_3]
  := by
    subst h_d_2 h_d_3
    rcases h_s with rfl | rfl
    · simp only [zero_mul, sub_zero] at h_eq
      have h_d := h_forward rfl
      simp [← BitVec.toNat_inj, U64w.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    · have h_d := h_backward rfl
      simp [← BitVec.toNat_inj, U64w.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind

  /-- A taken branch's next pc is `pc + offset`, the sign-extended `op_c` (constraint 19); a
      branch's `op_c` is always its immediate (constraint 18). The offset bound is the
      caller's, stated on the instruction's own `op_c` pieces: `imm_operand_offset_bounds`
      gives it from the 13-bit immediate the row was decoded from. -/
  lemma branch_taken_next_pc
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
    (h_branch_sum :
      air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1)
    (h_taken : branch_taken air row = 1)
    (h_forward : air.cols.instruction.op_c_sign row 0 = 0 →
      (air.cols.instruction.op_c_0 row 0).val +
        65536 * (air.cols.instruction.op_c_1 row 0).val ≤ 0x10_0000)
    (h_backward : air.cols.instruction.op_c_sign row 0 = 1 →
      0x1_0000_0000 - 0x10_0000 ≤ (air.cols.instruction.op_c_0 row 0).val +
        65536 * (air.cols.instruction.op_c_1 row 0).val)
  :
    U64w.toBV (next_pc air row) =
      U64w.toBV (pc air row) +
      U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                    air.cols.op_c_access.access.value_1 row 0,
                    air.cols.op_c_access.access.value_2 row 0,
                    air.cols.op_c_access.access.value_3 row 0 ]
  := by
    have h_cs := h_constraints row h_row
    have h_wf_row := h_wf row h_row
    have h_c18 : constraint_18 air row := constraint_at h_cs 18 (by norm_num)
    simp only [constraint_and_interaction_simplification, h_branch_sum, one_mul,
      sub_eq_zero] at h_c18
    have h_c19 : constraint_19 air row := constraint_at h_cs 19 (by norm_num)
    obtain ⟨ e_0, e_1, e_2, e_3 ⟩ := imm_c_eq_1_constraints air row h_c18.symm h_cs
    obtain ⟨ h_pc_0, h_pc_1, -, h_pc_bound, - ⟩ := pc_facts air row h_is_real h_wf_row
    obtain ⟨ h_np_0, h_np_1, h_np_bound, - ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    obtain ⟨ -, -, -, -, h_d_0, h_d_1, -, - ⟩ :=
      operand_ranges air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf_row) h_cs
    obtain ⟨ -, -, -, -, -, h_sign ⟩ :=
      instruction_operand_facts air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf_row)
    have h_pc_1' : (air.cols.pc_1 row 0).val < 65536 := Nat.lt_of_le_of_lt h_pc_1 (by norm_num)
    rcases mul_eq_zero.mp h_c19 with h_gate | h_eq
    · exact absurd (h_taken.symm.trans h_gate) one_ne_zero
    · rw [sub_eq_zero] at h_eq
      simp only [next_pc, pc]
      exact two_piece_plus_offset_implies_sum _ _ _ _ _ _ _ _ _ h_pc_0 h_pc_1' h_np_0 h_np_1
        h_pc_bound h_np_bound h_d_0 h_d_1 (by rw [e_0, e_1]; exact h_forward)
        (by rw [e_0, e_1]; exact h_backward) h_sign e_2 e_3 h_eq

  /-- A JAL row's next pc is `pc + offset`, the sign-extended `op_b` (constraint 24), and its
      `op_b` is an immediate (constraint 25). The offset bound is the caller's, stated on the
      instruction's own `op_b` pieces: `imm_operand_offset_bounds` gives it from the 21-bit
      immediate the row was decoded from. -/
  lemma jal_next_pc
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
    (h_is_jal : air.cols.opcode_selector.is_jal row 0 = 1)
    (h_forward : air.cols.instruction.op_b_sign row 0 = 0 →
      (air.cols.instruction.op_b_0 row 0).val +
        65536 * (air.cols.instruction.op_b_1 row 0).val ≤ 0x10_0000)
    (h_backward : air.cols.instruction.op_b_sign row 0 = 1 →
      0x1_0000_0000 - 0x10_0000 ≤ (air.cols.instruction.op_b_0 row 0).val +
        65536 * (air.cols.instruction.op_b_1 row 0).val)
  :
    air.cols.opcode_selector.imm_b row 0 = 1 ∧
    U64w.toBV (next_pc air row) =
      U64w.toBV (pc air row) +
      U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                    air.cols.op_b_access.access.value_1 row 0,
                    air.cols.op_b_access.access.value_2 row 0,
                    air.cols.op_b_access.access.value_3 row 0 ]
  := by
    have h_cs := h_constraints row h_row
    have h_wf_row := h_wf row h_row
    have h_c24 : constraint_24 air row := constraint_at h_cs 24 (by norm_num)
    have h_c25 : constraint_25 air row := constraint_at h_cs 25 (by norm_num)
    simp [constraint_and_interaction_simplification, h_is_jal, sub_eq_zero] at h_c25
    obtain ⟨ e_0, e_1, e_2, e_3 ⟩ := imm_b_eq_1_constraints air row h_c25.symm h_cs
    obtain ⟨ h_pc_0, h_pc_1, -, h_pc_bound, - ⟩ := pc_facts air row h_is_real h_wf_row
    obtain ⟨ h_np_0, h_np_1, h_np_bound, - ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    obtain ⟨ h_d_0, h_d_1, -, -, -, -, -, - ⟩ :=
      operand_ranges air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf_row) h_cs
    obtain ⟨ -, -, h_sign, -, -, - ⟩ :=
      instruction_operand_facts air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf_row)
    have h_pc_1' : (air.cols.pc_1 row 0).val < 65536 := Nat.lt_of_le_of_lt h_pc_1 (by norm_num)
    refine ⟨ h_c25.symm, ?_ ⟩
    rcases mul_eq_zero.mp h_c24 with h_gate | h_eq
    · exact absurd (h_is_jal.symm.trans h_gate) one_ne_zero
    · rw [sub_eq_zero] at h_eq
      simp only [next_pc, pc]
      exact two_piece_plus_offset_implies_sum _ _ _ _ _ _ _ _ _ h_pc_0 h_pc_1' h_np_0 h_np_1
        h_pc_bound h_np_bound h_d_0 h_d_1 (by rw [e_0, e_1]; exact h_forward)
        (by rw [e_0, e_1]; exact h_backward) h_sign e_2 e_3 h_eq

  -- ============================================================================
  -- Jump rows: the return address
  -- ============================================================================

  /-- On a jump row that writes a register, `op_a` is `pc + 4` (constraints 20 to 23, the
      `Pc::add_limb_with_carry` gadget of `jump/constraints.rs:29-46`). `pc_carry` is the
      Program table's `[pc[0] >= 0xFFFC]`, and a table address is 4-aligned, so the carry is
      taken exactly when the low piece is `0xFFFC`. -/
  lemma jump_return_address
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_jump : air.cols.opcode_selector.is_jal row 0 + air.cols.opcode_selector.is_jalr row 0 = 1)
    (h_not_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0)
  :
    U64w.toBV #v[ air.cols.op_a_access.access.value_0 row 0,
                  air.cols.op_a_access.access.value_1 row 0,
                  air.cols.op_a_access.access.value_2 row 0,
                  air.cols.op_a_access.access.value_3 row 0 ] =
      U64w.toBV (pc air row) + 4#64
  := by
    have h_c20 : constraint_20 air row := constraint_at h_constraints 20 (by norm_num)
    have h_c21 : constraint_21 air row := constraint_at h_constraints 21 (by norm_num)
    have h_c22 : constraint_22 air row := constraint_at h_constraints 22 (by norm_num)
    have h_c23 : constraint_23 air row := constraint_at h_constraints 23 (by norm_num)
    simp [constraint_and_interaction_simplification, h_jump, h_not_x0, sub_eq_zero]
      at h_c20 h_c21 h_c22 h_c23
    obtain ⟨ h_pc_0, h_pc_1, h_al, h_bound, h_carry ⟩ := pc_facts air row h_is_real h_wf
    have e_0 : (air.cols.op_a_access.access.value_0 row 0).val =
        ((air.cols.pc_0 row 0).val + 4) % 65536 ∧
        (air.cols.op_a_access.access.value_1 row 0).val =
          (air.cols.pc_1 row 0).val + ((air.cols.pc_0 row 0).val + 4) / 65536 := by
      rw [h_carry] at h_c20 h_c21
      split_ifs at h_c20 h_c21 with h_big
      · -- The low piece is `0xFFFC`, the only 4-aligned value at or above it.
        have h_eq : (air.cols.pc_0 row 0).val = 65532 := by omega
        exact ⟨ by clear * - h_c20 h_eq; grind, by clear * - h_c21 h_eq h_pc_1; grind ⟩
      · exact ⟨ by clear * - h_c20 h_big h_pc_0 h_al; grind,
                by clear * - h_c21 h_big h_pc_0 h_al h_pc_1; grind ⟩
    obtain ⟨ e_0, e_1 ⟩ := e_0
    simp [pc, ← BitVec.toNat_inj, U64w.toNat, h_c22, h_c23, e_0, e_1]
    omega

  -- ============================================================================
  -- JALR: the four-carry addition and the cleared low bit
  -- ============================================================================

  /-- `inv(2^16)` in KoalaBear, the factor the extracted carries carry. -/
  lemma inv_65536 : (2130673921 : FKB) * 65536 = 1 := by decide

  /-- A carry the extraction writes as `e * inv(2^16)` is `e / 2^16`. -/
  lemma carry_mul_65536 {k e : FKB} (h : k = e * 2130673921) : e = k * 65536 := by
    rw [h, mul_assoc, inv_65536, mul_one]

  /-- Four boolean carries make the schoolbook 64-bit sum `b + c = next_pc + lsb`, whose third
      and fourth limbs are zero: a target at or above `2^32` has no witness. -/
  lemma four_limb_carry_sum
    (b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 n_0 n_1 m_0 lsb k_1 k_2 k_3 k_4 : FKB)
    (h_b_0 : b_0.val < 65536) (h_b_1 : b_1.val < 65536)
    (h_b_2 : b_2.val < 65536) (h_b_3 : b_3.val < 65536)
    (h_c_0 : c_0.val < 65536) (h_c_1 : c_1.val < 65536)
    (h_c_2 : c_2.val < 65536) (h_c_3 : c_3.val < 65536)
    (h_n_0 : n_0.val ≤ 0xFFFC) (h_n_1 : n_1.val < 65536)
    (h_lsb : lsb = 0 ∨ lsb = 1)
    (h_k_1 : k_1 = 0 ∨ k_1 = 1) (h_k_2 : k_2 = 0 ∨ k_2 = 1)
    (h_k_3 : k_3 = 0 ∨ k_3 = 1) (h_k_4 : k_4 = 0 ∨ k_4 = 1)
    (h_m_0 : m_0 = n_0 + lsb)
    (h_1 : b_0 + c_0 = n_0 + lsb + k_1 * 65536)
    (h_2 : b_1 + c_1 + k_1 = n_1 + k_2 * 65536)
    (h_3 : b_2 + c_2 + k_2 = k_3 * 65536)
    (h_4 : b_3 + c_3 + k_3 = k_4 * 65536)
  :
    U64w.toBV #v[m_0, n_1, 0#16, 0#16] =
      U64w.toBV #v[b_0, b_1, b_2, b_3] + U64w.toBV #v[c_0, c_1, c_2, c_3]
  := by
    subst h_m_0
    have v_lsb : lsb.val = 0 ∨ lsb.val = 1 := by rcases h_lsb with rfl | rfl <;> simp
    have v_k_1 : k_1.val = 0 ∨ k_1.val = 1 := by rcases h_k_1 with rfl | rfl <;> simp
    have v_k_2 : k_2.val = 0 ∨ k_2.val = 1 := by rcases h_k_2 with rfl | rfl <;> simp
    have v_k_3 : k_3.val = 0 ∨ k_3.val = 1 := by rcases h_k_3 with rfl | rfl <;> simp
    have v_k_4 : k_4.val = 0 ∨ k_4.val = 1 := by rcases h_k_4 with rfl | rfl <;> simp
    have e_1 : b_0.val + c_0.val = n_0.val + lsb.val + k_1.val * 65536 := by
      clear * - h_1 h_b_0 h_c_0 h_n_0 v_lsb v_k_1; grind
    have e_2 : b_1.val + c_1.val + k_1.val = n_1.val + k_2.val * 65536 := by
      clear * - h_2 h_b_1 h_c_1 h_n_1 v_k_1 v_k_2; grind
    have e_3 : b_2.val + c_2.val + k_2.val = k_3.val * 65536 := by
      clear * - h_3 h_b_2 h_c_2 v_k_2 v_k_3; grind
    have e_4 : b_3.val + c_3.val + k_3.val = k_4.val * 65536 := by
      clear * - h_4 h_b_3 h_c_3 v_k_3 v_k_4; grind
    have e_sum : (n_0 + lsb).val = n_0.val + lsb.val := by
      clear * - h_n_0 v_lsb; grind
    clear h_1 h_2 h_3 h_4 h_lsb h_k_1 h_k_2 h_k_3 h_k_4
    simp [← BitVec.toNat_inj, U64w.toNat]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    omega

  /-- RISC-V clears bit 0 of a JALR target, and so does the chip: the low bit it added back,
      `jalr_lsb`, is the only difference between the sum and the 4-aligned `next_pc`. A pure
      fact about bit vectors. -/
  lemma clear_low_bit (target low : BitVec 64)
    (h_even : target.toNat % 2 = 0) (h_low : low.toNat < 2)
  :
    0xFFFFFFFFFFFFFFFE#64 &&& (target + low) = target
  := by
    have h_sum : (target + low).toNat = target.toNat + low.toNat := by
      have := target.isLt
      have := low.isLt
      simp [BitVec.toNat_add]
      omega
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_and, Nat.testBit_and, h_sum]
    match i, hi with
    | 0, _ =>
      have h_n : Nat.testBit target.toNat 0 = false := by simp [Nat.testBit_zero]; omega
      simp [h_n]
    | (j + 1), hj =>
      have h_mask : Nat.testBit (0xFFFFFFFFFFFFFFFE#64).toNat (j + 1) = true := by
        simp only [BitVec.toNat_ofNat]
        norm_num
        rw [Nat.testBit_succ, show (18446744073709551614 : ℕ) / 2 = 2 ^ 63 - 1 by norm_num,
            Nat.testBit_two_pow_sub_one]
        simp
        omega
      rw [h_mask, Nat.testBit_succ, Nat.testBit_succ,
          show (target.toNat + low.toNat) / 2 = target.toNat / 2 by omega]
      simp

  /-- The JALR target: `op_b + op_c = next_pc + jalr_lsb` as a 64-bit addition, proven in the
      chip by the four boolean carries of constraints 27 to 30
      (`jump/constraints.rs:79-126`). Constraint 26 makes `jalr_lsb` boolean; that it is bit 0
      of the unmasked target follows from this sum and the 4-alignment of `next_pc`
      (`jalr_target`). -/
  lemma jalr_sum
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
    (h_is_jalr : air.cols.opcode_selector.is_jalr row 0 = 1)
  :
    (air.cols.jalr_lsb row 0 = 0 ∨ air.cols.jalr_lsb row 0 = 1) ∧
    U64w.toBV #v[ ((air.cols.next_pc_0 row 0 + air.cols.jalr_lsb row 0 : FKB) : BitVec 16),
                  air.cols.next_pc_1 row 0, 0#16, 0#16 ] =
      U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                    air.cols.op_b_access.access.value_1 row 0,
                    air.cols.op_b_access.access.value_2 row 0,
                    air.cols.op_b_access.access.value_3 row 0 ] +
      U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                    air.cols.op_c_access.access.value_1 row 0,
                    air.cols.op_c_access.access.value_2 row 0,
                    air.cols.op_c_access.access.value_3 row 0 ]
  := by
    have h_cs := h_constraints row h_row
    have h_wf_row := h_wf row h_row
    obtain ⟨ h_b_0, h_b_1, h_b_2, h_b_3, h_c_0, h_c_1, h_c_2, h_c_3 ⟩ :=
      operand_ranges air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf_row) h_cs
    obtain ⟨ h_np_0, h_np_1, -, h_np_al ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    have h_c26 : constraint_26 air row := constraint_at h_cs 26 (by norm_num)
    have h_c27 : constraint_27 air row := constraint_at h_cs 27 (by norm_num)
    have h_c28 : constraint_28 air row := constraint_at h_cs 28 (by norm_num)
    have h_c29 : constraint_29 air row := constraint_at h_cs 29 (by norm_num)
    have h_c30 : constraint_30 air row := constraint_at h_cs 30 (by norm_num)
    simp only [constraint_and_interaction_simplification] at h_c26 h_c27 h_c28 h_c29 h_c30
    -- Name the four carry expressions, innermost first, so that each constraint is a
    -- boolean check on one of them.
    set k_1 : FKB := (0 + air.cols.op_b_access.access.value_0 row 0 +
      air.cols.op_c_access.access.value_0 row 0 - air.cols.next_pc_0 row 0 -
      air.cols.jalr_lsb row 0) * 2130673921 with h_k_1_def
    set k_2 : FKB := (0 + air.cols.op_b_access.access.value_1 row 0 +
      air.cols.op_c_access.access.value_1 row 0 + k_1 -
      air.cols.next_pc_1 row 0) * 2130673921 with h_k_2_def
    set k_3 : FKB := (0 + air.cols.op_b_access.access.value_2 row 0 +
      air.cols.op_c_access.access.value_2 row 0 + k_2) * 2130673921 with h_k_3_def
    set k_4 : FKB := (0 + air.cols.op_b_access.access.value_3 row 0 +
      air.cols.op_c_access.access.value_3 row 0 + k_3) * 2130673921 with h_k_4_def
    simp only [h_is_jalr, one_mul, mul_eq_zero, sub_eq_zero] at h_c26 h_c27 h_c28 h_c29 h_c30
    refine ⟨ h_c26, ?_ ⟩
    apply four_limb_carry_sum _ _ _ _ _ _ _ _ (air.cols.next_pc_0 row 0)
      (air.cols.next_pc_1 row 0) _ (air.cols.jalr_lsb row 0) k_1 k_2 k_3 k_4
      h_b_0 h_b_1 h_b_2 h_b_3 h_c_0 h_c_1 h_c_2 h_c_3 (by omega) h_np_1 h_c26 h_c27 h_c28
      h_c29 h_c30 rfl
    · linear_combination carry_mul_65536 h_k_1_def
    · linear_combination carry_mul_65536 h_k_2_def
    · linear_combination carry_mul_65536 h_k_3_def
    · linear_combination carry_mul_65536 h_k_4_def

  /-- The JALR target, as RISC-V and the Sail specification read it: `next_pc` is the 64-bit
      sum `op_b + op_c` with bit 0 cleared, and bit 1 of that sum is zero, so the fetch is
      aligned and the specification takes its success path. Both come from `jalr_sum` and the
      4-alignment of `next_pc`. -/
  lemma jalr_target
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
    (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
    (pico_assumptions : Equivalence.pico_CpuChip_control_flow_assumptions air)
    (h_is_jalr : air.cols.opcode_selector.is_jalr row 0 = 1)
  :
    U64w.toBV (next_pc air row) =
      0xFFFFFFFFFFFFFFFE#64 &&&
        (U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                       air.cols.op_b_access.access.value_1 row 0,
                       air.cols.op_b_access.access.value_2 row 0,
                       air.cols.op_b_access.access.value_3 row 0 ] +
         U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                       air.cols.op_c_access.access.value_1 row 0,
                       air.cols.op_c_access.access.value_2 row 0,
                       air.cols.op_c_access.access.value_3 row 0 ]) ∧
    (U64w.toBV #v[ air.cols.op_b_access.access.value_0 row 0,
                   air.cols.op_b_access.access.value_1 row 0,
                   air.cols.op_b_access.access.value_2 row 0,
                   air.cols.op_b_access.access.value_3 row 0 ] +
     U64w.toBV #v[ air.cols.op_c_access.access.value_0 row 0,
                   air.cols.op_c_access.access.value_1 row 0,
                   air.cols.op_c_access.access.value_2 row 0,
                   air.cols.op_c_access.access.value_3 row 0 ]) % 4 < 2
  := by
    obtain ⟨ h_lsb, h_sum ⟩ :=
      jalr_sum air row h_row h_is_real h_wf h_constraints pico_assumptions h_is_jalr
    obtain ⟨ h_np_0, h_np_1, -, h_np_al ⟩ :=
      next_pc_facts air row h_row h_is_real h_wf h_constraints pico_assumptions
    have v_lsb : (air.cols.jalr_lsb row 0).val = 0 ∨ (air.cols.jalr_lsb row 0).val = 1 := by
      rcases h_lsb with h | h <;> rw [h] <;> simp
    have e_add : (air.cols.next_pc_0 row 0 + air.cols.jalr_lsb row 0).val =
        (air.cols.next_pc_0 row 0).val + (air.cols.jalr_lsb row 0).val := by
      clear * - h_np_0 v_lsb; grind
    have h_split :
        U64w.toBV #v[ ((air.cols.next_pc_0 row 0 + air.cols.jalr_lsb row 0 : FKB) : BitVec 16),
                      air.cols.next_pc_1 row 0, 0#16, 0#16 ] =
          U64w.toBV (next_pc air row) + BitVec.ofNat 64 (air.cols.jalr_lsb row 0).val := by
      simp [next_pc, ← BitVec.toNat_inj, U64w.toNat, e_add]
      omega
    have h_even : (U64w.toBV (next_pc air row)).toNat % 2 = 0 := by
      simp [next_pc, U64w.toNat]
      omega
    have h_low : (BitVec.ofNat 64 (air.cols.jalr_lsb row 0).val).toNat < 2 := by
      simp; omega
    rw [← h_sum, h_split]
    refine ⟨ (clear_low_bit _ _ h_even h_low).symm, ?_ ⟩
    simp only [BitVec.lt_def, BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp [next_pc, U64w.toNat]
    omega

  -- ============================================================================
  -- Branch rows: the comparison message
  -- ============================================================================

  /-- A branch row sends the comparison message, so the ALU chips' promise holds for it: the
      two bits are `[op_a < op_b]` and `[op_b < op_a]`, signed for `BLT` and `BGE` (opcode 264)
      and unsigned for the other four (265). The row's own taken predicate is `branch_taken`,
      which a class file evaluates by unfolding it at its selectors. -/
  lemma branch_compare_spec
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_branch_sum :
      air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1)
  :
    (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 = 1 →
      RV64IM_Interactions.ALUBus.Spec 264
        (air.cols.a_lt_b row 0) (air.cols.a_gt_b row 0) 0 0
        (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
        (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
        (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
        (air.cols.op_b_access.access.value_2 row 0)
        (air.cols.op_b_access.access.value_3 row 0)) ∧
    (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 = 0 →
      RV64IM_Interactions.ALUBus.Spec 265
        (air.cols.a_lt_b row 0) (air.cols.a_gt_b row 0) 0 0
        (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
        (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
        (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
        (air.cols.op_b_access.access.value_2 row 0)
        (air.cols.op_b_access.access.value_3 row 0))
  := by
    have h_cmp := (dispatch_specs air row h_is_real h_wf).2.1 h_branch_sum
    constructor
    · intro h_lt_ge
      rw [h_lt_ge] at h_cmp
      norm_num at h_cmp
      exact h_cmp
    · intro h_lt_ge
      rw [h_lt_ge] at h_cmp
      norm_num at h_cmp
      exact h_cmp

  -- ============================================================================
  -- Memory rows
  -- ============================================================================

  /-- A memory row sends the memory dispatch, so the memory chips' promise holds for it: the
      address `op_b + op_c` is at least `2^16` and below `2^32`, and a load's value has 16-bit
      pieces and the opcode's extension. The address need not be a multiple of the access
      width, and the promise does not give the `0x7800_0000` guest bound. -/
  lemma memory_message_spec
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_memory : air.cols.opcode_selector.is_memory row 0 = 1)
  :
    MemoryBus.Spec (air.cols.instruction.opcode row 0)
      (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
      (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
      (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
      (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
      (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
      (air.cols.op_c_access.access.value_2 row 0) (air.cols.op_c_access.access.value_3 row 0)
      (air.cols.instruction.op_a_is_x0 row 0)
  := by
    exact (dispatch_specs air row h_is_real h_wf).2.2 h_memory

end CpuChip.Interpretations
