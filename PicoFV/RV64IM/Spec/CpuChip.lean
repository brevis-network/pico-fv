import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.Constraints.CpuChipInterpretations

open Plonky3

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 2_000_000
set_option linter.constructorNameAsVariable false

/-!
# CpuChip — what the chip guarantees as a sender (RV64, Pico v3.2.0)

A message the CPU chip sends with multiplicity 1 carries two predicates
(`Fundamentals/Interaction.lean`): the receiver's promise `wf_assume`, which the instruction
theorems take as a hypothesis, and the sender's duty `ext_assert`, which this file proves.
`ext_asrt` is the CPU chip's counterpart of the ALU chips' theorems of the same name.

Of the 17 messages a row sends (`raw_bus_row`), the deserialiser keeps 16; the Ecall message
has no contract and is dropped. Program, byte and register-access messages ask nothing of the
sender (`externals := True`). Three do:

- **The memory dispatch** (`memory_dispatch`, multiplicity `is_memory`,
  `MemoryBus.externals`): a memory opcode, `is_memory = 1`, 16-bit pieces for the base `b` and
  the offset `c`, 16-bit pieces for a store's value `a`, and `a = 0` when the instruction's
  first register field is `x0` (the destination of a load, the source register of a store).
  The memory chip's address addition `b + c` is exact only for 16-bit pieces, so the load and
  store theorems rest on this.
- **The ALU dispatch** (`alu_dispatch`, multiplicity `is_alu_not_x0`, `ALUBus.externals`): a
  valid ALU opcode, and 16-bit pieces for both operands.
- **The branch comparison** (`branch_compare`, multiplicity the sum of the six branch
  selectors): opcode 264 or 265, and 16-bit pieces for both operands, the values of `op_a` and
  `op_b`.

Every duty holds on the row alone, from its constraints and `bus_row_reads_asm`: the Program
table's promise about its instruction and the register file's promise about the values it
reads. The hypothesis leaves out the ALU and memory chips' promises on the three messages
above, so the theorem can be put together with those chips' theorems without circular
reasoning. None of the duties needs the whole-trace assumption or the next row, and a padding
row sends none of the three messages.

`ext_asrt` covers a message sent with multiplicity 1. `multiplicity_eq_zero_or_one` shows the
three are sent 0 or 1 times, so it covers every one the receivers count.

The facts about one row (operand ranges, `op_a` kept on a branch or store row, `op_a` zero on an
`x0` row, padding rows silent, the class-selector table) are in
`Constraints/CpuChipInterpretations.lean`.
-/

namespace CpuChip.Spec

  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations
  open RV64IM_Interactions

  -- ============================================================================
  -- Opcode sets, read through `.val`
  -- ============================================================================

  /-- The ALU opcodes the CPU dispatches are valid ALU-bus opcodes. -/
  lemma alu_validOpcode_of_val (x : FKB)
      (h : x.val ≤ 9 ∨ (30 ≤ x.val ∧ x.val ≤ 37) ∨ (40 ≤ x.val ∧ x.val ≤ 44) ∨
        (48 ≤ x.val ∧ x.val ≤ 52))
  :
    RV64IM_Interactions.ALUBus.validOpcode x
  := by
    simp only [RV64IM_Interactions.ALUBus.validOpcode, Finset.mem_Icc, Fin.le_def]
    simp
    omega

  /-- The memory opcodes, read through `.val`. -/
  lemma memory_validOpcode_of_val (x : FKB)
      (h : (10 ≤ x.val ∧ x.val ≤ 17) ∨ (45 ≤ x.val ∧ x.val ≤ 47))
  :
    MemoryBus.validOpcode x
  := by
    simp only [MemoryBus.validOpcode, Finset.mem_Icc, Fin.le_def]
    simp
    omega

  /-- The store opcodes, read through `.val`. -/
  lemma val_of_isStore (x : FKB) (h : MemoryBus.isStore x) :
      (15 ≤ x.val ∧ x.val ≤ 17) ∨ x.val = 47
  := by
    simp only [MemoryBus.isStore, Finset.mem_Icc, Fin.le_def, Fin.ext_iff] at h
    simpa using h

  -- ============================================================================
  -- The three messages that carry a duty
  -- ============================================================================

  /-- The ALU dispatch: entry 14 of `raw_bus_row`, sent with multiplicity `is_alu_not_x0`. -/
  def alu_dispatch {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      RV64IM_Interactions.ALUBusEntry FKB :=
    ⟨ air.cols.is_alu_not_x0 row 0
    , air.cols.instruction.opcode row 0
    , air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0
    , air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0
    , air.cols.op_b_access.access.value_0 row 0, air.cols.op_b_access.access.value_1 row 0
    , air.cols.op_b_access.access.value_2 row 0, air.cols.op_b_access.access.value_3 row 0
    , air.cols.op_c_access.access.value_0 row 0, air.cols.op_c_access.access.value_1 row 0
    , air.cols.op_c_access.access.value_2 row 0, air.cols.op_c_access.access.value_3 row 0 ⟩

  /-- The branch comparison: entry 15 of `raw_bus_row`, sent with multiplicity the sum of the
      six branch selectors. It asks the ALU chips to compare the values of `op_a` and `op_b`. -/
  def branch_compare {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      RV64IM_Interactions.ALUBusEntry FKB :=
    ⟨ air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0
    , (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0) * 8 +
        (1 - (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0)) * 9 +
        256
    , air.cols.a_lt_b row 0, air.cols.a_gt_b row 0, 0, 0
    , air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0
    , air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0
    , air.cols.op_b_access.access.value_0 row 0, air.cols.op_b_access.access.value_1 row 0
    , air.cols.op_b_access.access.value_2 row 0, air.cols.op_b_access.access.value_3 row 0 ⟩

  /-- The memory dispatch: entry 13 of `raw_bus_row`, sent with multiplicity `is_memory`. -/
  def memory_dispatch {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      MemoryBusEntry FKB :=
    ⟨ air.cols.opcode_selector.is_memory row 0
    , air.cols.instruction.opcode row 0
    , air.cols.op_a_access.access.value_0 row 0, air.cols.op_a_access.access.value_1 row 0
    , air.cols.op_a_access.access.value_2 row 0, air.cols.op_a_access.access.value_3 row 0
    , air.cols.op_b_access.access.value_0 row 0, air.cols.op_b_access.access.value_1 row 0
    , air.cols.op_b_access.access.value_2 row 0, air.cols.op_b_access.access.value_3 row 0
    , air.cols.op_c_access.access.value_0 row 0, air.cols.op_c_access.access.value_1 row 0
    , air.cols.op_c_access.access.value_2 row 0, air.cols.op_c_access.access.value_3 row 0
    , air.cols.instruction.op_a_is_x0 row 0
    , air.cols.opcode_selector.is_memory row 0
    , air.public_values 48
    , air.cols.clk row 0 ⟩

  /-- The row's ALU-bus messages are the ALU dispatch and the branch comparison. -/
  lemma bus_row_alu {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      (bus_row air row).ALU = [alu_dispatch air row, branch_compare air row] := by
    simp [bus_row, deserialise_bus_row, raw_bus_row, alu_dispatch, branch_compare]

  /-- The row's memory-bus message is the memory dispatch. -/
  lemma bus_row_memory {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
      (bus_row air row).Memory = [memory_dispatch air row] := by
    simp [bus_row, deserialise_bus_row, raw_bus_row, memory_dispatch]

  /-- The Program, byte and register-access contracts ask nothing of the sender, so a row's
      duties are those of its ALU and memory messages. -/
  lemma bus_row_ext_asrt_of_alu_memory {r : BusRow}
      (h_alu : ∀ e ∈ r.ALU, Interaction.BusEntry.ext_assert FKB e)
      (h_mem : ∀ e ∈ r.Memory, Interaction.BusEntry.ext_assert FKB e)
  :
    bus_row_ext_asrt r
  := by
    simp only [bus_row_ext_asrt, List.forall_iff_forall_mem, List.mem_append, List.mem_map]
    rintro _ ((((⟨ e, -, rfl ⟩ | ⟨ e, he, rfl ⟩) | ⟨ e, -, rfl ⟩) | ⟨ e, -, rfl ⟩) |
      ⟨ e, he, rfl ⟩)
    · exact fun _ => trivial
    · exact h_alu e he
    · exact fun _ => trivial
    · exact fun _ => trivial
    · exact h_mem e he

  -- ============================================================================
  -- The duties, one message at a time
  -- ============================================================================

  /-- The memory dispatch, when sent, meets `MemoryBus.externals`: a memory opcode,
      `is_memory = 1`, 16-bit pieces for `b` and `c`, 16-bit pieces for a store's `a`, and
      `a = 0` when `op_a` is `x0` (`op_a_zero_of_x0`). -/
  lemma memory_duty
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    Interaction.BusEntry.ext_assert FKB (memory_dispatch air row)
  := by
    intro h_send _
    have h_mem : air.cols.opcode_selector.is_memory row 0 = 1 := h_send
    have h_is_real : air.cols.is_real row 0 = 1 :=
      is_real_of_send h_constraints (fun h => (padding_row_silent h_constraints h).1) h_mem
    obtain ⟨ -, e_mem, e_store, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, -, - ⟩ :=
      selectors_by_opcode air row h_is_real h_reads
    have h_table := class_selectors_facts _ (selector_breakdown air row h_is_real h_reads)
    obtain ⟨ h_b_0, h_b_1, h_b_2, h_b_3, h_c_0, h_c_1, h_c_2, h_c_3 ⟩ :=
      operand_ranges air row h_is_real h_reads h_constraints
    refine ⟨ ?_, h_mem, h_b_0, h_b_1, h_b_2, h_b_3, h_c_0, h_c_1, h_c_2, h_c_3, ?_,
             op_a_zero_of_x0 air row h_constraints ⟩
    · -- Only a load or store opcode sets `is_memory`.
      exact memory_validOpcode_of_val _ (h_table.2.1 (by rw [← e_mem]; exact h_mem))
    · -- A store opcode sets `is_store` and no branch selector, so constraints 13 to 16 keep
      -- the value read.
      intro h_store
      obtain ⟨ s_2, s_3, s_4, s_5, s_6, s_7, s_8 ⟩ := h_table.2.2.1 (val_of_isStore _ h_store)
      apply op_a_kept_range air row h_is_real h_reads h_constraints
      rw [e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_store, s_2, s_3, s_4, s_5, s_6, s_7, s_8]
      norm_num

  /-- The ALU dispatch, when sent, meets `ALUBus.externals`: the row's opcode is an ALU opcode
      (constraint 17 makes the multiplicity zero unless the Program table set no class
      selector), and both operands are 16-bit. -/
  lemma alu_dispatch_duty
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    Interaction.BusEntry.ext_assert FKB (alu_dispatch air row)
  := by
    intro h_send _
    have h_alu : air.cols.is_alu_not_x0 row 0 = 1 := h_send
    have h_is_real : air.cols.is_real row 0 = 1 :=
      is_real_of_send h_constraints (fun h => (padding_row_silent h_constraints h).2.1) h_alu
    refine ⟨ ?_, fun _ => operand_ranges air row h_is_real h_reads h_constraints ⟩
    obtain ⟨ e_ecall, e_mem, -, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jalr, e_jal ⟩ :=
      selectors_by_opcode air row h_is_real h_reads
    have h_table := class_selectors_facts _ (selector_breakdown air row h_is_real h_reads)
    have h_c17 : constraint_17 air row := constraint_at h_constraints 17 (by norm_num)
    simp only [constraint_and_interaction_simplification] at h_c17
    rw [h_alu, h_is_real, e_ecall, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jalr,
      e_jal] at h_c17
    -- The ten class selectors add up to 0 or 1; at 1 constraint 17 would read `1 = 0`.
    apply alu_validOpcode_of_val
    apply h_table.2.2.2.2.2.2
    rcases h_table.2.2.2.2.2.1 with h | h
    · exact h
    · rw [h] at h_c17; simp at h_c17

  /-- The branch comparison, when sent, meets `ALUBus.externals`: exactly one branch selector
      is set, so the opcode is 264 (`BLT`, `BGE`) or 265 (the other four), and its operands,
      the values of `op_a` and `op_b`, are 16-bit (`op_a` keeps the value read on a branch
      row). -/
  lemma compare_duty
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    Interaction.BusEntry.ext_assert FKB (branch_compare air row)
  := by
    intro h_send _
    have h_sum :
        air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1 :=
      h_send
    have h_is_real : air.cols.is_real row 0 = 1 :=
      is_real_of_send h_constraints (fun h => (padding_row_silent h_constraints h).2.2) h_sum
    obtain ⟨ -, -, e_store, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, -, - ⟩ :=
      selectors_by_opcode air row h_is_real h_reads
    have h_table := class_selectors_facts _ (selector_breakdown air row h_is_real h_reads)
    -- A branch opcode: `is_store` is 0, and `is_blt + is_bge` is 0 or 1.
    have h_branch :
        air.cols.opcode_selector.is_store row 0 = 0 ∧
        (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 = 0 ∨
         air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 = 1) := by
      rw [e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu] at h_sum
      rw [e_store, e_blt, e_bge]
      exact h_table.2.2.2.2.1 h_sum
    obtain ⟨ h_no_store, h_lt_ge ⟩ := h_branch
    obtain ⟨ h_a_0, h_a_1, h_a_2, h_a_3 ⟩ :=
      op_a_kept_range air row h_is_real h_reads h_constraints
        (by rw [h_sum, h_no_store, add_zero])
    obtain ⟨ h_b_0, h_b_1, h_b_2, h_b_3, -, -, -, - ⟩ :=
      operand_ranges air row h_is_real h_reads h_constraints
    refine ⟨ ?_, fun _ => ⟨ h_a_0, h_a_1, h_a_2, h_a_3, h_b_0, h_b_1, h_b_2, h_b_3 ⟩ ⟩
    show RV64IM_Interactions.ALUBus.validOpcode
      ((air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0) * 8 +
        (1 - (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0)) * 9 +
        256)
    rcases h_lt_ge with h | h <;> rw [h] <;> norm_num [RV64IM_Interactions.ALUBus.validOpcode]

  -- ============================================================================
  -- The checked theorems
  -- ============================================================================

  /-- Each message that carries a duty is sent 0 or 1 times: a padding row sends none
      (`padding_row_silent`); on a real row the memory selector and the sum of the branch
      selectors are 0 or 1 (the class-selector table), and constraint 17 makes
      `is_alu_not_x0` a product of two such values. So `ext_asrt`, which covers multiplicity
      1, covers every one of these messages the receivers count. -/
  lemma multiplicity_eq_zero_or_one
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    (∀ e ∈ (bus_row air row).ALU, e.multiplicity = 0 ∨ e.multiplicity = 1) ∧
    (∀ e ∈ (bus_row air row).Memory, e.multiplicity = 0 ∨ e.multiplicity = 1)
  := by
    rw [bus_row_alu, bus_row_memory]
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    show ((air.cols.is_alu_not_x0 row 0 = 0 ∨ air.cols.is_alu_not_x0 row 0 = 1) ∧
      (air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 0 ∨
       air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
        air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
        air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1)) ∧
      (air.cols.opcode_selector.is_memory row 0 = 0 ∨
       air.cols.opcode_selector.is_memory row 0 = 1)
    rcases is_real_bool h_constraints with h_pad | h_is_real
    · obtain ⟨ h_m, h_a, h_b ⟩ := padding_row_silent h_constraints h_pad
      exact ⟨ ⟨ Or.inl h_a, Or.inl h_b ⟩, Or.inl h_m ⟩
    obtain ⟨ e_ecall, e_mem, -, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jalr, e_jal ⟩ :=
      selectors_by_opcode air row h_is_real h_reads
    have h_table := class_selectors_facts _ (selector_breakdown air row h_is_real h_reads)
    have h_c17 : constraint_17 air row := constraint_at h_constraints 17 (by norm_num)
    simp only [constraint_and_interaction_simplification, sub_eq_zero] at h_c17
    rw [h_is_real, e_ecall, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jalr,
      e_jal, op_a_is_x0_eq air row h_is_real h_reads] at h_c17
    rw [e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_mem]
    refine ⟨ ⟨ ?_, h_table.2.2.2.1 ⟩, h_table.1 ⟩
    rw [h_c17]
    rcases h_table.2.2.2.2.2.1 with h | h <;> rw [h] <;> split_ifs <;> norm_num

  /-- The CPU chip does its duty as a sender on every row, real or padding: each message it
      sends with multiplicity 1 satisfies its contract's `externals`. The hypothesis holds only
      the Program table's and the register file's promises (`bus_row_reads_asm`), not those of
      the chips that receive the three messages with a duty. -/
  lemma ext_asrt
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_reads : bus_row_reads_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    apply bus_row_ext_asrt_of_alu_memory
    · rw [bus_row_alu]
      simp only [List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      exact ⟨ alu_dispatch_duty air row h_reads h_constraints,
              compare_duty air row h_reads h_constraints ⟩
    · rw [bus_row_memory]
      simp only [List.mem_singleton, forall_eq]
      exact memory_duty air row h_reads h_constraints

end CpuChip.Spec
