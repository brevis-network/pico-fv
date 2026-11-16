import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.Constraints.CpuChipInterpretations

open Plonky3

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 2_000_000
set_option linter.constructorNameAsVariable false

/-!
# CpuChip — what the chip guarantees as a sender (RV64, Pico v3.1.1)

A message the CPU chip sends with multiplicity 1 carries two predicates
(`Fundamentals/Interaction.lean`): the receiver's promise `wf_assume`, which the instruction
theorems take as a hypothesis, and the sender's duty `ext_assert`, which this file proves.
`ext_asrt` is the CPU chip's counterpart of the ALU chips' theorems of the same name.

Of the 17 messages a row sends (`raw_bus_row`), the deserialiser keeps 16; the Ecall message
has no contract and is dropped. Program, byte and register-access messages ask nothing of the
sender (`externals := True`). Three do:

- **The memory dispatch** (multiplicity `is_memory`, `MemoryBus.externals`): a memory opcode,
  `is_memory = 1`, 16-bit pieces for the base `b` and the offset `c`, 16-bit pieces for a
  store's value `a`, and `a = 0` when the destination is `x0`. The memory chip's address
  addition `b + c` is exact only for 16-bit pieces, so the load and store theorems rest on this.
- **The ALU dispatch** (multiplicity `is_alu_not_x0`, `ALUBus.externals`): a valid ALU opcode,
  and 16-bit pieces for both operands.
- **The branch comparison** (multiplicity the sum of the six branch selectors): opcode 264 or
  265, and 16-bit pieces for both operands, the values of `op_a` and `op_b`.

Every duty holds on the row alone: from its constraints, the Program table's row facts and the
register values it reads (`bus_row_wf_asm`). None needs the whole-trace assumption or the next
row, and a padding row sends none of the three messages.

The operand facts used throughout:

- a register operand (immediate flag 0) is 16-bit because the register file says so
  (`StateBusEntry`'s promise on the read message);
- an immediate operand (flag 1) is the instruction's two 16-bit pieces and a sign fill
  `sign * 65535` (constraints 0 to 7), with the sign 0 or 1 (the Program table);
- on a branch or store row `op_a` keeps the value read (constraints 13 to 16);
- with `op_a_is_x0` set, the four pieces of `op_a` are zero (constraints 8 to 11).
-/

namespace CpuChip.Spec

  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations
  open RV64IM_Interactions.V3

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
  -- Facts about one row
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

  /-- A padding row sends none of the three messages that carry a duty: constraints 55 and 57
      to 62 zero the memory and branch selectors, and with them and constraints 54, 63 and 64
      constraint 17 zeroes `is_alu_not_x0`. -/
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

  /-- The row's class selectors, one by one, as the Program table sets them for its opcode. -/
  lemma selectors_by_opcode
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
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
    have h := (selector_exclusivity air row h_is_real h_wf).1
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

  /-- The immediate flags are 0 or 1, and the instruction's operand pieces are 16-bit with a
      sign of 0 or 1 (the Program table, `ProgramBusEntry.inversion`). -/
  lemma instruction_operand_pieces
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
  :
    (air.cols.opcode_selector.imm_b row 0 = 0 ∨ air.cols.opcode_selector.imm_b row 0 = 1) ∧
    (air.cols.opcode_selector.imm_c row 0 = 0 ∨ air.cols.opcode_selector.imm_c row 0 = 1) ∧
    (air.cols.instruction.op_b_0 row 0).val < 65536 ∧
    (air.cols.instruction.op_b_1 row 0).val < 65536 ∧
    (air.cols.instruction.op_b_sign row 0 = 0 ∨ air.cols.instruction.op_b_sign row 0 = 1) ∧
    (air.cols.instruction.op_c_0 row 0).val < 65536 ∧
    (air.cols.instruction.op_c_1 row 0).val < 65536 ∧
    (air.cols.instruction.op_c_sign row 0 = 0 ∨ air.cols.instruction.op_c_sign row 0 = 1)
  := by
    have h_prog := program_bus_operand_properties air row h_is_real h_wf
    obtain ⟨ instr, pc', data, props, _, _, h_trans, h_deser, _ ⟩ := h_prog
    have h := ProgramBusEntry.inversion h_trans h_deser
    rw [deserialise_program_bus_entry] at h
    exact ⟨ h.one_hot.1, h.one_hot.2.1, h.b_pieces.1, h.b_pieces.2.1, h.b_pieces.2.2,
            h.c_pieces.1, h.c_pieces.2.1, h.c_pieces.2.2 ⟩

  /-- The register values the row reads are 16-bit: `op_a`'s previous value on every real row,
      `op_b` and `op_c` when they are registers. Only the read messages are used
      (`bus_row_wf_asm`), not the row's own write. -/
  lemma read_ranges
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
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
    simp [bus_row_wf_asm, bus_row, deserialise_bus_row, raw_bus_row, h_is_real] at h_wf
    grind

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

  /-- On a real row both operand values the row sends on are 16-bit, whatever their
      immediate flags. -/
  lemma operand_ranges
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_is_real : air.cols.is_real row 0 = 1)
    (h_wf : bus_row_wf_asm (bus_row air row))
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
    obtain ⟨ h_imm_b, h_imm_c, h_b_0, h_b_1, h_b_s, h_c_0, h_c_1, h_c_s ⟩ :=
      instruction_operand_pieces air row h_is_real h_wf
    obtain ⟨ -, -, -, -, h_read_b, h_read_c ⟩ := read_ranges air row h_is_real h_wf
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
    (h_wf : bus_row_wf_asm (bus_row air row))
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
    obtain ⟨ h_p_0, h_p_1, h_p_2, h_p_3, -, - ⟩ := read_ranges air row h_is_real h_wf
    have h_c13 : constraint_13 air row := constraint_at h_constraints 13 (by norm_num)
    have h_c14 : constraint_14 air row := constraint_at h_constraints 14 (by norm_num)
    have h_c15 : constraint_15 air row := constraint_at h_constraints 15 (by norm_num)
    have h_c16 : constraint_16 air row := constraint_at h_constraints 16 (by norm_num)
    simp only [constraint_and_interaction_simplification, h_gate, one_mul, sub_eq_zero]
      at h_c13 h_c14 h_c15 h_c16
    rw [h_c13, h_c14, h_c15, h_c16]
    exact ⟨ h_p_0, h_p_1, h_p_2, h_p_3 ⟩

  /-- With `op_a_is_x0` set the four pieces of `op_a` are zero (constraints 8 to 11). -/
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
  -- The three messages that carry a duty
  -- ============================================================================

  /-- The memory dispatch, when sent: a memory opcode, `is_memory = 1`, 16-bit pieces for `b`
      and `c`, 16-bit pieces for a store's `a`, and `a = 0` when the destination is `x0`. -/
  lemma memory_duty
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_mem : air.cols.opcode_selector.is_memory row 0 = 1)
  :
    MemoryBus.validOpcode (air.cols.instruction.opcode row 0) ∧
    air.cols.opcode_selector.is_memory row 0 = 1 ∧
    (air.cols.op_b_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_b_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_b_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_b_access.access.value_3 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_0 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_1 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_2 row 0).val < 65536 ∧
    (air.cols.op_c_access.access.value_3 row 0).val < 65536 ∧
    (MemoryBus.isStore (air.cols.instruction.opcode row 0) →
      (air.cols.op_a_access.access.value_0 row 0).val < 65536 ∧
      (air.cols.op_a_access.access.value_1 row 0).val < 65536 ∧
      (air.cols.op_a_access.access.value_2 row 0).val < 65536 ∧
      (air.cols.op_a_access.access.value_3 row 0).val < 65536) ∧
    (¬ air.cols.instruction.op_a_is_x0 row 0 = 0 →
      air.cols.op_a_access.access.value_0 row 0 = 0 ∧
      air.cols.op_a_access.access.value_1 row 0 = 0 ∧
      air.cols.op_a_access.access.value_2 row 0 = 0 ∧
      air.cols.op_a_access.access.value_3 row 0 = 0)
  := by
    have h_is_real : air.cols.is_real row 0 = 1 :=
      is_real_of_send h_constraints (fun h => (padding_row_silent h_constraints h).1) h_mem
    obtain ⟨ -, e_mem, e_store, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, -, - ⟩ :=
      selectors_by_opcode air row h_is_real h_wf
    obtain ⟨ h_b_0, h_b_1, h_b_2, h_b_3, h_c_0, h_c_1, h_c_2, h_c_3 ⟩ :=
      operand_ranges air row h_is_real h_wf h_constraints
    have h_range := selector_breakdown air row h_is_real h_wf
    refine ⟨ ?_, h_mem, h_b_0, h_b_1, h_b_2, h_b_3, h_c_0, h_c_1, h_c_2, h_c_3, ?_,
             op_a_zero_of_x0 air row h_constraints ⟩
    · -- Only a load or store opcode sets `is_memory`.
      apply memory_validOpcode_of_val
      rw [e_mem] at h_mem
      generalize (air.cols.instruction.opcode row 0).val = n at h_range h_mem ⊢
      have h_n : n ≤ 52 := by omega
      clear e_mem e_store e_beq e_bne e_blt e_bge e_bltu e_bgeu
      interval_cases n <;> first | omega | simp [class_selectors_of_opcode] at h_mem
    · -- A store opcode sets `is_store` and no branch selector, so constraints 13 to 16 keep
      -- the value read.
      intro h_store
      apply op_a_kept_range air row h_is_real h_wf h_constraints
      have h_n := val_of_isStore _ h_store
      rw [e_store, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu]
      generalize (air.cols.instruction.opcode row 0).val = n at h_n ⊢
      rcases h_n with ⟨ h_lo, h_hi ⟩ | h_n
      · interval_cases n <;> simp [class_selectors_of_opcode]
      · subst h_n; simp [class_selectors_of_opcode]

  /-- The ALU dispatch, when sent: the row's opcode is an ALU opcode (the selector sum in
      constraint 17 is zero, so the Program table set no class selector), and both operands
      are 16-bit. -/
  lemma alu_dispatch_duty
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_alu : air.cols.is_alu_not_x0 row 0 = 1)
  :
    RV64IM_Interactions.ALUBus.validOpcode (air.cols.instruction.opcode row 0) ∧
    RV64IM_Interactions.ALUBus.operandRange
      (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
      (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
      (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
      (air.cols.op_c_access.access.value_2 row 0) (air.cols.op_c_access.access.value_3 row 0)
  := by
    have h_is_real : air.cols.is_real row 0 = 1 :=
      is_real_of_send h_constraints (fun h => (padding_row_silent h_constraints h).2.1) h_alu
    refine ⟨ ?_, operand_ranges air row h_is_real h_wf h_constraints ⟩
    obtain ⟨ e_ecall, e_mem, -, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jalr, e_jal ⟩ :=
      selectors_by_opcode air row h_is_real h_wf
    have h_range := selector_breakdown air row h_is_real h_wf
    have h_c17 : constraint_17 air row := constraint_at h_constraints 17 (by norm_num)
    simp only [constraint_and_interaction_simplification] at h_c17
    rw [h_alu, h_is_real, e_ecall, e_mem, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, e_jalr,
      e_jal] at h_c17
    apply alu_validOpcode_of_val
    generalize (air.cols.instruction.opcode row 0).val = n at h_range h_c17 ⊢
    clear e_ecall e_mem e_beq e_bne e_blt e_bge e_bltu e_bgeu e_jalr e_jal
    have h_n : n ≤ 52 := by omega
    by_contra h_not
    interval_cases n <;> first | omega | simp [class_selectors_of_opcode] at h_c17

  /-- The branch comparison, when sent: exactly one branch selector is set, so the opcode is
      264 (`BLT`, `BGE`) or 265 (the other four), and its operands, the values of `op_a` and
      `op_b`, are 16-bit (`op_a` keeps the value read on a branch row). -/
  lemma compare_duty
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
    (h_sum : air.cols.opcode_selector.is_beq row 0 + air.cols.opcode_selector.is_bne row 0 +
      air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 +
      air.cols.opcode_selector.is_bltu row 0 + air.cols.opcode_selector.is_bgeu row 0 = 1)
  :
    RV64IM_Interactions.ALUBus.validOpcode
      ((air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0) * 8 +
        (1 - (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0)) * 9 +
        256) ∧
    RV64IM_Interactions.ALUBus.operandRange
      (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
      (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
      (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
      (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
  := by
    have h_is_real : air.cols.is_real row 0 = 1 :=
      is_real_of_send h_constraints (fun h => (padding_row_silent h_constraints h).2.2) h_sum
    obtain ⟨ -, -, e_store, e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu, -, - ⟩ :=
      selectors_by_opcode air row h_is_real h_wf
    have h_range := selector_breakdown air row h_is_real h_wf
    -- A branch opcode: `is_store` is 0, and `is_blt + is_bge` is 0 or 1.
    have h_branch :
        air.cols.opcode_selector.is_store row 0 = 0 ∧
        (air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 = 0 ∨
         air.cols.opcode_selector.is_blt row 0 + air.cols.opcode_selector.is_bge row 0 = 1) := by
      rw [e_beq, e_bne, e_blt, e_bge, e_bltu, e_bgeu] at h_sum
      rw [e_store, e_blt, e_bge]
      generalize (air.cols.instruction.opcode row 0).val = n at h_range h_sum ⊢
      have h_n : n ≤ 52 := by omega
      interval_cases n <;> first | omega | simp [class_selectors_of_opcode] at h_sum ⊢
    obtain ⟨ h_no_store, h_lt_ge ⟩ := h_branch
    obtain ⟨ h_a_0, h_a_1, h_a_2, h_a_3 ⟩ :=
      op_a_kept_range air row h_is_real h_wf h_constraints (by rw [h_sum, h_no_store, add_zero])
    obtain ⟨ h_b_0, h_b_1, h_b_2, h_b_3, -, -, -, - ⟩ :=
      operand_ranges air row h_is_real h_wf h_constraints
    refine ⟨ ?_, h_a_0, h_a_1, h_a_2, h_a_3, h_b_0, h_b_1, h_b_2, h_b_3 ⟩
    rcases h_lt_ge with h | h <;> rw [h] <;> norm_num [RV64IM_Interactions.ALUBus.validOpcode]

  -- ============================================================================
  -- The sender theorem
  -- ============================================================================

  /-- The CPU chip does its duty as a sender on every row, real or padding: each message it
      sends with multiplicity 1 satisfies its contract's `externals`. -/
  lemma ext_asrt
    [Field ExtF]
    (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : CpuChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have h_mem := memory_duty air row h_wf h_constraints
    have h_alu := alu_dispatch_duty air row h_wf h_constraints
    have h_cmp := compare_duty air row h_wf h_constraints
    simp [bus_row_ext_asrt, bus_row, deserialise_bus_row, raw_bus_row,
      RV64IM_Interactions.ALUBus.externals, MemoryBus.externals]
    exact ⟨ fun h _ => ⟨ (h_alu h).1, fun _ => (h_alu h).2 ⟩,
            fun h _ => ⟨ (h_cmp h).1, fun _ => (h_cmp h).2 ⟩,
            fun h _ => h_mem h ⟩

end CpuChip.Spec
