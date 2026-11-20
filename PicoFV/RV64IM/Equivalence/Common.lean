import PicoFV.RV64IM.Constraints.CpuChip
import PicoFV.RV64IM.Constraints.CpuChipInterpretations
import PicoFV.RV64IM.RVSail.Opcodes.Opcodes

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.constructorNameAsVariable false

/-!
# Shared definitions of the RV64IM instruction theorems (Pico v3.1.1)

The operand values a row reads and writes, the operations its messages stand for, and the
control-flow facts every ALU-class row shares. The one assumption the theorems make about the
whole trace rather than about a row, `pico_CpuChip_control_flow_assumptions`, is defined in
`Constraints/CpuChipInterpretations.lean` so that the lemmas there can take it.

The pc-alignment lemmas that the 2.x file also held are not here. A real row's next pc is
4-aligned by `CpuChip.Interpretations.next_pc_mod_four_eq_zero`, which keeps the 2.x name but
takes its arguments in the interpretations file's order and no longer takes the Program-bus
axioms. The 2.x `pc_next_row_mod_four_eq_zero` has no v3.1.1 counterpart: `pc_facts` gives
any real row's pc alignment directly.

An ALU-class instruction theorem with register operands closes in one call,
`eq_operation_list_effect_state_of_reg_reg` or `eq_operation_list_effect_state_of_reg_imm`
(for a shift by an immediate, `eq_operation_list_effect_state_of_shift_imm`, which calls the
latter).
Both take the row's facts bundled as `ALURowFacts`, the immediate flags of their family, the bus
hypotheses, and the ALU chip's promise `alu_promise`. The bundle says nothing about the
immediate flags, so every ALU-class row has one, `LUI` and `AUIPC` rows included; a theorem
that does not fit either family uses its lemmas for the next pc
(`ALURowFacts.toBV_next_pc_eq`) and the result's write
(`operation_list_effect_state_writeReg_eq_op_a_value`). Of the lemmas that compute a row's
bus operations, the register-register one is private; `CPU_bus_operations_eq_of_imm_c_eq_one`
is shared with the branch theorems.
-/

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  -- `bv_decide` realises these auxiliary declarations in each module that needs them, and two
  -- instruction-class files realising them separately cannot be imported together. Realising
  -- them once here, below every class file, avoids the clash.
  open Lean.Elab.Tactic.BVDecide.Frontend.Normalize in
  run_meta do
    for enum in [``Register, ``Reservability, ``misaligned_fault, ``uop, ``bop] do
      discard <| getEnumToBitVecFor enum
      discard <| getEqIffEnumToBitVecEqFor enum
      discard <| getEnumToBitVecLeFor enum

  section Auxiliaries

    /-- The row's `op_a` value, the one it writes back, as a `U64w`. -/
    def op_a_value {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_a_access.access.value_0 row 0,
          air.cols.op_a_access.access.value_1 row 0,
          air.cols.op_a_access.access.value_2 row 0,
          air.cols.op_a_access.access.value_3 row 0 ]

    /-- The row's `op_a` value before the write: the old value of `rd`, which the row reads
        back. -/
    def op_a_prev_value {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) :
        U64w :=
      #v[ air.cols.op_a_access.prev_value_0 row 0,
          air.cols.op_a_access.prev_value_1 row 0,
          air.cols.op_a_access.prev_value_2 row 0,
          air.cols.op_a_access.prev_value_3 row 0 ]

    /-- The row's `op_b` value, a register read or the instruction's immediate. -/
    def op_b_value {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_b_access.access.value_0 row 0,
          air.cols.op_b_access.access.value_1 row 0,
          air.cols.op_b_access.access.value_2 row 0,
          air.cols.op_b_access.access.value_3 row 0 ]

    /-- The row's `op_c` value, a register read or the instruction's immediate. -/
    def op_c_value {ExtF : Type} [Field ExtF] (air : Valid_CpuChip FKB ExtF) (row : ℕ) : U64w :=
      #v[ air.cols.op_c_access.access.value_0 row 0,
          air.cols.op_c_access.access.value_1 row 0,
          air.cols.op_c_access.access.value_2 row 0,
          air.cols.op_c_access.access.value_3 row 0 ]

    /-- The operations the row's messages stand for, followed by the write of its `next_pc`.
        The v3.1.1 pc has two pieces instead of three, so `next_pc` packs two. -/
    def CPU_bus_operations {ExtF : Type} [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ) :=
      RV64IM_Interactions.V3.bus_operations (deserialise_bus_row (raw_bus_row air row)) ++
      [ .WritePC (U64w.toBV (next_pc air row)) ]

    /-- The facts about a CPU-chip row that every ALU-class instruction theorem has, for either
        family and whatever its immediate flags: the row is a real row of the trace, the
        whole-trace assumptions and constraints hold, its opcode is `op`, and `op` sets no
        class selector. An instruction proof builds it once and passes it whole.

        The immediate flags are not in it. `imm_c` tells the two families apart (0 for
        register-register, 1 for register-immediate), so each family's lemmas take it, and on a
        register-register row it fixes `imm_b = 0` (`imm_b_eq_zero_of_imm_c_eq_zero`). `imm_b`
        is 1 on `LUI` and `AUIPC` rows (opcode 0 with `imm_c = 1`), which are ALU-class rows
        too, so only the register-immediate lemma takes `imm_b = 0`. Nor are the bus hypotheses
        in it, which are about the Sail state rather than the row. -/
    structure ALURowFacts {ExtF : Type} [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : FKB) : Prop where
      row_le : row ≤ air.last_row
      is_real : air.cols.is_real row 0 = 1
      all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row)
      all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row
      control_flow : pico_CpuChip_control_flow_assumptions air
      opcode_eq : air.cols.instruction.opcode row 0 = op
      class_selectors : class_selectors_of_opcode op.val = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

    /-- The ALU chip's promise for an ALU-class row, as the instruction lemmas take it: if the
        ALU chip's specification for opcode `op` holds of the row's operand columns
        (`alu_spec_of_row`, which `alu_message_spec` gives), the result `v` is the row's `op_a`
        value. -/
    def alu_promise {ExtF : Type} [Field ExtF]
        (air : Valid_CpuChip FKB ExtF) (row : ℕ) (op : FKB) (v : BitVec 64) : Prop :=
      alu_spec_of_row air row op → v = U64w.toBV (op_a_value air row)

    /-- An ALU-class row's next pc is `pc + 4`: it sets no class selector, so it neither
        branches, jumps nor halts. Its class selectors one by one are `alu_class_selectors_zero`;
        whether it sends its ALU message is `CpuChip.Interpretations.alu_message_spec`. -/
    lemma ALURowFacts.toBV_next_pc_eq
      [Field ExtF]
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
    :
      U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64
    := by
      obtain ⟨ h_row, h_is_real, h_wf, h_constraints, pico_assumptions, h_opcode, h_class ⟩ := h
      subst h_opcode
      obtain ⟨ h_ecall, -, -, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_jalr, h_jal ⟩ :=
        alu_class_selectors_zero air row h_is_real (h_wf row h_row) h_class
      exact is_sequential_active_constraints air row h_row h_is_real h_wf h_constraints
        pico_assumptions ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr
        (is_halt_eq_zero_of_no_ecall air row h_ecall (h_constraints row h_row))

    /-- An opcode that sets no class selector has no memory width: every opcode with one (10 to
        17 and 45 to 47) sets `is_memory`. -/
    lemma mem_width_of_opcode_eq_none_of_class_selectors {op : FKB}
      (h_class : class_selectors_of_opcode op.val = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    :
      mem_width_of_opcode op = none
    := by
      unfold mem_width_of_opcode
      split_ifs with h_double h_word h_half h_byte
      · rcases h_double with rfl | rfl <;> simp [class_selectors_of_opcode] at h_class
      · rcases h_word with rfl | rfl | rfl <;> simp [class_selectors_of_opcode] at h_class
      · rcases h_half with rfl | rfl | rfl <;> simp [class_selectors_of_opcode] at h_class
      · rcases h_byte with rfl | rfl | rfl <;> simp [class_selectors_of_opcode] at h_class
      · rfl

    /-- `imm_b` is 0 on a real row whose opcode the decoder always gives a register `op_b`
        (`imm_b_of_opcode` is `some 0`: every opcode but 0 and `JAL`'s 24). An instruction proof
        that has built its `ALURowFacts` uses `ALURowFacts.imm_b_eq_zero`. -/
    lemma imm_b_eq_zero_of_opcode
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_op : imm_b_of_opcode (air.cols.instruction.opcode row 0).val = some 0)
    :
      air.cols.opcode_selector.imm_b row 0 = 0
    :=
      (selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)).2.1 0 h_op

    /-- `imm_b_eq_zero_of_opcode` from an ALU-class row's facts: for an opcode the decoder
        always gives a register `op_b`, which a caller with a literal opcode proves by `rfl`. -/
    lemma ALURowFacts.imm_b_eq_zero
      [Field ExtF]
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
      (h_op : imm_b_of_opcode op.val = some 0)
    :
      air.cols.opcode_selector.imm_b row 0 = 0
    :=
      imm_b_eq_zero_of_opcode air row h.is_real (h.all_wf row h.row_le)
        (by rw [h.opcode_eq]; exact h_op)

    /-- `imm_b` is 0 on a real row with `imm_c = 0`, whatever its opcode. The rows with
        `imm_b = 1` are `JAL` (opcode 24) and `LUI` and `AUIPC` (opcode 0), and all three have
        `imm_c = 1` (`imm_c_of_opcode` at 24, `ProgramBusEntry.decoded_from` at 0). So a
        register-register row needs no separate `imm_b = 0`. -/
    lemma imm_b_eq_zero_of_imm_c_eq_zero
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
    :
      air.cols.opcode_selector.imm_b row 0 = 0
    := by
      have h_sel := selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
      by_cases h0 : (air.cols.instruction.opcode row 0).val = 0
      · -- Opcode 0 with `imm_c = 0` is `ADD`, decoded with `imm_b = 0`.
        obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ :=
          program_bus_operand_properties air row h_is_real h_wf
        have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
        rw [deserialise_program_bus_entry] at h_decoded
        simp [ProgramBusEntry.decoded_from, h0, h_imm_c] at h_decoded
        exact h_decoded.1
      · by_cases h24 : (air.cols.instruction.opcode row 0).val = 24
        · -- `JAL` has `imm_c = 1`.
          have h1 := h_sel.2.2 1 (by rw [h24]; rfl)
          rw [h_imm_c] at h1
          exact absurd h1 zero_ne_one
        · exact h_sel.2.1 0 (by unfold imm_b_of_opcode; split <;> simp_all)

    /-- `imm_c` is 0 on a real row whose opcode the decoder always gives a register `op_c`
        (`imm_c_of_opcode` is `some 0`: an ALU opcode no immediate form shares, such as `SUBW`'s
        41). -/
    lemma imm_c_eq_zero_of_opcode
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_op : imm_c_of_opcode (air.cols.instruction.opcode row 0).val = some 0)
    :
      air.cols.opcode_selector.imm_c row 0 = 0
    :=
      (selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)).2.2 0 h_op

    /-- `imm_c_eq_zero_of_opcode` from an ALU-class row's facts: for an opcode the decoder
        always gives a register `op_c`, which a caller with a literal opcode proves by `rfl`. -/
    lemma ALURowFacts.imm_c_eq_zero
      [Field ExtF]
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
      (h_op : imm_c_of_opcode op.val = some 0)
    :
      air.cols.opcode_selector.imm_c row 0 = 0
    :=
      imm_c_eq_zero_of_opcode air row h.is_real (h.all_wf row h.row_le)
        (by rw [h.opcode_eq]; exact h_op)

    /-- The register indices the decoder writes: `op_a` is below 32, and so is each operand
        whose immediate flag is 0 (`ProgramBusEntry.inversion_operands`). -/
    lemma register_indices_lt
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
    :
      (air.cols.instruction.op_a row 0).val < 32 ∧
      (air.cols.opcode_selector.imm_b row 0 = 0 → (air.cols.instruction.op_b_0 row 0).val < 32) ∧
      (air.cols.opcode_selector.imm_c row 0 = 0 → (air.cols.instruction.op_c_0 row 0).val < 32)
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_ops := ProgramBusEntry.inversion_operands h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_ops
      exact ⟨ h_ops.1, fun h => (h_ops.2.2.1 h).1, fun h => (h_ops.2.2.2.1 h).1 ⟩

    /-- The row's packed `pc` is the address its Program message's pc read carries. -/
    lemma toBV_pc_eq_ofNat
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
    :
      U64w.toBV (pc air row) =
        BitVec.ofNat 64 ((air.cols.pc_0 row 0).val + 65536 * (air.cols.pc_1 row 0).val)
    := by
      have h_pc_bounds := pc_facts air row h_is_real h_wf
      simp [pc, ← BitVec.toNat_inj, U64w.toNat]
      omega

    /-! A row's bus operations are computed from its 17 messages (`raw_bus_row`). Sorting them
        into a `BusRow` folds over all 17, and one `simp` through that fold builds a proof term
        too deep for the kernel replay (`leanchecker`) at its default stack. The three lemmas
        below give the parts of the sorted row that `bus_operations` reads, each as its own
        declaration checked by evaluation (`rfl`). The lemmas that compute a row's bus
        operations rewrite with them and then simplify short lists. -/

    /-- The Program part of a sorted CPU row: its one instruction fetch, with multiplicity
        `is_real` (the first message of `raw_bus_row`). -/
    lemma deserialise_raw_bus_row_Program
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    :
      (deserialise_bus_row (raw_bus_row air row)).Program =
        [ ProgramBusEntry.deserialise (air.cols.is_real row 0,
            #v[ air.cols.pc_0 row 0, air.cols.pc_1 row 0,
                air.cols.instruction.opcode row 0, air.cols.instruction.opcode row 0,
                air.cols.instruction.op_a row 0, air.cols.instruction.op_b_0 row 0,
                air.cols.instruction.op_b_1 row 0, air.cols.instruction.op_b_sign row 0,
                air.cols.instruction.op_c_0 row 0, air.cols.instruction.op_c_1 row 0,
                air.cols.instruction.op_c_sign row 0, air.cols.instruction.op_a_is_x0 row 0,
                air.cols.opcode_selector.imm_b row 0, air.cols.opcode_selector.imm_c row 0,
                air.cols.opcode_selector.is_ecall row 0, air.cols.opcode_selector.is_memory row 0,
                air.cols.opcode_selector.is_store row 0, air.cols.opcode_selector.is_beq row 0,
                air.cols.opcode_selector.is_bne row 0, air.cols.opcode_selector.is_blt row 0,
                air.cols.opcode_selector.is_bge row 0, air.cols.opcode_selector.is_bltu row 0,
                air.cols.opcode_selector.is_bgeu row 0, air.cols.opcode_selector.is_jalr row 0,
                air.cols.opcode_selector.is_jal row 0, air.cols.pc_carry row 0 ]) ]
    := rfl

    /-- The register-access part of a sorted CPU row, in message order: the previous and the
        new access to `op_b`'s register (multiplicities `1 - imm_b` and its negation), the same
        for `op_c` (`1 - imm_c`), and for `op_a` (`is_real`). Each entry's fields are the
        chunk, the timestamp, the register as the pointer's three limbs and the value's four. -/
    lemma deserialise_raw_bus_row_State
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    :
      let b := air.cols.op_b_access
      let c := air.cols.op_c_access
      let a := air.cols.op_a_access
      let clk := air.cols.clk row 0
      let chunk := air.public_values 48
      (deserialise_bus_row (raw_bus_row air row)).State =
        [ RV64IM_Interactions.StateBusEntry.deserialise
            (1 - air.cols.opcode_selector.imm_b row 0,
             #v[ chunk,
                 clk + 2 - (b.access.diff_16bit_limb row 0 + b.access.diff_hi9 row 0 * 65536) - 1,
                 air.cols.instruction.op_b_0 row 0, 0, 0,
                 b.access.value_0 row 0, b.access.value_1 row 0,
                 b.access.value_2 row 0, b.access.value_3 row 0 ]),
          RV64IM_Interactions.StateBusEntry.deserialise
            (0 - (1 - air.cols.opcode_selector.imm_b row 0),
             #v[ chunk, clk + 2, air.cols.instruction.op_b_0 row 0, 0, 0,
                 b.access.value_0 row 0, b.access.value_1 row 0,
                 b.access.value_2 row 0, b.access.value_3 row 0 ]),
          RV64IM_Interactions.StateBusEntry.deserialise
            (1 - air.cols.opcode_selector.imm_c row 0,
             #v[ chunk,
                 clk + 1 - (c.access.diff_16bit_limb row 0 + c.access.diff_hi9 row 0 * 65536) - 1,
                 air.cols.instruction.op_c_0 row 0, 0, 0,
                 c.access.value_0 row 0, c.access.value_1 row 0,
                 c.access.value_2 row 0, c.access.value_3 row 0 ]),
          RV64IM_Interactions.StateBusEntry.deserialise
            (0 - (1 - air.cols.opcode_selector.imm_c row 0),
             #v[ chunk, clk + 1, air.cols.instruction.op_c_0 row 0, 0, 0,
                 c.access.value_0 row 0, c.access.value_1 row 0,
                 c.access.value_2 row 0, c.access.value_3 row 0 ]),
          RV64IM_Interactions.StateBusEntry.deserialise
            (air.cols.is_real row 0,
             #v[ chunk,
                 clk + 3 - (a.access.diff_16bit_limb row 0 + a.access.diff_hi9 row 0 * 65536) - 1,
                 air.cols.instruction.op_a row 0, 0, 0,
                 a.prev_value_0 row 0, a.prev_value_1 row 0,
                 a.prev_value_2 row 0, a.prev_value_3 row 0 ]),
          RV64IM_Interactions.StateBusEntry.deserialise
            (0 - air.cols.is_real row 0,
             #v[ chunk, clk + 3, air.cols.instruction.op_a row 0, 0, 0,
                 a.access.value_0 row 0, a.access.value_1 row 0,
                 a.access.value_2 row 0, a.access.value_3 row 0 ]) ]
    := rfl

    /-- The memory-dispatch part of a sorted CPU row: its one message, with multiplicity
        `is_memory`. Its fields are the opcode, the three operand values, `op_a_is_x0`,
        `is_memory`, the chunk and the timestamp. -/
    lemma deserialise_raw_bus_row_Memory
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
    :
      let b := air.cols.op_b_access
      let c := air.cols.op_c_access
      let a := air.cols.op_a_access
      (deserialise_bus_row (raw_bus_row air row)).Memory =
        [ MemoryBusEntry.deserialise (air.cols.opcode_selector.is_memory row 0,
            #v[ air.cols.instruction.opcode row 0,
                a.access.value_0 row 0, a.access.value_1 row 0,
                a.access.value_2 row 0, a.access.value_3 row 0,
                b.access.value_0 row 0, b.access.value_1 row 0,
                b.access.value_2 row 0, b.access.value_3 row 0,
                c.access.value_0 row 0, c.access.value_1 row 0,
                c.access.value_2 row 0, c.access.value_3 row 0,
                air.cols.instruction.op_a_is_x0 row 0, air.cols.opcode_selector.is_memory row 0,
                air.public_values 48, air.cols.clk row 0 ]) ]
    := rfl

    /-- The operations a register-register ALU row's messages stand for (no class selector,
        both operands registers), in order: the pc read, a read and write back of `rs1` and of
        `rs2`, the read of `rd`'s old value and the write of the result, and the next pc. -/
    private lemma CPU_bus_operations_eq_of_reg_reg
      [Field ExtF]
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
    :
      CPU_bus_operations air row =
        [ .ReadPC (U64w.toBV (pc air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_c_0 row 0).val)
            (U64w.toBV (op_c_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_c_0 row 0).val)
            (U64w.toBV (op_c_value air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_prev_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC (U64w.toBV (next_pc air row)) ]
    := by
      obtain ⟨ h_row, h_is_real, h_all_wf, -, -, h_opcode, h_class ⟩ := h
      have h_wf := h_all_wf row h_row
      subst h_opcode
      have h_no_mem := mem_width_of_opcode_eq_none_of_class_selectors h_class
      obtain ⟨ h_reg_rd, h_reg_rs1, h_reg_rs2 ⟩ := register_indices_lt air row h_is_real h_wf
      rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
          deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
          deserialise_raw_bus_row_Memory]
      simp [MemoryBusEntry.deserialise, h_no_mem, h_is_real, h_imm_b, h_imm_c,
            h_reg_rd, h_reg_rs1 h_imm_b, h_reg_rs2 h_imm_c, BitVec.ofNatLT_eq_ofNat,
            toBV_pc_eq_ofNat air row h_is_real h_wf,
            op_a_prev_value, op_a_value, op_b_value, op_c_value]

    /-- The operations a row's messages stand for when `op_b` is a register (`imm_b = 0`),
        `op_c` is the instruction's immediate (`imm_c = 1`) and the opcode has no memory width,
        in order: the pc read, a read and write back of `rs1`, the read of `op_a`'s old value
        and the write of its new one, and the next pc. `op_c` sends no message.

        A register-immediate ALU row is one such row, and so is a branch row, whose `op_a` is
        `rs2` and whose `op_c` is the offset. -/
    lemma CPU_bus_operations_eq_of_imm_c_eq_one
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_width : mem_width_of_opcode (air.cols.instruction.opcode row 0) = none)
    :
      CPU_bus_operations air row =
        [ .ReadPC (U64w.toBV (pc air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
            (U64w.toBV (op_b_value air row)),
          .ReadReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_prev_value air row)),
          .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC (U64w.toBV (next_pc air row)) ]
    := by
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
          deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
          deserialise_raw_bus_row_Memory]
      simp [MemoryBusEntry.deserialise, h_width, h_is_real, h_imm_b, h_imm_c,
            h_reg_rd, h_reg_rs1 h_imm_b, BitVec.ofNatLT_eq_ofNat,
            toBV_pc_eq_ofNat air row h_is_real h_wf,
            op_a_prev_value, op_a_value, op_b_value]

    /-- The write of an ALU row's result. For any value `v` that the ALU chip's promise for
        the row's opcode pins to the `op_a` value, writing `v` to `rd` leaves the state that
        writing the `op_a` value does. When the destination is `x0` the chip sends no ALU
        message, so there is no promise, and neither write changes the state. Otherwise the
        message is sent (`alu_message_spec`). It takes no immediate flag, so a `LUI` or `AUIPC`
        theorem can use it as well. -/
    lemma operation_list_effect_state_writeReg_eq_op_a_value
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
      (v : BitVec 64)
      (h_v : alu_promise air row op v)
      (pc_val : BitVec 64)
    :
      (operation_list_effect
        [ .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val) v, .WritePC pc_val ]
        state).state =
      (operation_list_effect
        [ .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
            (U64w.toBV (op_a_value air row)),
          .WritePC pc_val ] state).state
    := by
      obtain ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, -, h_opcode, h_class ⟩ := h
      subst h_opcode
      by_cases h_rd0 : air.cols.instruction.op_a row 0 = 0
      · have h_zero :
            (regidx_to_fin (.Regidx (air.cols.instruction.op_a row 0).val)).val = 0 := by
          simp [regidx_to_fin, h_rd0]
        rw [operation_list_effect_state_writeReg_x0 (val := v) h_zero,
            operation_list_effect_state_writeReg_x0 (val := U64w.toBV (op_a_value air row))
              h_zero]
      · rw [h_v (alu_message_spec air row h_is_real (h_all_wf row h_row)
              (h_all_constraints row h_row) h_class h_rd0)]

    /-- An instruction theorem's whole close for a register-register ALU row (`imm_c = 0`), in
        one call. `exec` is the Sail step. `h_exec` rewrites it, given the reads Sail's
        specification takes (the pc, `rs1` and `rs2`, which this lemma reads off the row's
        messages), into "read the pc, `rs1` and `rs2`, write the next pc and `v` to `rd`", and
        `h_v` is the ALU chip's promise that pins `v` to the `op_a` value. Then `exec` is the
        state the row's messages leave. The row's `imm_b = 0` follows from `imm_c = 0`
        (`imm_b_eq_zero_of_imm_c_eq_zero`), so the caller does not supply it.

        The whole close is one lemma, with no other lemma about the row applied in the
        instruction file, because each application of a lemma about a CPU-chip row costs the
        instruction file several seconds to elaborate. -/
    lemma eq_operation_list_effect_state_of_reg_reg
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      {exec : EStateM.Result (Sail.Error exception)
        (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult}
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (v : BitVec 64)
      (h_exec :
        Sail.readReg Register.PC state = .ok (U64w.toBV (pc air row)) state →
        read_xreg (regidx_to_fin (.Regidx (air.cols.instruction.op_b_0 row 0).val)) state =
          .ok (U64w.toBV (op_b_value air row)) state →
        read_xreg (regidx_to_fin (.Regidx (air.cols.instruction.op_c_0 row 0).val)) state =
          .ok (U64w.toBV (op_c_value air row)) state →
        exec = (operation_list_effect
          [ .ReadPC (U64w.toBV (pc air row)),
            .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
              (U64w.toBV (op_b_value air row)),
            .ReadReg (.Regidx (air.cols.instruction.op_c_0 row 0).val)
              (U64w.toBV (op_c_value air row)),
            .WritePC (U64w.toBV (pc air row) + 4#64),
            .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val) v ] state).state)
      (h_v : alu_promise air row op v)
    :
      exec = (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_ops := CPU_bus_operations_eq_of_reg_reg h
        (imm_b_eq_zero_of_imm_c_eq_zero air row h.is_real (h.all_wf row h.row_le) h_imm_c) h_imm_c
      -- The reads Sail's specification takes: the pc, `rs1` and `rs2`, from the row's messages.
      rw [h_ops, operation_list_effect_hypotheses_readPC] at h_bus_hypotheses
      obtain ⟨ h_pc, h_bus ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_readReg] at h_bus
      obtain ⟨ h_rs1, h_bus ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same h_rs1,
          operation_list_effect_hypotheses_readReg] at h_bus
      have h_rs2 := h_bus.1
      -- Each side, down to its write of `rd` and of the next pc. The row writes each register
      -- operand back unchanged, and its next pc is `pc + 4`.
      rw [h_exec h_pc h_rs1 h_rs2, h_ops]
      conv_lhs =>
        rw [operation_list_effect_state_readPC, operation_list_effect_state_readReg,
            operation_list_effect_state_readReg, operation_list_effect_state_swap_writePC_writeReg]
      conv_rhs =>
        rw [operation_list_effect_state_readPC, operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same h_rs1, operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same h_rs2, operation_list_effect_state_readReg,
            h.toBV_next_pc_eq]
      exact operation_list_effect_state_writeReg_eq_op_a_value h v h_v _

    set_option hygiene false in
    /-- The proof of a register-register ALU instruction theorem: introduce its `rd`, `rs1` and
        `rs2`, build the row's `ALURowFacts` as `h_alu`, make the one call to
        `eq_operation_list_effect_state_of_reg_reg`, whose Sail side is the opcode's
        specification lemma, and close the opcode's arm of `ALUBus.Spec` by `simp`. `h_op` proves
        the row's opcode and `h_imm_c` its `imm_c = 0`; `h_imm_c` may use `h_alu`, as
        `h_alu.imm_c_eq_zero rfl` does for an opcode no immediate form shares. `equiv` and
        `hyps` are the opcode's Sail lemmas `execute_<OP>_equiv` and `spec_<OP>_hypotheses`;
        `extra` names further `simp` lemmas for the arm, such as the class's `execute_*_pure`.

        The arm is passed to `simp` whole, so the proof does not depend on how `simp` orders
        its conjuncts (the result range, the operand range and the result equation). Hygiene
        is off so the tactic can name the theorem's hypotheses (`h_row`, `h_is_real`,
        `h_all_wf`, `h_all_constraints`, `pico_assumptions`, `h_bus_hypotheses`), which every
        such theorem declares under the same names. -/
    macro "alu_reg_reg_close " h_op:term:max h_imm_c:term:max equiv:ident hyps:ident
        " [" extra:ident,* "]" : tactic => `(tactic| (
      intro rd rs1 rs2
      have h_alu : ALURowFacts air row _ :=
        ⟨ h_row, h_is_real, h_all_wf, h_all_constraints, pico_assumptions, $h_op, rfl ⟩
      refine eq_operation_list_effect_state_of_reg_reg h_alu $h_imm_c h_bus_hypotheses _
        (fun h_pc h_rs1 h_rs2 => $equiv:ident
          (by rw [$hyps:ident]; exact ⟨ h_pc, h_rs1, h_rs2 ⟩))
        (fun h_spec => ?_)
      simp [alu_spec_of_row, RV64IM_Interactions.ALUBus.Spec] at h_spec
      simp [op_a_value, op_b_value, op_c_value, h_spec, $[$extra:ident],*]))

    /-- `eq_operation_list_effect_state_of_reg_reg` for a register-immediate ALU row
        (`imm_b = 0`, `imm_c = 1`): one register read, `rs1`. It takes `imm_b = 0` because
        `imm_c = 1` does not fix it: opcode 0 with `imm_c = 1` is `ADDI` when `imm_b = 0` and
        `LUI` or `AUIPC` when `imm_b = 1` (`ProgramBusEntry.decoded_from` at 0). Where the
        decoder fixes it, `ALURowFacts.imm_b_eq_zero` gives it. -/
    lemma eq_operation_list_effect_state_of_reg_imm
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      {exec : EStateM.Result (Sail.Error exception)
        (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult}
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB}
      (h : ALURowFacts air row op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (v : BitVec 64)
      (h_exec :
        Sail.readReg Register.PC state = .ok (U64w.toBV (pc air row)) state →
        read_xreg (regidx_to_fin (.Regidx (air.cols.instruction.op_b_0 row 0).val)) state =
          .ok (U64w.toBV (op_b_value air row)) state →
        exec = (operation_list_effect
          [ .ReadPC (U64w.toBV (pc air row)),
            .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val)
              (U64w.toBV (op_b_value air row)),
            .WritePC (U64w.toBV (pc air row) + 4#64),
            .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val) v ] state).state)
      (h_v : alu_promise air row op v)
    :
      exec = (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_ops := CPU_bus_operations_eq_of_imm_c_eq_one air row h.is_real
        (h.all_wf row h.row_le) h_imm_b h_imm_c
        (h.opcode_eq ▸ mem_width_of_opcode_eq_none_of_class_selectors h.class_selectors)
      rw [h_ops, operation_list_effect_hypotheses_readPC] at h_bus_hypotheses
      obtain ⟨ h_pc, h_bus ⟩ := h_bus_hypotheses
      rw [operation_list_effect_hypotheses_readReg] at h_bus
      have h_rs1 := h_bus.1
      rw [h_exec h_pc h_rs1, h_ops]
      conv_lhs =>
        rw [operation_list_effect_state_readPC, operation_list_effect_state_readReg,
            operation_list_effect_state_swap_writePC_writeReg]
      conv_rhs =>
        rw [operation_list_effect_state_readPC, operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same h_rs1, operation_list_effect_state_readReg,
            h.toBV_next_pc_eq]
      exact operation_list_effect_state_writeReg_eq_op_a_value h v h_v _

    /-- Cutting a sign extension back to the immediate's own width returns the immediate. An
        instruction theorem that reads its `imm` back from an operand column, where the decoder
        put it sign-extended to 64 bits, uses it at the immediate's width. -/
    lemma setWidth_signExtend_self {w : ℕ} (imm : BitVec w) (hw : w ≤ 64) :
      (BitVec.signExtend 64 imm).setWidth w = imm
    := by
      ext i hi
      simp [BitVec.getElem_setWidth]
      rw [BitVec.getLsbD_signExtend]
      simp [hi]
      omega

    /-- On a row of `ADDI`, `XORI`, `ORI`, `ANDI`, `SLTI`, `SLTIU` (opcodes 0, 2, 3, 4, 8, 9 with
        `imm_b = 0`, `imm_c = 1`) or `ADDIW` (40 with `imm_c = 1`), the `op_c` value is the
        sign extension of its own low 12 bits: the decoder writes the instruction's 12-bit
        immediate there, sign-extended (`Transpiler.V3.imm_operand`, constraints 4 to 7). The
        `ITYPE` and `ADDIW` theorems read `imm` from the instruction's `op_c_0`; they rewrite
        the low 12 bits on the right with `op_c_value_setWidth_eq_op_c_0` and use the result to
        recover the 64-bit value Sail adds or compares. -/
    lemma op_c_value_eq_signExtend_imm12
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {op : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = op)
      (h_op : op = 0 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 8 ∨ op = 9 ∨ op = 40)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      U64w.toBV (op_c_value air row) =
        BitVec.signExtend 64 ((U64w.toBV (op_c_value air row)).setWidth 12)
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      have h_imm : ∃ imm' : BitVec 12,
          air.cols.instruction.op_c_0 row 0 = (Transpiler.V3.imm_operand imm' true)[0] ∧
          air.cols.instruction.op_c_1 row 0 = (Transpiler.V3.imm_operand imm' true)[1] ∧
          air.cols.instruction.op_c_sign row 0 = (Transpiler.V3.imm_operand imm' true)[2] := by
        subst h_opcode
        rcases h_op with h | h | h | h | h | h | h <;>
        ( simp [ProgramBusEntry.decoded_from, h, h_imm_b, h_imm_c] at h_decoded
          obtain ⟨ imm', rs1', rd', h_eq_instr ⟩ := h_decoded
          subst h_eq_instr
          simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
          obtain ⟨ h_eq_data, - ⟩ := h_eq
          subst h_eq_data
          rw [deserialise_program_bus_entry] at h_eq_entry
          simp [ProgramBusEntry.deserialise] at h_eq_entry
          exact ⟨ imm', by simp [h_eq_entry], by simp [h_eq_entry], by simp [h_eq_entry] ⟩ )
      obtain ⟨ imm', eq_c0, eq_c1, eq_cs ⟩ := h_imm
      have h_imm_c_eqs := imm_c_eq_1_constraints air row h_imm_c h_constraints
      have h_op_c_bv : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm' := by
        simp only [op_c_value, h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1,
                   h_imm_c_eqs.2.2.2, eq_c0, eq_c1, eq_cs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)
      rw [h_op_c_bv, setWidth_signExtend_self imm' (by norm_num)]

    /-- On a row whose `op_c` is an immediate (`imm_c = 1`), the low `n ≤ 16` bits of the `op_c`
        value the row sends to the ALU chip are those of the instruction's encoded `op_c_0`
        (constraint 4, through `imm_c_eq_1_constraints`). The register-immediate theorems read
        their immediate from `op_c_0`, as they read `rd` and `rs1` from the instruction, and use
        this lemma to reach the value the ALU chip works on: the shifts at `n` = 6 or 5, the
        `ITYPE` and `ADDIW` theorems at `n` = 12. -/
    lemma op_c_value_setWidth_eq_op_c_0
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {n : ℕ} (hn : n ≤ 16)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_constraints : CpuChip.Extraction.allHold air row)
    :
      (U64w.toBV (op_c_value air row)).setWidth n =
        ((air.cols.instruction.op_c_0 row 0).val : BitVec n)
    := by
      have h_c0 := (imm_c_eq_1_constraints air row h_imm_c h_constraints).1
      ext i hi
      have hi16 : i < 16 := by omega
      simp [op_c_value, h_c0, U64w.toBV, BitVec.getElem_setWidth]
      rw [BitVec.getLsbD_append]
      simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
      simp [hi16, hi]

    /-- `eq_operation_list_effect_state_of_reg_imm` for a shift by an immediate amount
        (`SLLI`, `SRLI`, `SRAI`, `SLLIW`, `SRLIW`, `SRAIW`). The theorem reads the amount from
        the instruction's encoded `op_c_0`, cut to the shift's `n` bits, as it reads `rd` and
        `rs1`; the ALU chip shifts by the low `n` bits of the `op_c` value the row sends.
        `op_c_value_setWidth_eq_op_c_0` shows the two agree, so the caller gives the Sail step
        (`h_exec`, from the opcode's `execute_*_equiv`) with the amount from `op_c_0`, and the
        ALU chip's arm for its opcode (`h_shift`) with the amount from `op_c`. `shift` is the
        result Sail writes to `rd`, as a function of `rs1`'s value and the amount. -/
    lemma eq_operation_list_effect_state_of_shift_imm
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      {exec : EStateM.Result (Sail.Error exception)
        (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult}
      {air : Valid_CpuChip FKB ExtF} {row : ℕ} {op : FKB} {n : ℕ}
      (hn : n ≤ 16)
      (h : ALURowFacts air row op)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (shift : BitVec 64 → BitVec n → BitVec 64)
      (h_exec : ∀ pc_val rs1_val : BitVec 64,
        Sail.readReg Register.PC state = .ok pc_val state ∧
        read_xreg (regidx_to_fin (.Regidx (air.cols.instruction.op_b_0 row 0).val)) state =
          .ok rs1_val state →
        exec = (operation_list_effect
          [ .ReadPC pc_val,
            .ReadReg (.Regidx (air.cols.instruction.op_b_0 row 0).val) rs1_val,
            .WritePC (pc_val + 4#64),
            .WriteReg (.Regidx (air.cols.instruction.op_a row 0).val)
              (shift rs1_val ((air.cols.instruction.op_c_0 row 0).val : BitVec n)) ] state).state)
      (h_shift : alu_spec_of_row air row op →
        shift (U64w.toBV (op_b_value air row)) ((U64w.toBV (op_c_value air row)).setWidth n) =
          U64w.toBV (op_a_value air row))
    :
      exec = (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      rw [← op_c_value_setWidth_eq_op_c_0 air row hn h_imm_c (h.all_constraints row h.row_le)]
        at h_exec
      exact eq_operation_list_effect_state_of_reg_imm h h_imm_b h_imm_c h_bus_hypotheses _
        (fun h_pc h_rs1 => h_exec _ _ ⟨ h_pc, h_rs1 ⟩) (fun h_spec => h_shift h_spec)

  end Auxiliaries

end Equivalence
