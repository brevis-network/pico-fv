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

The pc-alignment proof that the 2.x file also held (`pc_next_row_mod_four_eq_zero`,
`next_pc_mod_four_eq_zero`) is not here: it splits over every instruction class and calls the
branch and jump lemmas, which come with those classes. Only the branch and jump theorems use
it.
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

    /-- Everything an ALU-class row needs about its control flow in one step: all eleven
        class selectors are zero, the halt flag is zero, and the next pc is `pc + 4`. A caller
        discharges `h_class` for its opcode by `rw [h_opcode]; rfl`. Whether the row sends its
        ALU message is `CpuChip.Interpretations.alu_message_spec`. -/
    lemma alu_row_facts
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_class : class_selectors_of_opcode (air.cols.instruction.opcode row 0).val =
        #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
    :
      (air.cols.opcode_selector.is_ecall row 0 = 0 ∧
       air.cols.opcode_selector.is_memory row 0 = 0 ∧
       air.cols.opcode_selector.is_store row 0 = 0 ∧
       air.cols.opcode_selector.is_beq row 0 = 0 ∧
       air.cols.opcode_selector.is_bne row 0 = 0 ∧
       air.cols.opcode_selector.is_blt row 0 = 0 ∧
       air.cols.opcode_selector.is_bge row 0 = 0 ∧
       air.cols.opcode_selector.is_bltu row 0 = 0 ∧
       air.cols.opcode_selector.is_bgeu row 0 = 0 ∧
       air.cols.opcode_selector.is_jalr row 0 = 0 ∧
       air.cols.opcode_selector.is_jal row 0 = 0) ∧
      air.cols.is_halt row 0 = 0 ∧
      U64w.toBV (next_pc air row) = U64w.toBV (pc air row) + 4#64
    := by
      obtain ⟨ h_ecall, h_mem, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ :=
        alu_class_selectors_zero air row h_is_real (h_wf row h_row) h_class
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall (h_constraints row h_row)
      exact ⟨ ⟨ h_ecall, h_mem, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_jalr,
                h_jal ⟩, h_halt,
        is_sequential_active_constraints air row h_row h_is_real h_wf h_constraints
          pico_assumptions ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt ⟩

    /-- `imm_b` is 0 on a real row whose opcode the decoder always gives a register `op_b`
        (`imm_b_of_opcode` is `some 0`: every opcode but 0 and `JAL`'s 24). -/
    lemma imm_b_eq_zero_of_opcode
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_op : imm_b_of_opcode (air.cols.instruction.opcode row 0).val = some 0)
    :
      air.cols.opcode_selector.imm_b row 0 = 0
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h := (ProgramBusEntry.inversion h_eq h_eq_entry).imm_b
      rw [deserialise_program_bus_entry] at h
      exact h 0 h_op

    /-- Everything a register-register ALU row gives its instruction theorem, for any of the
        opcodes `op` such a row carries (no class selector, no memory width, both operands
        registers):

        - the three reads Sail's specification of the instruction takes: the pc, `rs1` (the
          `op_b` value) and `rs2` (the `op_c` value);
        - for any result `v` the ALU chip's promise for `op` pins to the `op_a` value, the
          Sail operations "read the pc, `rs1` and `rs2`, write the next pc and `v` to `rd`"
          leave the state the row's messages leave.

        When the destination is `x0` the chip sends no ALU message, so there is no promise, and
        both sides' writes to `x0` change nothing. Otherwise the message is sent
        (`alu_message_spec`) and `v` is the value the row writes. An instruction theorem
        rewrites with its Sail specification lemma and is left with one fact about its
        opcode's arm of `ALUBus.Spec`. -/
    lemma alu_reg_reg_row
      [Field ExtF]
      {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {op : FKB}
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = op)
      (h_class : class_selectors_of_opcode op.val = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
      (h_no_mem : mem_width_of_opcode op = none)
      (h_imm_b : air.cols.opcode_selector.imm_b row 0 = 0)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 0)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let rs2 : regidx := .Regidx (air.cols.instruction.op_c_0 row 0).val
      Sail.readReg Register.PC state = .ok (U64w.toBV (pc air row)) state ∧
      read_xreg (regidx_to_fin rs1) state = .ok (U64w.toBV (op_b_value air row)) state ∧
      read_xreg (regidx_to_fin rs2) state = .ok (U64w.toBV (op_c_value air row)) state ∧
      ∀ v : BitVec 64,
        (RV64IM_Interactions.ALUBus.Spec op
          (air.cols.op_a_access.access.value_0 row 0) (air.cols.op_a_access.access.value_1 row 0)
          (air.cols.op_a_access.access.value_2 row 0) (air.cols.op_a_access.access.value_3 row 0)
          (air.cols.op_b_access.access.value_0 row 0) (air.cols.op_b_access.access.value_1 row 0)
          (air.cols.op_b_access.access.value_2 row 0) (air.cols.op_b_access.access.value_3 row 0)
          (air.cols.op_c_access.access.value_0 row 0) (air.cols.op_c_access.access.value_1 row 0)
          (air.cols.op_c_access.access.value_2 row 0) (air.cols.op_c_access.access.value_3 row 0) →
          v = U64w.toBV (op_a_value air row)) →
        (operation_list_effect
          [ .ReadPC (U64w.toBV (pc air row)),
            .ReadReg rs1 (U64w.toBV (op_b_value air row)),
            .ReadReg rs2 (U64w.toBV (op_c_value air row)),
            .WritePC (U64w.toBV (pc air row) + 4#64),
            .WriteReg rd v ] state).state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      intro rd rs1 rs2
      subst h_opcode
      have h_wf : bus_row_wf_asm (bus_row air row) := h_all_wf row h_row
      -- The row is an ALU row: no class selector, no halt, `next_pc = pc + 4`.
      obtain ⟨ h_sel, -, h_next_pc ⟩ := alu_row_facts air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions h_class
      have h_s_mem := h_sel.2.1
      -- The decoder writes register indices below 32 for `op_a` and both register operands.
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_ops := ProgramBusEntry.inversion_operands h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_ops
      simp only [h_imm_b, h_imm_c, forall_const] at h_ops
      obtain ⟨ h_reg_rd, -, ⟨ h_reg_rs1, -, - ⟩, ⟨ h_reg_rs2, -, - ⟩, - ⟩ := h_ops
      -- The row's messages, as operations on the Sail state: the pc read, a read and write
      -- back of each register operand, the read and write of `rd`, and the next pc.
      have h_bus := h_bus_hypotheses
      simp [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, deserialise_bus_row,
            raw_bus_row, MemoryBusEntry.deserialise, h_no_mem,
            h_is_real, h_imm_b, h_imm_c, h_s_mem, h_reg_rd, h_reg_rs1, h_reg_rs2] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_c, - ⟩ := h_rest
      have h_pc_bounds := pc_facts air row h_is_real h_wf
      have h_pc : Sail.readReg Register.PC state = .ok (U64w.toBV (pc air row)) state := by
        rw [h_pc_read]
        congr 1
        simp [pc, ← BitVec.toNat_inj, U64w.toNat]
        omega
      refine ⟨ h_pc, by simpa [rs1, op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b,
        by simpa [rs2, op_c_value, BitVec.ofNatLT_eq_ofNat] using h_read_c, ?_ ⟩
      intro v h_v
      simp [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations, deserialise_bus_row,
            raw_bus_row, MemoryBusEntry.deserialise, h_no_mem,
            h_is_real, h_imm_b, h_imm_c, h_s_mem, h_reg_rd, h_reg_rs1, h_reg_rs2,
            rd, BitVec.ofNatLT_eq_ofNat]
      rw [operation_list_effect_state_swap_writePC_writeReg]
      -- The row writes each register operand back unchanged.
      conv =>
        rhs
        rw [operation_list_effect_state_writeReg_same
              (by simpa [BitVec.ofNatLT_eq_ofNat] using h_read_b),
            operation_list_effect_state_readReg,
            operation_list_effect_state_writeReg_same
              (by simpa [BitVec.ofNatLT_eq_ofNat] using h_read_c),
            operation_list_effect_state_readReg]
      rw [h_next_pc]
      by_cases h_rd0 : air.cols.instruction.op_a row 0 = 0
      · -- The destination is `x0`: neither write changes the state.
        have h_rd0' : (air.cols.instruction.op_a row 0).val = 0 := by simp [h_rd0]
        rw [operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0']),
            operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin, h_rd0'])]
      · -- The destination is not `x0`: the chip sends its ALU message, and `v` is its result.
        rw [h_v (alu_message_spec air row h_is_real h_wf (h_all_constraints row h_row) h_class
          h_rd0)]
        simp [op_a_value]

  end Auxiliaries

end Equivalence
