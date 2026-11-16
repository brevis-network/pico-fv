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

  end Auxiliaries

end Equivalence
