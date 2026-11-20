import PicoFV.RV64IM.Equivalence.Common

/-! # NOT FOR MERGE — the two U-type statements, for review before the proofs

    Every proof here is `sorry`. The file is not imported by `PicoFV64.lean` and its theorem
    list is still parked, so no check sees it; `check.sh`, the axiom lists and the tactic
    ratchet are unaffected. It exists so the statements can be read and agreed before the
    proofs are written, which is what the U-type needs: `LUI` and `AUIPC` share an opcode at
    v3.1.1, so how to tell them apart is a design decision and not a proof detail.

    The proofs follow in the same pull request once the statements are settled. -/

set_option maxHeartbeats 1_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section UTYPE

    -- ========================================================================
    -- UTYPE — `LUI` and `AUIPC`. Both are opcode 0 with both immediate flags
    -- set, and v3.1.1 has no `is_auipc` selector and no opcode 27, so the
    -- opcode and the flags no longer tell them apart: a `LUI` row and an
    -- `AUIPC` row have the same shape, and the decoder's clause for opcode 0
    -- (`ProgramBusEntry.decoded_from`) is a disjunction of the two.
    --
    -- What tells them apart is where the row carries the 32-bit immediate
    -- `imm ++ 0#12`:
    --
    --   * `LUI`   — `op_b` is zero and `op_c` is the immediate;
    --   * `AUIPC` — `op_b` is the immediate and `op_c` is the row's pc.
    --
    -- Either way the row is an ALU row of opcode 0, so the ALU chip's promise
    -- makes `op_a` the sum `op_b + op_c`: the immediate for `LUI`, and
    -- `pc + immediate` for `AUIPC`. Each theorem therefore takes the shape
    -- its instruction has, and `utype_row_cases` shows the two shapes cover
    -- every such row, so the pair says as much about opcode 0 as the two 2.x
    -- theorems said about opcodes 0 and 27.
    --
    -- The shapes are not exclusive: a row whose pc is a multiple of `2 ^ 12`
    -- can be read as either, and both theorems then hold of it, because
    -- `LUI imm` and `AUIPC imm'` agree exactly there.
    -- ========================================================================

    /-- Every row of opcode 0 with both immediate flags set has one of the two U-type shapes:
        `op_b` zero with the immediate in `op_c` (`LUI`), or the immediate in `op_b` with the
        row's pc in `op_c` (`AUIPC`). This is the decoder's clause for opcode 0 read through
        the constraints that tie the operand values to the instruction's columns, and it is
        what makes `equivalence_LUI` and `equivalence_AUIPC` together cover the opcode. -/
    theorem utype_row_cases
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
    :
      (∃ imm : BitVec 20,
        U64w.toBV (op_b_value air row) = 0#64 ∧
        U64w.toBV (op_c_value air row) = BitVec.signExtend 64 (imm ++ 0#12)) ∨
      (∃ imm : BitVec 20,
        U64w.toBV (op_b_value air row) = BitVec.signExtend 64 (imm ++ 0#12) ∧
        U64w.toBV (op_c_value air row) = U64w.toBV (pc air row))
    := by
      sorry

    /-- Equivalence for LUI (opcode 0 with `imm_b = 1` and `imm_c = 1`, `op_b` zero).

        Against 2.x this gains the whole-trace assumption, names the v3.1.1 contracts, reads
        `rd` from `op_a` instead of `op_a_0`, and takes the row's `LUI` shape: at 2.x opcode 0
        with both flags was `LUI` alone, and at v3.1.1 it is `LUI` or `AUIPC`
        (`utype_row_cases`). The immediate is a parameter pinned by that shape rather than cut
        out of `op_c` as at 2.x; `BitVec.signExtend 64 (imm ++ 0#12)` determines `imm`, so the
        two forms say the same thing. -/
    theorem equivalence_LUI
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (imm : BitVec 20)
      (h_op_b : U64w.toBV (op_b_value air row) = 0#64)
      (h_op_c : U64w.toBV (op_c_value air row) = BitVec.signExtend 64 (imm ++ 0#12))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      sorry

    /-- Equivalence for AUIPC (opcode 0 with `imm_b = 1` and `imm_c = 1`, `op_c` the row's pc).

        Against 2.x this is keyed on opcode 0 instead of opcode 27, which v3.1.1 never emits,
        and drops `is_auipc = 1`, a column the v3.1.1 chip does not have. It gains the
        whole-trace assumption, names the v3.1.1 contracts, reads `rd` from `op_a`, and takes
        the row's `AUIPC` shape in place of the opcode that used to identify it. -/
    theorem equivalence_AUIPC
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_is_real : air.cols.is_real row 0 = 1)
      (_h_all_axioms : ∀ row ≤ air.last_row, bus_row_axioms (bus_row air row))
      (_h_all_ext : ∀ row ≤ air.last_row, bus_row_ext_asm (bus_row air row))
      (h_all_wf : ∀ row ≤ air.last_row, bus_row_wf_asm (bus_row air row))
      (_h_all_wf_asrt : ∀ row ≤ air.last_row, bus_row_wf_asrt (bus_row air row))
      (h_all_constraints : ∀ row ≤ air.last_row, CpuChip.Extraction.allHold air row)
      (pico_assumptions : pico_CpuChip_control_flow_assumptions air)
      (h_opcode : air.cols.instruction.opcode row 0 = 0 ∧
                  air.cols.opcode_selector.imm_b row 0 = 1 ∧
                  air.cols.opcode_selector.imm_c row 0 = 1)
      (imm : BitVec 20)
      (h_op_b : U64w.toBV (op_b_value air row) = BitVec.signExtend 64 (imm ++ 0#12))
      (h_op_c : U64w.toBV (op_c_value air row) = U64w.toBV (pc air row))
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (_risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      sorry

  end UTYPE

end Equivalence
