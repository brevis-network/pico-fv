import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 6_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section LOADS

    -- ========================================================================
    -- LOADS — the seven load opcodes: LB = 10, LH = 11, LW = 12, LBU = 13,
    -- LHU = 14, LWU = 45, LD = 46. None is shared
    -- (`ProgramBusEntry.decoded_from`), so the decoder fixes both immediate
    -- flags and the row's class selectors, and no statement takes them, as
    -- none did at 2.x either.
    --
    -- A load row reads `rs1` into `op_b`, carries the 12-bit offset in `op_c`
    -- (`imm_c = 1`), and writes the loaded word into `op_a`. It sends one
    -- Memory message (Pico v3.1.6, `riscv_cpu/constraints.rs:117-133`), whose
    -- promise (`memory_message_spec`) puts the address `op_b + op_c` below
    -- `2 ^ 32`, inside the memory region `RISC_V_assumptions` gives Sail, and
    -- gives the loaded word the opcode's extension — sign for `LB`, `LH` and
    -- `LW`, zero for `LBU`, `LHU` and `LWU`, none for `LD`. The extension is
    -- what Sail writes to `rd`. The promise says nothing about alignment: at
    -- an address that is not a multiple of the width Sail splits the load
    -- into aligned pieces, which the Sail lemmas of `LH`, `LHU`, `LW`, `LWU`
    -- and `LD` cover (`RVSail/Misaligned.lean`). The row sets no branch or
    -- jump selector, so its next pc is `pc + 4`
    -- (`is_sequential_active_constraints`; Pico v3.1.6,
    -- `riscv_cpu/constraints.rs:318-326`).
    --
    -- Each theorem splits on whether the destination is `x0`. There the row
    -- writes zero to `x0` (Pico v3.1.6, `riscv_cpu/register/constraints.rs:73-76`)
    -- and sends `ReadMemAny`, and Sail's write to `x0` changes nothing;
    -- elsewhere both read the same bytes and write the same extension.
    -- ========================================================================

    /-- The low 8 bits of a `U64w`'s value are those of its first limb. -/
    private lemma toBV_setWidth_8 (w : U64w) :
      (U64w.toBV w).setWidth 8 = (w[0]).setWidth 8
    := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, U64w.toBV_toNat, U64w.toNat]
      omega

    /-- The low 16 bits of a `U64w`'s value are its first limb. -/
    private lemma toBV_setWidth_16 (w : U64w) :
      (U64w.toBV w).setWidth 16 = w[0]
    := by
      apply BitVec.eq_of_toNat_eq
      have h0 := (w[0]).isLt
      simp only [BitVec.toNat_setWidth, U64w.toBV_toNat, U64w.toNat]
      omega

    /-- A halfword is its two bytes, high then low. Sail's load specifications take the loaded
        value as single bytes and append them; the chip's Memory message carries it whole, so
        each proof passes the slices and folds them back with one of these. -/
    private lemma eq_append_bytes_16 (x : BitVec 16) :
      x = BitVec.extractLsb' 8 8 x ++ BitVec.extractLsb' 0 8 x
    := by
      repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
      all_goals simp

    /-- A word is its four bytes. -/
    private lemma eq_append_bytes_32 (x : BitVec 32) :
      x = BitVec.extractLsb' 24 8 x ++ BitVec.extractLsb' 16 8 x ++
          BitVec.extractLsb' 8 8 x ++ BitVec.extractLsb' 0 8 x
    := by
      repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
      all_goals simp

    /-- A doubleword is its eight bytes. -/
    private lemma eq_append_bytes_64 (x : BitVec 64) :
      x = BitVec.extractLsb' 56 8 x ++ BitVec.extractLsb' 48 8 x ++
          BitVec.extractLsb' 40 8 x ++ BitVec.extractLsb' 32 8 x ++
          BitVec.extractLsb' 24 8 x ++ BitVec.extractLsb' 16 8 x ++
          BitVec.extractLsb' 8 8 x ++ BitVec.extractLsb' 0 8 x
    := by
      repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
      all_goals simp

    /-- A load row's flags and selectors, as its opcode fixes them (`selector_exclusivity`). -/
    private lemma load_row_selectors
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ) {op : FKB}
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_opcode : air.cols.instruction.opcode row 0 = op)
      (h_b : imm_b_of_opcode op.val = some 0)
      (h_c : imm_c_of_opcode op.val = some 1)
    :
      air.cols.opcode_selector.imm_b row 0 = 0 ∧
      air.cols.opcode_selector.imm_c row 0 = 1 ∧
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
        class_selectors_of_opcode op.val
    := by
      obtain ⟨ h_sel, h_imm_b, h_imm_c ⟩ :=
        selector_exclusivity air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)
      rw [h_opcode] at h_sel h_imm_b h_imm_c
      exact ⟨ h_imm_b 0 h_b, h_imm_c 1 h_c, h_sel ⟩

    /-- A load row's offset: the Program message says the row's `op_c` columns encode a 12-bit
        immediate `imm'`, and `op_c` is then its 64-bit sign extension (constraints 4 to 7,
        through `imm_c_eq_1_constraints`). The seven opcodes share one proof. -/
    private lemma load_offset
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 10 ∨
                  air.cols.instruction.opcode row 0 = 11 ∨
                  air.cols.instruction.opcode row 0 = 12 ∨
                  air.cols.instruction.opcode row 0 = 13 ∨
                  air.cols.instruction.opcode row 0 = 14 ∨
                  air.cols.instruction.opcode row 0 = 45 ∨
                  air.cols.instruction.opcode row 0 = 46)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ imm' : BitVec 12, U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm'
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      rcases h_opcode with h_op | h_op | h_op | h_op | h_op | h_op | h_op <;>
      · simp [ProgramBusEntry.decoded_from, h_op] at h_decoded
        obtain ⟨ imm', rs1', rd', h_eq_instr ⟩ := h_decoded
        subst h_eq_instr
        simp [Transpiler.V3.transpile_op, -Vector.eq_mk] at h_eq
        obtain ⟨ h_eq_data, - ⟩ := h_eq
        subst h_eq_data
        rw [deserialise_program_bus_entry] at h_eq_entry
        simp [ProgramBusEntry.deserialise] at h_eq_entry
        have eq_c0 : air.cols.instruction.op_c_0 row 0 =
            (Transpiler.V3.imm_operand imm' true)[0] := by simp [h_eq_entry]
        have eq_c1 : air.cols.instruction.op_c_1 row 0 =
            (Transpiler.V3.imm_operand imm' true)[1] := by simp [h_eq_entry]
        have eq_cs : air.cols.instruction.op_c_sign row 0 =
            (Transpiler.V3.imm_operand imm' true)[2] := by simp [h_eq_entry]
        refine ⟨ imm', ?_ ⟩
        have h_imm_c_eqs := imm_c_eq_1_constraints air row h_imm_c h_constraints
        simp only [op_c_value, h_imm_c_eqs.1, h_imm_c_eqs.2.1, h_imm_c_eqs.2.2.1,
                   h_imm_c_eqs.2.2.2, eq_c0, eq_c1, eq_cs]
        exact Transpiler.V3.imm_operand_toBV_sgn imm' (by norm_num) (by norm_num)

    /-- Equivalence for LW (opcode 12, `instruction.LOAD` of width 4, sign-extended). -/
    theorem equivalence_LW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 12)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 4)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 4 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LW_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8) (data1 := 0#8) (data2 := 0#8) (data3 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LW,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LW_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v32 := (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)) ++
                   (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0))
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.signExtend 64 v32 := by
          have h : U64w.toBV (op_a_value air row) =
              BitVec.signExtend 64 (BitVec.truncate 32 (U64w.toBV (op_a_value air row))) :=
            h_mem_spec.2.2.2.2.2.1 trivial h_a_is_x0
          have h32 : BitVec.truncate 32 (U64w.toBV (op_a_value air row)) = v32 := by
            rw [BitVec.truncate_eq_setWidth, U64w.setWidth_32_eq_low_U32w]
            simp [v32, op_a_value, U32w.toBV]
          rw [← h32]; exact h
        have h_append_eq := eq_append_bytes_32 v32
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LW_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := BitVec.extractLsb' 0 8 v32)
              (data1 := BitVec.extractLsb' 8 8 v32)
              (data2 := BitVec.extractLsb' 16 8 v32)
              (data3 := BitVec.extractLsb' 24 8 v32)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LW,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          have h_a_ext' : U64w.toBV
                #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                    (air.cols.op_a_access.access.value_1 row 0 : FKB),
                    (air.cols.op_a_access.access.value_2 row 0 : FKB),
                    (air.cols.op_a_access.access.value_3 row 0 : FKB) ] =
              BitVec.signExtend 64 v32 := h_a_ext
          simp [h_next_pc, op_b_value, h_a_ext']
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (try rw [← h_append_eq])
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LW_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.2.2.2

    /-- Equivalence for LB (opcode 10, `instruction.LOAD` of width 1, sign-extended). -/
    theorem equivalence_LB
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
      (h_opcode : air.cols.instruction.opcode row 0 = 10)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 1)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 1 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LB_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LB,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LB_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v8 := BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0)
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.signExtend 64 v8 := by
          have h : U64w.toBV (op_a_value air row) =
              BitVec.signExtend 64 (BitVec.truncate 8 (U64w.toBV (op_a_value air row))) :=
            h_mem_spec.2.2.2.1 trivial h_a_is_x0
          have h8 : BitVec.truncate 8 (U64w.toBV (op_a_value air row)) = v8 := by
            rw [BitVec.truncate_eq_setWidth, toBV_setWidth_8]
            simp [v8, op_a_value]
          rw [← h8]; exact h
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LB_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := v8)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LB,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          have h_a_ext' : U64w.toBV
                #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                    (air.cols.op_a_access.access.value_1 row 0 : FKB),
                    (air.cols.op_a_access.access.value_2 row 0 : FKB),
                    (air.cols.op_a_access.access.value_3 row 0 : FKB) ] =
              BitVec.signExtend 64 v8 := h_a_ext
          simp [h_next_pc, op_b_value, h_a_ext']
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LB_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v8] using h_mem

    /-- Equivalence for LH (opcode 11, `instruction.LOAD` of width 2, sign-extended). -/
    theorem equivalence_LH
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
      (h_opcode : air.cols.instruction.opcode row 0 = 11)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 2)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 2 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LH_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8) (data1 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LH,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LH_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v16 := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.signExtend 64 v16 := by
          have h : U64w.toBV (op_a_value air row) =
              BitVec.signExtend 64 (BitVec.truncate 16 (U64w.toBV (op_a_value air row))) :=
            h_mem_spec.2.2.2.2.1 trivial h_a_is_x0
          have h16 : BitVec.truncate 16 (U64w.toBV (op_a_value air row)) = v16 := by
            rw [BitVec.truncate_eq_setWidth, toBV_setWidth_16]
            simp [v16, op_a_value]
          rw [← h16]; exact h
        have h_append_eq := eq_append_bytes_16 v16
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LH_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := BitVec.extractLsb' 0 8 v16)
              (data1 := BitVec.extractLsb' 8 8 v16)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LH,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          have h_a_ext' : U64w.toBV
                #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                    (air.cols.op_a_access.access.value_1 row 0 : FKB),
                    (air.cols.op_a_access.access.value_2 row 0 : FKB),
                    (air.cols.op_a_access.access.value_3 row 0 : FKB) ] =
              BitVec.signExtend 64 v16 := h_a_ext
          simp [h_next_pc, op_b_value, h_a_ext']
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (try rw [← h_append_eq])
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LH_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v16] using h_mem.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v16] using h_mem.2

    /-- Equivalence for LBU (opcode 13, `instruction.LOAD` of width 1, zero-extended). -/
    theorem equivalence_LBU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 13)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, true, 1)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 1 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LBU_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LBU,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LBU_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v8 := BitVec.ofNat 8 ↑(air.cols.op_a_access.access.value_0 row 0)
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.zeroExtend 64 v8 := by
          have h : U64w.toBV (op_a_value air row) =
              BitVec.zeroExtend 64 (BitVec.truncate 8 (U64w.toBV (op_a_value air row))) :=
            h_mem_spec.2.2.2.2.2.2.1 trivial h_a_is_x0
          have h8 : BitVec.truncate 8 (U64w.toBV (op_a_value air row)) = v8 := by
            rw [BitVec.truncate_eq_setWidth, toBV_setWidth_8]
            simp [v8, op_a_value]
          rw [← h8]; exact h
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LBU_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := v8)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LBU,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          have h_a_ext' : U64w.toBV
                #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                    (air.cols.op_a_access.access.value_1 row 0 : FKB),
                    (air.cols.op_a_access.access.value_2 row 0 : FKB),
                    (air.cols.op_a_access.access.value_3 row 0 : FKB) ] =
              BitVec.zeroExtend 64 v8 := h_a_ext
          simp [h_next_pc, op_b_value, h_a_ext']
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LBU_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v8] using h_mem

    /-- Equivalence for LHU (opcode 14, `instruction.LOAD` of width 2, zero-extended). -/
    theorem equivalence_LHU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 14)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, true, 2)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 2 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LHU_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8) (data1 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LHU,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LHU_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v16 := BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0)
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.zeroExtend 64 v16 := by
          have h : U64w.toBV (op_a_value air row) =
              BitVec.zeroExtend 64 (BitVec.truncate 16 (U64w.toBV (op_a_value air row))) :=
            h_mem_spec.2.2.2.2.2.2.2.1 trivial h_a_is_x0
          have h16 : BitVec.truncate 16 (U64w.toBV (op_a_value air row)) = v16 := by
            rw [BitVec.truncate_eq_setWidth, toBV_setWidth_16]
            simp [v16, op_a_value]
          rw [← h16]; exact h
        have h_append_eq := eq_append_bytes_16 v16
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LHU_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := BitVec.extractLsb' 0 8 v16)
              (data1 := BitVec.extractLsb' 8 8 v16)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LHU,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          have h_a_ext' : U64w.toBV
                #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                    (air.cols.op_a_access.access.value_1 row 0 : FKB),
                    (air.cols.op_a_access.access.value_2 row 0 : FKB),
                    (air.cols.op_a_access.access.value_3 row 0 : FKB) ] =
              BitVec.zeroExtend 64 v16 := h_a_ext
          simp [h_next_pc, op_b_value, h_a_ext']
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (try rw [← h_append_eq])
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LHU_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v16] using h_mem.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v16] using h_mem.2

    /-- Equivalence for LWU (opcode 45, `instruction.LOAD` of width 4, zero-extended). -/
    theorem equivalence_LWU
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
      (h_opcode : air.cols.instruction.opcode row 0 = 45)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, true, 4)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 4 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LWU_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8) (data1 := 0#8) (data2 := 0#8) (data3 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LWU,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LWU_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v32 := (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_1 row 0)) ++
                   (BitVec.ofNat 16 ↑(air.cols.op_a_access.access.value_0 row 0))
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = BitVec.zeroExtend 64 v32 := by
          have h : U64w.toBV (op_a_value air row) =
              BitVec.zeroExtend 64 (BitVec.truncate 32 (U64w.toBV (op_a_value air row))) :=
            h_mem_spec.2.2.2.2.2.2.2.2 trivial h_a_is_x0
          have h32 : BitVec.truncate 32 (U64w.toBV (op_a_value air row)) = v32 := by
            rw [BitVec.truncate_eq_setWidth, U64w.setWidth_32_eq_low_U32w]
            simp [v32, op_a_value, U32w.toBV]
          rw [← h32]; exact h
        have h_append_eq := eq_append_bytes_32 v32
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LWU_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := BitVec.extractLsb' 0 8 v32)
              (data1 := BitVec.extractLsb' 8 8 v32)
              (data2 := BitVec.extractLsb' 16 8 v32)
              (data3 := BitVec.extractLsb' 24 8 v32)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LWU,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          have h_a_ext' : U64w.toBV
                #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                    (air.cols.op_a_access.access.value_1 row 0 : FKB),
                    (air.cols.op_a_access.access.value_2 row 0 : FKB),
                    (air.cols.op_a_access.access.value_3 row 0 : FKB) ] =
              BitVec.zeroExtend 64 v32 := h_a_ext
          simp [h_next_pc, op_b_value, h_a_ext']
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (try rw [← h_append_eq])
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LWU_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v32] using h_mem.2.2.2

    /-- Equivalence for LD (opcode 46, `instruction.LOAD` of width 8, no extension). -/
    theorem equivalence_LD
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
      (h_opcode : air.cols.instruction.opcode row 0 = 46)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rd  : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.LOAD (imm, rs1, rd, false, 8)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        load_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        load_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rd, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
      replace h_reg_rs1 := h_reg_rs1 h_imm_b
      -- The memory chip's promise for the dispatch this row sends.
      have h_mem_spec := memory_message_spec air row h_is_real h_wf h_memory
      simp only [MemoryBus.Spec, h_opcode] at h_mem_spec
      have h_addr_bridge : U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm' =
          U64w.toBV #v[ (air.cols.op_b_access.access.value_0 row 0 : FKB),
                        (air.cols.op_b_access.access.value_1 row 0 : FKB),
                        (air.cols.op_b_access.access.value_2 row 0 : FKB),
                        (air.cols.op_b_access.access.value_3 row 0 : FKB) ] +
          U64w.toBV #v[ (air.cols.op_c_access.access.value_0 row 0 : FKB),
                        (air.cols.op_c_access.access.value_1 row 0 : FKB),
                        (air.cols.op_c_access.access.value_2 row 0 : FKB),
                        (air.cols.op_c_access.access.value_3 row 0 : FKB) ] := by
        rw [← h_op_c]; rfl
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat + 8 ≤
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      extract_lets rd rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      by_cases h_rd0 : (air.cols.instruction.op_a row 0).val = 0
      · -- The destination is `x0`: the chip asks for any word and writes it nowhere.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 1 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        have h_rd_x0 : rd = regidx.Regidx 0#5 := by
          simp only [rd, h_rd0]
          rfl
        rw [OpcodeSpec.RV64.execute_LD_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := 0#8) (data1 := 0#8) (data2 := 0#8) (data3 := 0#8) (data4 := 0#8) (data5 := 0#8) (data6 := 0#8) (data7 := 0#8)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [h_rd_x0]
          rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
              deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
              deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LD,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
              operation_list_effect_state_writeReg_x0 (by simp [regidx_to_fin]; omega)]
          rw [h_next_pc]
        · rw [OpcodeSpec.RV64.spec_LD_hypotheses, h_rd_x0]
          simp only [beq_self_eq_true, if_true]
          obtain ⟨ h_read_a, h_mem_any ⟩ := h_rest
          -- The row's register write goes to `x0`, where `write_xreg` is the identity, so the
          -- bytes the load needs are mapped in `state` itself. Without this the match on the
          -- write's result stays stuck and the memberships stay about the state after it.
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                BitVec.ofNatLT_eq_ofNat, h_rd0] at h_mem_any
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add] using h_mem_any.2.2.2.2.2.2.2
      · -- The destination is a real register: the chip reads the word and writes it back.
        have h_a_is_x0 : air.cols.instruction.op_a_is_x0 row 0 = 0 := by
          rw [op_a_is_x0_eq air row h_is_real (bus_row_reads_asm_of_wf_asm h_wf)]
          simp [Fin.ext_iff, h_rd0]
        have h_bus := h_bus_hypotheses
        rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
            deserialise_raw_bus_row_Memory] at h_bus
        simp +decide [MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
              h_reg_rd, h_reg_rs1] at h_bus
        obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
        rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
        simp at h_rest
        obtain ⟨ h_read_a, h_mem ⟩ := h_rest
        -- The 32 bits the row loaded, in the form the memory message carries them.
        let v64 := U64w.toBV
                     #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                         (air.cols.op_a_access.access.value_1 row 0 : FKB),
                         (air.cols.op_a_access.access.value_2 row 0 : FKB),
                         (air.cols.op_a_access.access.value_3 row 0 : FKB) ]
        -- The memory chip's promise for a `LW` row: the word it writes back is the sign
        -- extension of those 32 bits, which is what the specification writes.
        have h_a_ext : U64w.toBV (op_a_value air row) = v64 := rfl
        have h_append_eq := eq_append_bytes_64 v64
        have h_rd_not_zero : ¬ (rd == regidx.Regidx 0#5) = true := by
          simp only [rd]
          simp [← BitVec.toNat_inj]
          clear * - h_rd0 h_reg_rd
          omega
        -- `write_xreg` matches on the destination index; the row's is not `x0`, so give
        -- the match a successor to reduce against.
        obtain ⟨ k, h_k ⟩ : ∃ k, (air.cols.instruction.op_a row 0).val % 32 = k + 1 := by
          clear * - h_rd0 h_reg_rd
          refine ⟨ (air.cols.instruction.op_a row 0).val % 32 - 1, ?_ ⟩
          omega
        rw [OpcodeSpec.RV64.execute_LD_equiv (r1 := rs1) (rd := rd) (imm := imm')
              (pc_val := U64w.toBV (pc air row))
              (r1_val := U64w.toBV (op_b_value air row))
              (data0 := BitVec.extractLsb' 0 8 v64)
              (data1 := BitVec.extractLsb' 8 8 v64)
              (data2 := BitVec.extractLsb' 16 8 v64)
              (data3 := BitVec.extractLsb' 24 8 v64)
              (data4 := BitVec.extractLsb' 32 8 v64)
              (data5 := BitVec.extractLsb' 40 8 v64)
              (data6 := BitVec.extractLsb' 48 8 v64)
              (data7 := BitVec.extractLsb' 56 8 v64)
              (state := state)
              (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
        · rw [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
                deserialise_raw_bus_row_Program, deserialise_raw_bus_row_State,
                deserialise_raw_bus_row_Memory]
          simp +decide [OpcodeSpec.RV64.spec_LD,
                MemoryBusEntry.deserialise, mem_width_of_opcode,
                h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store, h_a_is_x0,
                h_reg_rd, h_reg_rs1, rs1, BitVec.ofNatLT_eq_ofNat]
          rw [if_neg h_rd_not_zero]
          conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
          rw [operation_list_effect_state_writeReg_same
                (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b)]
          -- The goal carries the written value unfolded, so restate the chip's promise
          -- in that form before using it.
          simp [h_next_pc, op_b_value]
          simp [operation_list_effect, operation_effect, regidx_to_fin,
                write_xreg, Sail.writeReg, PreSail.writeReg, rd, h_k]
          rw [ExtDHashMap.insert_comm]
          all_goals (try rw [← h_append_eq])
          all_goals (clear * -; grind [reg_of_fin_neq_nextPC])
        · rw [OpcodeSpec.RV64.spec_LD_hypotheses]
          rw [if_neg (by simpa using h_rd_not_zero)]
          simp [operation_list_effect, operation_effect, write_xreg, regidx_to_fin,
                Sail.writeReg, PreSail.writeReg, BitVec.ofNatLT_eq_ofNat, h_k] at h_mem
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
          · rw [h_pc_read]
            congr 1
            simp [pc, ← BitVec.toNat_inj, U64w.toNat]
            omega
          · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.2.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.2.2.2.2.2.1
          · rw [h_addr_bridge]; simpa [BitVec.toNat_add, v64] using h_mem.2.2.2.2.2.2.2

  end LOADS

end Equivalence
