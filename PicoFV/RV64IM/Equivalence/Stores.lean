import PicoFV.RV64IM.Equivalence.Common

set_option maxHeartbeats 4_000_000

namespace Equivalence

  open Plonky3

  open RV64IM
  open RV64IM_Interactions.V3
  open CpuChip.ConstraintsAndBuses
  open CpuChip.Interpretations

  section STORES

    -- ========================================================================
    -- STORES — the four store opcodes: SB = 15, SH = 16, SW = 17, SD = 47.
    -- None is shared (`ProgramBusEntry.decoded_from`), so the decoder fixes
    -- both immediate flags and the row's class selectors, and no statement
    -- takes them, as none did at 2.x either.
    --
    -- A store row reads `rs2` into `op_a` and writes it back unchanged
    -- (`op_a_kept`), reads `rs1` into `op_b`, and carries the 12-bit offset in
    -- `op_c` (`imm_c = 1`). It sends one Memory message, whose promise
    -- (`memory_message_spec`, the contract of `RVSail/BusesV3.lean`) gives the
    -- address `op_b + op_c` its guest range and the width's alignment — the
    -- two conditions Sail needs to take the store rather than trap. The row
    -- sets no branch or jump selector, so its next pc is `pc + 4`
    -- (`is_sequential_active_constraints`).
    --
    -- The width is the only thing that differs: the chip writes the first
    -- limb of `op_a` for `SB` and `SH`, the first two for `SW` and all four
    -- for `SD`, and Sail writes the matching low bits of `rs2`'s value.
    -- ========================================================================

    /-- The low `n` bits of a `U64w`'s value, for `n` at most one limb, are those of its first
        limb. The chip writes a narrow store's data as that limb, and Sail writes the low bits
        of the register value. -/
    private lemma toBV_setWidth_8 (w : U64w) :
      (U64w.toBV w).setWidth 8 = (w[0]).setWidth 8
    := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, U64w.toBV_toNat, U64w.toNat]
      omega

    /-- The low limb itself, for a halfword store. -/
    private lemma toBV_setWidth_16 (w : U64w) :
      (U64w.toBV w).setWidth 16 = w[0]
    := by
      apply BitVec.eq_of_toNat_eq
      have h0 := (w[0]).isLt
      simp only [BitVec.toNat_setWidth, U64w.toBV_toNat, U64w.toNat]
      omega

    /-- A store row's flags and selectors, as its opcode fixes them (`selector_exclusivity`):
        `imm_b = 0` and `imm_c = 1` come from the decoder, and the class-selector vector is the
        opcode's row of `class_selectors_of_opcode`, which a caller with a literal opcode reads
        off by `simp`. -/
    private lemma store_row_selectors
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

    /-- A store row's offset: the Program message says the row's `op_c` columns encode a 12-bit
        immediate `imm'`, and `op_c` is then its 64-bit sign extension (constraints 4 to 7,
        through `imm_c_eq_1_constraints`). The four opcodes share one proof. -/
    private lemma store_offset
      [Field ExtF]
      (air : Valid_CpuChip FKB ExtF) (row : ℕ)
      (h_is_real : air.cols.is_real row 0 = 1)
      (h_wf : bus_row_wf_asm (bus_row air row))
      (h_constraints : CpuChip.Extraction.allHold air row)
      (h_opcode : air.cols.instruction.opcode row 0 = 15 ∨
                  air.cols.instruction.opcode row 0 = 16 ∨
                  air.cols.instruction.opcode row 0 = 17 ∨
                  air.cols.instruction.opcode row 0 = 47)
      (h_imm_c : air.cols.opcode_selector.imm_c row 0 = 1)
    :
      ∃ imm' : BitVec 12, U64w.toBV (op_c_value air row) = BitVec.signExtend 64 imm'
    := by
      have h_prog := program_bus_operand_properties air row h_is_real h_wf
      obtain ⟨ instr, pc_value, data, props, -, -, h_eq, h_eq_entry, - ⟩ := h_prog
      have h_decoded := ProgramBusEntry.operand_properties_inversion h_eq h_eq_entry
      rw [deserialise_program_bus_entry] at h_decoded
      rcases h_opcode with h_op | h_op | h_op | h_op <;>
      · simp [ProgramBusEntry.decoded_from, h_op] at h_decoded
        obtain ⟨ imm', rs2', rs1', h_eq_instr ⟩ := h_decoded
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

    /-- The byte a `SB` row stores: the low 8 bits of the register value are those of the
        first limb, which is what the chip's Memory message carries. -/
    private lemma extractLsb_toBV_8 (w : U64w) :
      BitVec.extractLsb 7 0 (U64w.toBV w) = (U64w.toBV w).setWidth 8
    := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.extractLsb, BitVec.extractLsb']

    /-- The halfword a `SH` row stores. -/
    private lemma extractLsb_toBV_16 (w : U64w) :
      BitVec.extractLsb 15 0 (U64w.toBV w) = (U64w.toBV w).setWidth 16
    := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.extractLsb, BitVec.extractLsb']

    /-- The word a `SW` row stores: the low 32 bits are the first two limbs, which the chip's
        Memory message carries as their append. -/
    private lemma extractLsb_toBV_32 (w : U64w) :
      BitVec.extractLsb 31 0 (U64w.toBV w) = w[1] ++ w[0]
    := by
      apply BitVec.eq_of_toNat_eq
      rw [show (w[1] ++ w[0] : BitVec 32) = U32w.toBV #v[w[0], w[1]] from rfl,
          ← U64w.setWidth_32_eq_low_U32w]
      have h0 := (w[0]).isLt
      have h1 := (w[1]).isLt
      simp [BitVec.extractLsb, BitVec.extractLsb', U32w.toNat, U64w.toNat]
      omega

    /-- Equivalence for SB (opcode 15, `instruction.STORE` of width 1). -/
    theorem equivalence_SB
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
      (h_opcode : air.cols.instruction.opcode row 0 = 15)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 1)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        store_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        store_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rs2, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
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
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      -- The row moves on by four, and writes back the value it read.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      -- The row's messages, as operations on the Sail state.
      have h_bus := h_bus_hypotheses
      simp +decide [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_bus_row, raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
            h_reg_rs2, h_reg_rs1] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      have h_read_a' : read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
          EStateM.Result.ok (U64w.toBV (op_a_value air row)) state := by
        rw [show U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) by
              simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1,
                    h_kept.2.2.2]]
        simpa [op_a_prev_value, BitVec.ofNatLT_eq_ofNat] using h_read_a
      extract_lets rs2 rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      rw [OpcodeSpec.RV64.execute_SB_equiv (r1 := rs1) (r2 := rs2) (imm := imm')
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_b_value air row))
            (r2_val := U64w.toBV (op_a_value air row))
            (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)]
      · simp +decide [OpcodeSpec.RV64.spec_SB, CPU_bus_operations,
              RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
              MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
              h_reg_rs2, h_reg_rs1, rs1, rs2, BitVec.ofNatLT_eq_ofNat]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        -- The store row writes `op_a` back unchanged, so its `WriteReg` drops out too. The
        -- read has to be restated with the value in its unfolded form, which is what the
        -- goal carries.
        have h_read_a'' : read_xreg (regidx_to_fin (regidx.Regidx
              (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
            EStateM.Result.ok (U64w.toBV
              #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                  (air.cols.op_a_access.access.value_1 row 0 : FKB),
                  (air.cols.op_a_access.access.value_2 row 0 : FKB),
                  (air.cols.op_a_access.access.value_3 row 0 : FKB) ]) state := h_read_a'
        rw [operation_list_effect_state_writeReg_same
              (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
            operation_list_effect_state_writeReg_same h_read_a'']
        -- Both sides now write the same word to the same address and the same next pc; the
        -- chip puts its pc write last, the specification puts it first.
        rw [h_next_pc]
        rw [show (((op_b_value air row).toNat + (BitVec.signExtend 64 imm').toNat) %
                  18446744073709551616)
                = (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat from by
              rw [BitVec.toNat_add]; simp]
        rw [h_addr_bridge]
        simp only [BitVec.toNat_add, U64w.toBV_toNat]
        rw [show (2 : ℕ) ^ 64 = 18446744073709551616 from by norm_num]
        simp [operation_list_effect, operation_effect, op_a_value, Sail.writeReg,
              PreSail.writeReg, extractLsb_toBV_8, toBV_setWidth_8]
      · rw [OpcodeSpec.RV64.spec_SB_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · rw [h_pc_read]
          congr 1
          simp [pc, ← BitVec.toNat_inj, U64w.toNat]
          omega
        · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
        · simpa [rs2] using h_read_a'

    /-- Equivalence for SH (opcode 16, `instruction.STORE` of width 2). -/
    theorem equivalence_SH
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
      (h_opcode : air.cols.instruction.opcode row 0 = 16)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 2)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        store_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        store_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rs2, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
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
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      have h_align : (2 : ℤ) ∣ (U64w.toBV (op_b_value air row) +
          BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]
        exact_mod_cast h_mem_spec.2.2.2.1 (by right; right; trivial)
      -- The row moves on by four, and writes back the value it read.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      -- The row's messages, as operations on the Sail state.
      have h_bus := h_bus_hypotheses
      simp +decide [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_bus_row, raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
            h_reg_rs2, h_reg_rs1] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      have h_read_a' : read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
          EStateM.Result.ok (U64w.toBV (op_a_value air row)) state := by
        rw [show U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) by
              simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1,
                    h_kept.2.2.2]]
        simpa [op_a_prev_value, BitVec.ofNatLT_eq_ofNat] using h_read_a
      extract_lets rs2 rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      rw [OpcodeSpec.RV64.execute_SH_equiv (r1 := rs1) (r2 := rs2) (imm := imm')
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_b_value air row))
            (r2_val := U64w.toBV (op_a_value air row))
            (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)
            (h_align := h_align)]
      · simp +decide [OpcodeSpec.RV64.spec_SH, CPU_bus_operations,
              RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
              MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
              h_reg_rs2, h_reg_rs1, rs1, rs2, BitVec.ofNatLT_eq_ofNat]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        -- The store row writes `op_a` back unchanged, so its `WriteReg` drops out too. The
        -- read has to be restated with the value in its unfolded form, which is what the
        -- goal carries.
        have h_read_a'' : read_xreg (regidx_to_fin (regidx.Regidx
              (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
            EStateM.Result.ok (U64w.toBV
              #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                  (air.cols.op_a_access.access.value_1 row 0 : FKB),
                  (air.cols.op_a_access.access.value_2 row 0 : FKB),
                  (air.cols.op_a_access.access.value_3 row 0 : FKB) ]) state := h_read_a'
        rw [operation_list_effect_state_writeReg_same
              (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
            operation_list_effect_state_writeReg_same h_read_a'']
        -- Both sides now write the same word to the same address and the same next pc; the
        -- chip puts its pc write last, the specification puts it first.
        rw [h_next_pc]
        rw [show (((op_b_value air row).toNat + (BitVec.signExtend 64 imm').toNat) %
                  18446744073709551616)
                = (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat from by
              rw [BitVec.toNat_add]; simp]
        rw [h_addr_bridge]
        simp only [BitVec.toNat_add, U64w.toBV_toNat]
        rw [show (2 : ℕ) ^ 64 = 18446744073709551616 from by norm_num]
        simp [operation_list_effect, operation_effect, op_a_value, Sail.writeReg,
              PreSail.writeReg, extractLsb_toBV_16, toBV_setWidth_16]
      · rw [OpcodeSpec.RV64.spec_SH_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · rw [h_pc_read]
          congr 1
          simp [pc, ← BitVec.toNat_inj, U64w.toNat]
          omega
        · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
        · simpa [rs2] using h_read_a'

    /-- Equivalence for SW (opcode 17, `instruction.STORE` of width 4). -/
    theorem equivalence_SW
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
      (h_opcode : air.cols.instruction.opcode row 0 = 17)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 4)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        store_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        store_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rs2, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
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
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      have h_align : (4 : ℤ) ∣ (U64w.toBV (op_b_value air row) +
          BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]
        exact_mod_cast h_mem_spec.2.2.2.2.1 (by right; left; trivial)
      -- The row moves on by four, and writes back the value it read.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      -- The row's messages, as operations on the Sail state.
      have h_bus := h_bus_hypotheses
      simp +decide [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_bus_row, raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
            h_reg_rs2, h_reg_rs1] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      have h_read_a' : read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
          EStateM.Result.ok (U64w.toBV (op_a_value air row)) state := by
        rw [show U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) by
              simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1,
                    h_kept.2.2.2]]
        simpa [op_a_prev_value, BitVec.ofNatLT_eq_ofNat] using h_read_a
      extract_lets rs2 rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      rw [OpcodeSpec.RV64.execute_SW_equiv (r1 := rs1) (r2 := rs2) (imm := imm')
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_b_value air row))
            (r2_val := U64w.toBV (op_a_value air row))
            (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)
            (h_align := h_align)]
      · simp +decide [OpcodeSpec.RV64.spec_SW, CPU_bus_operations,
              RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
              MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
              h_reg_rs2, h_reg_rs1, rs1, rs2, BitVec.ofNatLT_eq_ofNat]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        -- The store row writes `op_a` back unchanged, so its `WriteReg` drops out too. The
        -- read has to be restated with the value in its unfolded form, which is what the
        -- goal carries.
        have h_read_a'' : read_xreg (regidx_to_fin (regidx.Regidx
              (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
            EStateM.Result.ok (U64w.toBV
              #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                  (air.cols.op_a_access.access.value_1 row 0 : FKB),
                  (air.cols.op_a_access.access.value_2 row 0 : FKB),
                  (air.cols.op_a_access.access.value_3 row 0 : FKB) ]) state := h_read_a'
        rw [operation_list_effect_state_writeReg_same
              (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
            operation_list_effect_state_writeReg_same h_read_a'']
        -- Both sides now write the same word to the same address and the same next pc; the
        -- chip puts its pc write last, the specification puts it first.
        rw [h_next_pc]
        rw [show (((op_b_value air row).toNat + (BitVec.signExtend 64 imm').toNat) %
                  18446744073709551616)
                = (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat from by
              rw [BitVec.toNat_add]; simp]
        rw [h_addr_bridge]
        simp only [BitVec.toNat_add, U64w.toBV_toNat]
        rw [show (2 : ℕ) ^ 64 = 18446744073709551616 from by norm_num]
        simp [operation_list_effect, operation_effect, op_a_value, Sail.writeReg,
              PreSail.writeReg, extractLsb_toBV_32]
      · rw [OpcodeSpec.RV64.spec_SW_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · rw [h_pc_read]
          congr 1
          simp [pc, ← BitVec.toNat_inj, U64w.toNat]
          omega
        · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
        · simpa [rs2] using h_read_a'

    /-- Equivalence for SD (opcode 47, `instruction.STORE` of width 8). -/
    theorem equivalence_SD
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
      (h_opcode : air.cols.instruction.opcode row 0 = 47)
      (h_bus_hypotheses :
        (operation_list_effect (CPU_bus_operations air row) state).hypotheses)
      (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    :
      let rs2 : regidx := .Regidx (air.cols.instruction.op_a row 0).val
      let rs1 : regidx := .Regidx (air.cols.instruction.op_b_0 row 0).val
      let imm : BitVec 12 := (U64w.toBV (op_c_value air row)).setWidth 12
      execute_instruction (instruction.STORE (imm, rs2, rs1, 8)) state =
        (operation_list_effect (CPU_bus_operations air row) state).state
    := by
      have h_wf := h_all_wf row h_row
      have h_constraints := h_all_constraints row h_row
      have h_pc_facts := pc_facts air row h_is_real h_wf
      obtain ⟨ h_imm_b, h_imm_c, h_s ⟩ :=
        store_row_selectors air row h_is_real h_wf h_opcode (by rfl) (by rfl)
      simp [class_selectors_of_opcode] at h_s
      obtain ⟨ h_ecall, h_memory, h_store, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
               h_jalr, h_jal ⟩ := h_s
      obtain ⟨ imm', h_op_c ⟩ :=
        store_offset air row h_is_real h_wf h_constraints (by simp [h_opcode]) h_imm_c
      obtain ⟨ h_reg_rs2, h_reg_rs1, - ⟩ := register_indices_lt air row h_is_real h_wf
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
      have h_range : (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat <
          Pico_address_space_size_64 := by
        rw [h_addr_bridge]
        have h_space : Pico_address_space_size_64 = 2 ^ 48 := rfl
        have := h_mem_spec.2.2.1
        omega
      have h_align : (8 : ℤ) ∣ (U64w.toBV (op_b_value air row) +
          BitVec.signExtend 64 imm').toNat := by
        rw [h_addr_bridge]
        exact_mod_cast h_mem_spec.2.2.2.2.2.1 (by right; trivial)
      -- The row moves on by four, and writes back the value it read.
      have h_halt : air.cols.is_halt row 0 = 0 :=
        is_halt_eq_zero_of_no_ecall air row h_ecall h_constraints
      have h_next_pc := is_sequential_active_constraints air row h_row h_is_real h_all_wf
        h_all_constraints pico_assumptions
        ⟨ h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu ⟩ h_jal h_jalr h_halt
      have h_kept := op_a_kept air row h_constraints
        (by rw [h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_store]; norm_num)
      -- The row's messages, as operations on the Sail state.
      have h_bus := h_bus_hypotheses
      simp +decide [CPU_bus_operations, RV64IM_Interactions.V3.bus_operations,
            deserialise_bus_row, raw_bus_row, MemoryBusEntry.deserialise, mem_width_of_opcode,
            h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
            h_reg_rs2, h_reg_rs1] at h_bus
      obtain ⟨ h_pc_read, h_read_b, h_rest ⟩ := h_bus
      rw [operation_list_effect_hypotheses_writeReg_same (by simpa using h_read_b)] at h_rest
      simp at h_rest
      obtain ⟨ h_read_a, - ⟩ := h_rest
      have h_read_a' : read_xreg (regidx_to_fin (regidx.Regidx
            (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
          EStateM.Result.ok (U64w.toBV (op_a_value air row)) state := by
        rw [show U64w.toBV (op_a_value air row) = U64w.toBV (op_a_prev_value air row) by
              simp [op_a_value, op_a_prev_value, h_kept.1, h_kept.2.1, h_kept.2.2.1,
                    h_kept.2.2.2]]
        simpa [op_a_prev_value, BitVec.ofNatLT_eq_ofNat] using h_read_a
      extract_lets rs2 rs1 imm
      rw [show imm = imm' by
            simp only [imm, h_op_c]; exact setWidth_signExtend_self imm' (by norm_num)]
      rw [OpcodeSpec.RV64.execute_SD_equiv (r1 := rs1) (r2 := rs2) (imm := imm')
            (pc_val := U64w.toBV (pc air row))
            (r1_val := U64w.toBV (op_b_value air row))
            (r2_val := U64w.toBV (op_a_value air row))
            (risc_v_assumptions := risc_v_assumptions) (h_range := h_range)
            (h_align := h_align)]
      · simp +decide [OpcodeSpec.RV64.spec_SD, CPU_bus_operations,
              RV64IM_Interactions.V3.bus_operations, deserialise_bus_row, raw_bus_row,
              MemoryBusEntry.deserialise, mem_width_of_opcode,
              h_is_real, h_opcode, h_imm_b, h_imm_c, h_memory, h_store,
              h_reg_rs2, h_reg_rs1, rs1, rs2, BitVec.ofNatLT_eq_ofNat]
        conv => rhs; rw [operation_list_effect_state_filter]; unfold state_filter; simp
        -- The store row writes `op_a` back unchanged, so its `WriteReg` drops out too. The
        -- read has to be restated with the value in its unfolded form, which is what the
        -- goal carries.
        have h_read_a'' : read_xreg (regidx_to_fin (regidx.Regidx
              (BitVec.ofNat 5 (air.cols.instruction.op_a row 0).val))) state =
            EStateM.Result.ok (U64w.toBV
              #v[ (air.cols.op_a_access.access.value_0 row 0 : FKB),
                  (air.cols.op_a_access.access.value_1 row 0 : FKB),
                  (air.cols.op_a_access.access.value_2 row 0 : FKB),
                  (air.cols.op_a_access.access.value_3 row 0 : FKB) ]) state := h_read_a'
        rw [operation_list_effect_state_writeReg_same
              (by simpa [op_b_value, BitVec.ofNatLT_eq_ofNat] using h_read_b),
            operation_list_effect_state_writeReg_same h_read_a'']
        -- Both sides now write the same word to the same address and the same next pc; the
        -- chip puts its pc write last, the specification puts it first.
        rw [h_next_pc]
        rw [show (((op_b_value air row).toNat + (BitVec.signExtend 64 imm').toNat) %
                  18446744073709551616)
                = (U64w.toBV (op_b_value air row) + BitVec.signExtend 64 imm').toNat from by
              rw [BitVec.toNat_add]; simp]
        rw [h_addr_bridge]
        simp only [BitVec.toNat_add, U64w.toBV_toNat]
        rw [show (2 : ℕ) ^ 64 = 18446744073709551616 from by norm_num]
        simp [operation_list_effect, operation_effect, op_a_value, Sail.writeReg,
              PreSail.writeReg]
      · rw [OpcodeSpec.RV64.spec_SD_hypotheses]
        refine ⟨ ?_, ?_, ?_ ⟩
        · rw [h_pc_read]
          congr 1
          simp [pc, ← BitVec.toNat_inj, U64w.toNat]
          omega
        · simpa [op_b_value, rs1, BitVec.ofNatLT_eq_ofNat] using h_read_b
        · simpa [rs2] using h_read_a'

  end STORES

end Equivalence
