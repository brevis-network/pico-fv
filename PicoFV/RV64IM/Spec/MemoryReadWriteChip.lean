import PicoFV.RV64IM.Constraints.MemoryReadWriteChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MemoryReadWriteChip — semantic specification (RV64)

Per-opcode specs deriving `MemoryBus.Spec OPCODE a b c` (with `a`, `b`,
`c` 64-bit, laid out as four u16 limbs each) from the chip's bus
assumptions, constraints, and the active-selector witness:

| Selector active | Opcode | Semantics                                                       |
|-----------------|--------|-----------------------------------------------------------------|
| `is_lb = 1`     | 10     | Load byte, sign-extended to 64 bits                              |
| `is_lh = 1`     | 11     | Load halfword (u16), sign-extended                               |
| `is_lw = 1`     | 12     | Load word (u32), sign-extended                                   |
| `is_lbu = 1`    | 13     | Load byte, zero-extended                                         |
| `is_lhu = 1`    | 14     | Load halfword, zero-extended                                     |
| `is_lwu = 1`    | 45     | Load word, zero-extended (RV64-only)                             |
| `is_ld = 1`     | 46     | Load doubleword (no extension; RV64-only)                        |
| `is_sb = 1`     | 15     | Store byte                                                       |
| `is_sh = 1`     | 16     | Store halfword                                                   |
| `is_sw = 1`     | 17     | Store word                                                       |
| `is_sd = 1`     | 47     | Store doubleword (RV64-only)                                     |

The proofs follow the RV32 `MemoryReadWriteAir.Spec` template, adapted
for:
  * 11 selectors (vs RV32's 8);
  * u16-limb word view via `U64w.toBV` (vs RV32's u8-byte `U32b.toBV`);
  * 3 offset bits + 4-way `limb_select` one-hot (vs RV32's 2 offset bits).
-/

namespace MemoryReadWriteChip.Spec

  open RV64IM_Interactions
  open MemoryReadWriteChip.ConstraintsAndBuses
  open MemoryReadWriteChip.Interactions
  open MemoryReadWriteChip.Interpretations

  set_option maxHeartbeats 1_000_000_000

  -- ====================================
  -- LB (Load Byte, signed) — opcode 10
  -- ====================================

  lemma spec_LB
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 10)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- When `op_a_0 = 1` (rd = x0), Pico's chip leaves
    -- `op_a_access.access.value_0..3` unconstrained: c46/c47 (the
    -- `mem_value_is_neg/pos_not_x0` gate columns) collapse to 0 via
    -- the `(1 - op_a_0)` factor, so c48-c63 all fire vacuously. But
    -- the Memory bus carries those very columns as the loaded `a_0..3`
    -- value — they must hold the correct sign-extended byte, not just
    -- *something* u16-bounded. The cleanest Pico-side fix is to drop
    -- the `(1 - op_a_0)` factor from c46/c47, making c48-c63 fire
    -- unconditionally. The equations they would then enforce for LB
    -- are stated below: `value_0 = selected_byte + msb · 0xFF00`,
    -- `value_{1,2,3} = msb · 0xFFFF` (i.e., the 64-bit sign-extension
    -- of the loaded byte). See `mrw_op_a_x0_soundness_gap.md`.
    (MISSING_LB_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_byte row 0 +
            air.cols.values.msb row 0 * 65280 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 =
          air.cols.values.msb row 0 * 65535)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    -- ───────────────────────────────────────────────────────────────────
    -- Step 1: get the per-opcode selector pattern from selector_exclusivity.
    -- With `h_opcode = 10` this forces `is_lb = 1` and the other ten = 0.
    -- ───────────────────────────────────────────────────────────────────
    have h_excl := selector_exclusivity air row h_ext h_is_real
    simp only at h_excl
    obtain ⟨ _h_opcode_range, ub_b0, ub_b1, ub_b2, ub_b3,
             ub_c0, ub_c1, ub_c2, ub_c3,
             h_op_10, h_op_11, h_op_12, h_op_13, h_op_14,
             h_op_15, h_op_16, h_op_17, h_op_45, h_op_46, h_op_47 ⟩ := h_excl
    obtain ⟨ h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
             h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd ⟩ :=
      h_op_10 h_opcode
    clear h_op_11 h_op_12 h_op_13 h_op_14
          h_op_15 h_op_16 h_op_17 h_op_45 h_op_46 h_op_47 h_op_10
    -- ───────────────────────────────────────────────────────────────────
    -- Step 2: simp the goal with `MemoryBus.Spec` + `h_opcode`. Four
    -- obligations remain:
    --   (a) `a_0..3 < 65536` — load output u16-limbed;
    --   (b) `65536 ≤ addr` — stack guard (`addr ∉ [0, 2^16)`);
    --   (c) `addr < 2^48` — fits in Pico's 48-bit address space;
    --   (d) `a = signExtend 64 (a.truncate 8)` — LB sign-extension.
    -- ───────────────────────────────────────────────────────────────────
    simp [MemoryBus.Spec, h_opcode]
    -- ───────────────────────────────────────────────────────────────────
    -- Step 3: peel `h_ext` to expose the ALU-bus assumption
    -- `addr_word = op_b + op_c` and the byte-bus u16 / u8 ranges on
    -- `addr_word_0..2` and the memory-access metadata.
    -- ───────────────────────────────────────────────────────────────────
    simp [bus_row_ext_asm, bus_row, AbsBuses,
          h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw, h_is_lwu, h_is_ld,
          h_is_sb, h_is_sh, h_is_sw, h_is_sd, h_is_real] at h_ext
    obtain ⟨ _opcode_range, _ub_b0, _ub_b1, _ub_b2, _ub_b3,
             _ub_c0, _ub_c1, _ub_c2, _ub_c3,
             _neg_op_11, _neg_op_12, _neg_op_13, _neg_op_14,
             _neg_op_45, _neg_op_46,
             _neg_op_15, _neg_op_16, _neg_op_17, _neg_op_47 ⟩ := h_ext
    -- ───────────────────────────────────────────────────────────────────
    -- Step 4: peel `h_wf` to expose the consumer-side ALU-bus assumption
    -- (`addr_word = op_b + op_c` from the ADD lookup), the byte-bus u16
    -- range on `addr_word_0..2`, the byte-bus MSB lookup on
    -- `selected_byte`, and the state-bus u16 ranges on `memory_access`.
    -- ───────────────────────────────────────────────────────────────────
    simp [bus_row_wf_asm, bus_row, AbsBuses,
          h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw, h_is_lwu, h_is_ld,
          h_is_sb, h_is_sh, h_is_sw, h_is_sd, h_is_real] at h_wf
    obtain ⟨ h_alu_addr, _h_byte_aw0, _h_byte_aw1, _h_byte_aw2,
             _h_bit13, _h_byte_d16, _h_byte_d8,
             _h_byte_sl_low, h_msb_byte,
             ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := h_wf
    -- Unfold the ALU bus → `addr_word = op_b + op_c` (over BitVec 64,
    -- via `execute_RTYPE_pure .ADD`) plus the u16 ranges on
    -- `addr_word_0..3`.
    simp [ALUBus.Spec] at h_alu_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, h_alu_eq ⟩ := h_alu_addr
    simp [RV64IM.execute_RTYPE_pure] at h_alu_eq
    -- ───────────────────────────────────────────────────────────────────
    -- Step 5: project out the relevant constraints from `h_constraints`.
    --   * c0  → `is_mem · addr_word_3 = 0` (top limb of address forced 0)
    --   * c1  → stack guard `addr_top_two_limb_inv · (aw_1 + aw_2) = is_mem`
    --   * c22 → `(is_lb + is_lbu) · (unsigned_mem_val_0 - selected_byte) = 0`
    --   * c23–25 → `(is_lb + is_lbu) · unsigned_mem_val_{1,2,3} = 0`
    --   * c45 → `op_a_0 ∈ {0, 1}`
    --   * c46 → `mem_value_is_neg_not_x0 = (is_lb + is_lh + is_lw) · msb · (1 - op_a_0)`
    --   * c47 → `mem_value_is_pos_not_x0 = (1 - …) · (1 - op_a_0)`
    --   * c48–51 → LB sign-extension fills: `op_a.value_i = unsigned_mem_val_i + msb · 0xFF00 / 0xFFFF`
    --     (gated by `mem_value_is_neg_not_x0 · is_lb`)
    --   * c60–63 → positive case: `op_a.value_i = unsigned_mem_val_i`
    --     (gated by `mem_value_is_pos_not_x0`)
    -- ───────────────────────────────────────────────────────────────────
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall]
      at h_constraints
    have h_c0  : constraint_0  air row := by clear *- h_constraints; aesop
    have h_c1  : constraint_1  air row := by clear *- h_constraints; aesop
    have h_c22 : constraint_22 air row := by clear *- h_constraints; aesop
    have h_c23 : constraint_23 air row := by clear *- h_constraints; aesop
    have h_c24 : constraint_24 air row := by clear *- h_constraints; aesop
    have h_c25 : constraint_25 air row := by clear *- h_constraints; aesop
    -- Constraints driving `op_a_access.access.value_i` in the LB case.
    have h_c45 : constraint_45 air row := by clear *- h_constraints; aesop
    have h_c46 : constraint_46 air row := by clear *- h_constraints; aesop
    have h_c47 : constraint_47 air row := by clear *- h_constraints; aesop
    have h_c48 : constraint_48 air row := by clear *- h_constraints; aesop
    have h_c49 : constraint_49 air row := by clear *- h_constraints; aesop
    have h_c50 : constraint_50 air row := by clear *- h_constraints; aesop
    have h_c51 : constraint_51 air row := by clear *- h_constraints; aesop
    have h_c60 : constraint_60 air row := by clear *- h_constraints; aesop
    have h_c61 : constraint_61 air row := by clear *- h_constraints; aesop
    have h_c62 : constraint_62 air row := by clear *- h_constraints; aesop
    have h_c63 : constraint_63 air row := by clear *- h_constraints; aesop
    clear h_constraints
    -- Specialise selector-gated constraints to the LB-active branch.
    simp [constraint_0, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd] at h_c0
    simp [constraint_1, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd, sub_eq_zero] at h_c1
    simp [constraint_22, h_is_lb, h_is_lbu, sub_eq_zero] at h_c22
    simp [constraint_23, h_is_lb, h_is_lbu] at h_c23
    simp [constraint_24, h_is_lb, h_is_lbu] at h_c24
    simp [constraint_25, h_is_lb, h_is_lbu] at h_c25
    -- ───────────────────────────────────────────────────────────────────
    -- Step 6: specialise c45-c63 (op_a_0 booleanness + neg/pos gates +
    -- value_i fills) and `h_msb_byte` (msb ∈ {0, 1} + `selected_byte`
    -- byte-bound). With these in hand we derive the *unified* value_i
    -- extension equations, valid both for `op_a_0 = 0` (from c46-c63)
    -- and for `op_a_0 = 1` (from `MISSING_LB_extends_correctly`).
    -- ───────────────────────────────────────────────────────────────────
    simp [constraint_45, sub_eq_zero, mul_eq_zero] at h_c45
    simp [constraint_46, h_is_lb, h_is_lh, h_is_lw, sub_eq_zero] at h_c46
    simp [constraint_47, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, sub_eq_zero] at h_c47
    simp [constraint_48, h_is_lb, sub_eq_zero] at h_c48
    simp [constraint_49, h_is_lb, sub_eq_zero] at h_c49
    simp [constraint_50, h_is_lb, sub_eq_zero] at h_c50
    simp [constraint_51, h_is_lb, sub_eq_zero] at h_c51
    simp [constraint_60, sub_eq_zero] at h_c60
    simp [constraint_61, sub_eq_zero] at h_c61
    simp [constraint_62, sub_eq_zero] at h_c62
    simp [constraint_63, sub_eq_zero] at h_c63
    simp [ByteBus.Spec] at h_msb_byte
    obtain ⟨ h_msb_def, h_msb_lt, h_byte_lt ⟩ := h_msb_byte
    have h_msb_bool : air.cols.values.msb row 0 = 0 ∨
                      air.cols.values.msb row 0 = 1 := by
      rw [h_msb_def]; split_ifs <;> [left; right] <;> rfl
    -- Unified value_i sign-extension equations. The `op_a_0 = 0`
    -- branch derives them from c48..c63 (gates fire normally). The
    -- `op_a_0 = 1` branch uses `MISSING_LB_extends_correctly` — the
    -- assumed Pico-side fix that drops the `(1 - op_a_0)` factor from
    -- the gate columns, so c48..c63 fire unconditionally.
    have h_val_eq :
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_byte row 0 +
            air.cols.values.msb row 0 * 65280 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 =
          air.cols.values.msb row 0 * 65535 := by
      rcases h_c45 with h_x0 | h_x0
      . -- op_a_0 = 0: derive from c46/c47 + c48..c63.
        simp [h_x0] at h_c46 h_c47
        rcases h_msb_bool with h_msb | h_msb
        . -- msb = 0: pos = 1 fires c60..c63; value_0 = byte,
          -- value_{1,2,3} = 0.
          rw [h_msb] at h_c46 h_c47
          simp at h_c46 h_c47
          rcases h_c60 with h | h_v0; . rw [h] at h_c47; simp at h_c47
          rcases h_c61 with h | h_v1; . rw [h] at h_c47; simp at h_c47
          rcases h_c62 with h | h_v2; . rw [h] at h_c47; simp at h_c47
          rcases h_c63 with h | h_v3; . rw [h] at h_c47; simp at h_c47
          grind
        . -- msb = 1: neg = 1 fires c48..c51; value_0 = byte + 65280,
          -- value_{1,2,3} = 65535.
          rw [h_msb] at h_c46 h_c47
          simp at h_c46 h_c47
          rcases h_c48 with h | h_v0; . rw [h] at h_c46; simp at h_c46
          rcases h_c49 with h | h_v1; . rw [h] at h_c46; simp at h_c46
          rcases h_c50 with h | h_v2; . rw [h] at h_c46; simp at h_c46
          rcases h_c51 with h | h_v3; . rw [h] at h_c46; simp at h_c46
          grind
      . -- op_a_0 = 1: from the soundness-bug hypothesis.
        exact MISSING_LB_extends_correctly h_x0
    obtain ⟨ h_v0, h_v1, h_v2, h_v3 ⟩ := h_val_eq
    -- ───────────────────────────────────────────────────────────────────
    -- Step 7: discharge the four `MemoryBus.Spec` conjuncts.
    -- ───────────────────────────────────────────────────────────────────
    refine ⟨?_, ?_, ?_, ?_⟩
    . -- (a) u16 range on `op_a_access.access.value_0..3`.
      -- Case-split on `msb`:
      --   * msb = 0 → value_0 = byte (< 256), value_{1,2,3} = 0;
      --   * msb = 1 → value_0 = byte + 65280 (< 65536), value_{1,2,3} = 65535.
      grind
    . -- (b) 65536 ≤ addr.
      -- From `h_c1`: `addr_top_two_limb_inv · (aw_1 + aw_2) = 1` forces
      -- `aw_1 + aw_2 ≠ 0` in FKB. With u16 bounds on `aw_1`, `aw_2`
      -- (max sum 131070 < KB_prime), the field sum and the natural sum
      -- agree, so `aw_1.val + aw_2.val ≠ 0`. Combined with `h_alu_eq`
      -- and `h_c0`, `addr ≥ 2^16`.
      have h_alu_nat := h_alu_eq
      apply_fun BitVec.toNat at h_alu_nat
      simp at h_alu_nat
      rw [← h_alu_nat]
      have h_sum_ne :
          air.cols.values.addr_word_1 row 0 +
          air.cols.values.addr_word_2 row 0 ≠ 0 := by
        intro h_zero; rw [h_zero] at h_c1; simp at h_c1
      have h_sum_nat_ne :
          (air.cols.values.addr_word_1 row 0).val +
          (air.cols.values.addr_word_2 row 0).val ≠ 0 := by
        intro h_zero
        apply h_sum_ne
        simp [Fin.ext_iff, Fin.add_def]; omega
      simp [U64w.toNat, h_c0]
      omega
    . -- (c) addr < 2^48.
      apply_fun BitVec.toNat at h_alu_eq
      simp at h_alu_eq
      rw [← h_alu_eq]
      simp [U64w.toNat, h_c0]
      omega
    . -- (d) LB sign-extension: `a = signExtend 64 (a.truncate 8)`.
      -- Rewrite `value_i` via `h_v0..3`, then case-split on `msb`:
      --   * msb = 0 → value_0 = byte (< 128 from `h_msb_def`), so
      --     `(setWidth 8 ...).msb = false` and signExtend = zeroExtend;
      --   * msb = 1 → value_0 = byte + 65280 (byte ≥ 128), so
      --     `(setWidth 8 ...).msb = true` and signExtend fills 1s.
      rw [h_v0, h_v1, h_v2, h_v3]
      rcases h_msb_bool with h_msb | h_msb
      . rw [h_msb]
        simp only [zero_mul, add_zero]
        have h_byte_lt_128 : (air.cols.values.selected_byte row 0).val < 128 := by
          by_contra h_ge
          rw [h_msb_def, if_neg (by simp [Fin.lt_def]; omega)] at h_msb
          exact absurd h_msb (by decide)
        have h_byte_val_lt : (air.cols.values.selected_byte row 0).val < 65536 := by
          omega
        apply BitVec.eq_of_toNat_eq
        have h_bv : (U64w.toBV
            #v[BitVec.ofNat 16 (air.cols.values.selected_byte row 0).val,
               BitVec.ofNat 16 (0 : FKB).val,
               BitVec.ofNat 16 (0 : FKB).val,
               BitVec.ofNat 16 (0 : FKB).val]).toNat =
            (air.cols.values.selected_byte row 0).val := by
          rw [U64w.toBV_toNat]
          simp [U64w.toNat, Nat.mod_eq_of_lt h_byte_val_lt]
        rw [h_bv]
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
        have h_msb_false :
            (BitVec.setWidth 8
                (U64w.toBV
                  #v[BitVec.ofNat 16 (air.cols.values.selected_byte row 0).val,
                     BitVec.ofNat 16 (0 : FKB).val,
                     BitVec.ofNat 16 (0 : FKB).val,
                     BitVec.ofNat 16 (0 : FKB).val])).msb = false := by
          rw [BitVec.msb_eq_decide]
          simp [BitVec.toNat_setWidth, U64w.toNat]
          omega
        rw [h_msb_false]
        simp [U64w.toNat]
        omega
      . rw [h_msb]
        simp only [one_mul]
        have h_byte_ge_128 : 128 ≤ (air.cols.values.selected_byte row 0).val := by
          by_contra h_lt
          rw [h_msb_def, if_pos (by simp [Fin.lt_def]; omega)] at h_msb
          exact absurd h_msb (by decide)
        have h_byte_val_lt : (air.cols.values.selected_byte row 0).val < 65536 := by
          omega
        apply BitVec.eq_of_toNat_eq
        have h_v0_val :
            (air.cols.values.selected_byte row 0 + 65280 : FKB).val =
            (air.cols.values.selected_byte row 0).val + 65280 := by
          rw [Fin.val_add]
          simp
          omega
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
        have h_msb_true :
            (BitVec.setWidth 8
                (U64w.toBV
                  #v[BitVec.ofNat 16 (air.cols.values.selected_byte row 0 + 65280 : FKB).val,
                     BitVec.ofNat 16 (65535 : FKB).val,
                     BitVec.ofNat 16 (65535 : FKB).val,
                     BitVec.ofNat 16 (65535 : FKB).val])).msb = true := by
          simp [BitVec.msb_eq_decide, U64w.toNat]
          omega
        rw [h_msb_true]
        simp [U64w.toNat, -BitVec.reduceToNat, -BitVec.toNat_ofNat]
        repeat rw [BitVec.toNat_ofNat]
        omega

  -- =====================================
  -- LBU (Load Byte, unsigned) — opcode 13
  -- =====================================

  lemma spec_LBU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 13)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- See `spec_LB` for the full rationale. For LBU the correct
    -- extension is the zero-extension of `selected_byte`:
    --   `value_0 = selected_byte`, `value_{1,2,3} = 0`.
    (MISSING_LBU_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_byte row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 = 0)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-lbu-high-byte-gap`.
    -- The chip emits a byte-bus check on `selected_limb_low_byte` for
    -- the LB+LBU pair, but NOT on the high byte
    --   `(selected_limb - selected_limb_low_byte) · inv(256)`
    -- when `offset_bit_0 = 1`. For LB the missing bound is supplied by
    -- byte bus 6 (the MSB lookup, gated by `-is_lb`); LBU has no such
    -- backup, so a malicious prover can place an arbitrary FKB element
    -- in `selected_byte`. Fix: emit a byte-bus check on `selected_byte`
    -- (or include the high byte in entry 11). The bound below is what
    -- such a check would produce. See `mrw_lbu_high_byte_gap.md`.
    (MISSING_LBU_selected_byte_in_range :
      (air.cols.values.selected_byte row 0).val < 256)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    have h_excl := selector_exclusivity air row h_ext h_is_real
    simp only at h_excl
    obtain ⟨ _h_opcode_range, ub_b0, ub_b1, ub_b2, ub_b3,
             ub_c0, ub_c1, ub_c2, ub_c3,
             h_op_10, h_op_11, h_op_12, h_op_13, h_op_14,
             h_op_15, h_op_16, h_op_17, h_op_45, h_op_46, h_op_47 ⟩ := h_excl
    obtain ⟨ h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
             h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd ⟩ :=
      h_op_13 h_opcode
    clear h_op_10 h_op_11 h_op_12 h_op_14
          h_op_15 h_op_16 h_op_17 h_op_45 h_op_46 h_op_47 h_op_13
    simp [MemoryBus.Spec, h_opcode]
    simp [bus_row_ext_asm, bus_row, AbsBuses,
          h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw, h_is_lwu, h_is_ld,
          h_is_sb, h_is_sh, h_is_sw, h_is_sd, h_is_real] at h_ext
    obtain ⟨ _opcode_range, _ub_b0, _ub_b1, _ub_b2, _ub_b3,
             _ub_c0, _ub_c1, _ub_c2, _ub_c3,
             _neg_op_10, _neg_op_11, _neg_op_12, _neg_op_14,
             _neg_op_45, _neg_op_46,
             _neg_op_15, _neg_op_16, _neg_op_17, _neg_op_47 ⟩ := h_ext
    simp [bus_row_wf_asm, bus_row, AbsBuses,
          h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw, h_is_lwu, h_is_ld,
          h_is_sb, h_is_sh, h_is_sw, h_is_sd, h_is_real] at h_wf
    -- For LBU, the byte-bus MSB lookup on `selected_byte` (gated by
    -- `-is_lb`) is vacuous, so `h_wf` has 11 conjuncts (vs 12 for LB).
    obtain ⟨ h_alu_addr, _h_byte_aw0, _h_byte_aw1, _h_byte_aw2,
             _h_bit13, _h_byte_d16, _h_byte_d8,
             h_byte_sl_low,
             ub_mpv0, ub_mpv1, ub_mpv2, ub_mpv3 ⟩ := h_wf
    simp [ALUBus.Spec] at h_alu_addr
    obtain ⟨ ⟨ ub_aw0, ub_aw1, ub_aw2, ub_aw3 ⟩, h_alu_eq ⟩ := h_alu_addr
    simp [RV64IM.execute_RTYPE_pure] at h_alu_eq
    -- Get `selected_limb_low_byte < 256` from `h_byte_sl_low` (ByteBus.Spec 7).
    -- After simp, the trivial `0 = 0` and `0 < 256` conjuncts drop, leaving
    -- just `h_byte_sl_low : selected_limb_low_byte.val < 256`.
    simp [ByteBus.Spec] at h_byte_sl_low
    -- Extract relevant constraints.
    rw [allHold_iff_allHold_simplified] at h_constraints
    simp only [allHold_simplified, row_constraint_list, List.Forall]
      at h_constraints
    have h_c0  : constraint_0  air row := by clear *- h_constraints; aesop
    have h_c1  : constraint_1  air row := by clear *- h_constraints; aesop
    have h_c2  : constraint_2  air row := by clear *- h_constraints; aesop
    have h_c21 : constraint_21 air row := by clear *- h_constraints; aesop
    have h_c22 : constraint_22 air row := by clear *- h_constraints; aesop
    have h_c23 : constraint_23 air row := by clear *- h_constraints; aesop
    have h_c24 : constraint_24 air row := by clear *- h_constraints; aesop
    have h_c25 : constraint_25 air row := by clear *- h_constraints; aesop
    have h_c45 : constraint_45 air row := by clear *- h_constraints; aesop
    have h_c46 : constraint_46 air row := by clear *- h_constraints; aesop
    have h_c47 : constraint_47 air row := by clear *- h_constraints; aesop
    have h_c60 : constraint_60 air row := by clear *- h_constraints; aesop
    have h_c61 : constraint_61 air row := by clear *- h_constraints; aesop
    have h_c62 : constraint_62 air row := by clear *- h_constraints; aesop
    have h_c63 : constraint_63 air row := by clear *- h_constraints; aesop
    clear h_constraints
    simp [constraint_0, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd] at h_c0
    simp [constraint_1, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd,
          sub_eq_zero] at h_c1
    -- c2: `is_mem · offset_bit_0 · (offset_bit_0 - 1) = 0` → `offset_bit_0 ∈ {0, 1}`.
    simp [constraint_2, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, h_is_sb, h_is_sh, h_is_sw, h_is_sd,
          sub_eq_zero, mul_eq_zero] at h_c2
    simp [constraint_21, h_is_lb, h_is_lbu, sub_eq_zero] at h_c21
    simp [constraint_22, h_is_lb, h_is_lbu, sub_eq_zero] at h_c22
    simp [constraint_23, h_is_lb, h_is_lbu] at h_c23
    simp [constraint_24, h_is_lb, h_is_lbu] at h_c24
    simp [constraint_25, h_is_lb, h_is_lbu] at h_c25
    -- Specialise c45–c47 (op_a_0 bool + neg/pos gate defs) for LBU.
    simp [constraint_45, sub_eq_zero, mul_eq_zero] at h_c45
    simp [constraint_46, h_is_lb, h_is_lh, h_is_lw] at h_c46
    simp [constraint_47, h_is_lb, h_is_lbu, h_is_lh, h_is_lhu, h_is_lw,
          h_is_lwu, h_is_ld, sub_eq_zero] at h_c47
    simp [constraint_60, sub_eq_zero] at h_c60
    simp [constraint_61, sub_eq_zero] at h_c61
    simp [constraint_62, sub_eq_zero] at h_c62
    simp [constraint_63, sub_eq_zero] at h_c63
    -- Unified value_i zero-extension equations. The `op_a_0 = 0`
    -- branch closes via c47 + c60..c63 + c22..c25; the `op_a_0 = 1`
    -- branch uses `MISSING_LBU_extends_correctly` (the assumed Pico-
    -- side fix: drop the `(1 - op_a_0)` factor from the gate columns,
    -- so c60..c63 fire unconditionally for LBU).
    have h_val_eq :
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_byte row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 = 0 := by
      rcases h_c45 with h_x0 | h_x0
      . rw [h_x0] at h_c47
        simp at h_c47
        rcases h_c60 with h | h_v0; . rw [h] at h_c47; simp at h_c47
        rcases h_c61 with h | h_v1; . rw [h] at h_c47; simp at h_c47
        rcases h_c62 with h | h_v2; . rw [h] at h_c47; simp at h_c47
        rcases h_c63 with h | h_v3; . rw [h] at h_c47; simp at h_c47
        rw [h_c22] at h_v0
        rw [h_c23] at h_v1
        rw [h_c24] at h_v2
        rw [h_c25] at h_v3
        exact ⟨h_v0.symm, h_v1.symm, h_v2.symm, h_v3.symm⟩
      . exact MISSING_LBU_extends_correctly h_x0
    obtain ⟨ h_v0, h_v1, h_v2, h_v3 ⟩ := h_val_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    . -- (a) u16 range. `value_0 = selected_byte < 256`
      -- (from `MISSING_LBU_selected_byte_in_range`); others = 0.
      simp [*]; omega
    . -- (b) 65536 ≤ addr. Same proof as `spec_LB`.
      have h_alu_nat := h_alu_eq
      apply_fun BitVec.toNat at h_alu_nat
      simp at h_alu_nat
      rw [← h_alu_nat]
      have h_sum_ne :
          air.cols.values.addr_word_1 row 0 +
          air.cols.values.addr_word_2 row 0 ≠ 0 := by
        intro h_zero; rw [h_zero] at h_c1; simp at h_c1
      have h_sum_nat_ne :
          (air.cols.values.addr_word_1 row 0).val +
          (air.cols.values.addr_word_2 row 0).val ≠ 0 := by
        intro h_zero; apply h_sum_ne
        simp [Fin.ext_iff, Fin.add_def]; omega
      simp [U64w.toNat, h_c0]
      omega
    . -- (c) addr < 2^48. Same proof as `spec_LB`.
      apply_fun BitVec.toNat at h_alu_eq
      simp at h_alu_eq
      rw [← h_alu_eq]
      simp [U64w.toNat, h_c0]
      omega
    . -- (d) LBU zero-extension: `a = setWidth 64 (setWidth 8 a)`.
      -- After rewriting `value_i` via `h_v0..3`, both sides reduce to
      -- `U64w.toBV #v[selected_byte, 0, 0, 0]` (the RHS via
      -- `setWidth 64 (setWidth 8 …)`, lossless because `selected_byte
      -- < 256` from `MISSING_LBU_selected_byte_in_range`).
      rw [h_v0, h_v1, h_v2, h_v3]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, U64w.toNat,
            -BitVec.reduceToNat, -BitVec.toNat_ofNat]
      repeat rw [BitVec.toNat_ofNat]
      omega

  -- ====================================
  -- LH (Load Halfword, signed) — opcode 11
  -- ====================================

  lemma spec_LH
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 11)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- LH sign-extends the loaded halfword. The chip's c52..c55 (neg
    -- branch) and c60..c63 (pos branch) together compute:
    --   `value_0 = selected_limb`,
    --   `value_{1,2,3} = msb · 0xFFFF` (with `msb = bit_15(selected_limb)`).
    -- Both branches are gated by `(1 - op_a_0)`; when `op_a_0 = 1`
    -- (rd = x0) the value_i columns are unconstrained. Pico-side fix:
    -- drop the `(1 - op_a_0)` factor from c46/c47.
    (MISSING_LH_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_limb row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 =
          air.cols.values.msb row 0 * 65535)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    -- TODO: 5 LH MemoryBus.Spec conjuncts:
    --   (a) u16 limb bounds — via h_val_eq + U16MSB byte-bus check
    --       (gated by -is_lh) bounding `selected_limb < 65536`;
    --   (b) `65536 ≤ addr` — copy from `spec_LB`;
    --   (c) `addr < 2^48` — copy from `spec_LB`;
    --   (d) `2 ∣ addr` — c9 forces `offset_bit_0 = 0` for LH; combine
    --       with the ByteBus 9 (BitRange-13) check on
    --       `(aw_0 - offset_decoded)·inv(8)` to get `2 ∣ aw_0`;
    --   (e) signExtend equation — same shape as `spec_LB`'s (d), with
    --       `selected_limb` taking the role of `selected_byte` and
    --       bit-15 as the sign bit.
    sorry

  -- =====================================
  -- LHU (Load Halfword, unsigned) — opcode 14
  -- =====================================

  lemma spec_LHU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 14)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- LHU zero-extends the loaded halfword. c42 forces `msb = 0` for
    -- LHU, so the canonical layout is:
    --   `value_0 = selected_limb`, `value_{1,2,3} = 0`.
    (MISSING_LHU_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_limb row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 = 0)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    -- TODO: 5 LHU MemoryBus.Spec conjuncts. The U16MSB byte-bus check
    -- on selected_limb is gated by `-is_lh`, vacuous for LHU; so
    -- `selected_limb < 65536` must come from c20 + state-bus u16 bounds
    -- on `memory_access.prev_value_i` + the `limb_select` one-hot
    -- (offset_bit_1, offset_bit_2 case split). Alignment 2|addr from
    -- c9. Extension is zero-extend 16 (no sign bit).
    sorry

  -- ====================================
  -- LW (Load Word, signed) — opcode 12
  -- ====================================

  lemma spec_LW
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 12)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- LW sign-extends the loaded word. c56..c59 / c60..c63 enforce:
    --   `value_0 = selected_word_0`, `value_1 = selected_word_1`,
    --   `value_{2,3} = msb · 0xFFFF` (`msb = bit_15(selected_word_1)`).
    (MISSING_LW_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_word_0 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 =
          air.cols.values.selected_word_1 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 =
          air.cols.values.msb row 0 * 65535 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 =
          air.cols.values.msb row 0 * 65535)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    -- TODO: 5 LW conjuncts. selected_word_1 < 65536 from U16MSB byte
    -- bus (gated by -is_lw). selected_word_0 < 65536 from c30 + state
    -- bus + offset_bit_2 case split. Alignment 4|addr from c10
    -- (offset_bit_0 = offset_bit_1 = 0). Sign-extension to 64 bits via
    -- the upper-32-bit fill (msb relates to bit-15 of selected_word_1).
    sorry

  -- ======================================
  -- LWU (Load Word, unsigned) — opcode 45
  -- ======================================

  lemma spec_LWU
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 45)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- LWU zero-extends the loaded word. c44 forces `msb = 0` for LWU:
    --   `value_0 = selected_word_0`, `value_1 = selected_word_1`,
    --   `value_{2,3} = 0`.
    (MISSING_LWU_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.selected_word_0 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 =
          air.cols.values.selected_word_1 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 = 0 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 = 0)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    -- TODO: 5 LWU conjuncts. U16MSB on selected_word_1 is gated by
    -- `-is_lw`, vacuous for LWU. selected_word_{0,1} < 65536 from
    -- c30/c31 + state bus + offset_bit_2 case split. Alignment 4|addr
    -- from c10 (offset_bit_0 = offset_bit_1 = 0). Extension zero-ext 32.
    sorry

  -- ========================================
  -- LD (Load Doubleword) — opcode 46
  -- ========================================

  lemma spec_LD
    [Field ExtF]
    (air : Valid_MemoryReadWriteChip FKB ExtF)
    (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_is_real : air.cols.values.is_real row 0 = 1)
    (h_constraints : MemoryReadWriteChip.Extraction.allHold air row)
    (h_opcode : air.cols.values.instruction.opcode row 0 = 46)
    -- SOUNDNESS-BUG HYPOTHESIS — `mrw-op-a-x0-soundness-gap`.
    -- LD has no extension; c36..c39 enforce
    --   `unsigned_mem_val_i = memory_access.prev_value_i`,
    -- and c60..c63 (pos branch, fires for LD since c44 forces msb = 0)
    -- give `value_i = unsigned_mem_val_i`. When `op_a_0 = 1` the latter
    -- gate goes vacuous; the assumed fix preserves the equation.
    (MISSING_LD_extends_correctly :
      air.cols.values.instruction.op_a_0 row 0 = 1 →
        air.cols.values.instruction.op_a_access.access.value_0 row 0 =
          air.cols.values.memory_access.prev_value_0 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_1 row 0 =
          air.cols.values.memory_access.prev_value_1 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_2 row 0 =
          air.cols.values.memory_access.prev_value_2 row 0 ∧
        air.cols.values.instruction.op_a_access.access.value_3 row 0 =
          air.cols.values.memory_access.prev_value_3 row 0)
  :
    MemoryBus.Spec
      (air.cols.values.instruction.opcode row 0)
      (air.cols.values.instruction.op_a_access.access.value_0 row 0)
      (air.cols.values.instruction.op_a_access.access.value_1 row 0)
      (air.cols.values.instruction.op_a_access.access.value_2 row 0)
      (air.cols.values.instruction.op_a_access.access.value_3 row 0)
      (air.cols.values.instruction.op_b_access.access.value_0 row 0)
      (air.cols.values.instruction.op_b_access.access.value_1 row 0)
      (air.cols.values.instruction.op_b_access.access.value_2 row 0)
      (air.cols.values.instruction.op_b_access.access.value_3 row 0)
      (air.cols.values.instruction.op_c_access.access.value_0 row 0)
      (air.cols.values.instruction.op_c_access.access.value_1 row 0)
      (air.cols.values.instruction.op_c_access.access.value_2 row 0)
      (air.cols.values.instruction.op_c_access.access.value_3 row 0)
  := by
    -- TODO: 4 LD conjuncts. (a) u16 directly from state-bus bounds on
    -- `memory_access.prev_value_i` via h_val_eq. (b), (c) copy from LB.
    -- (d) 8|addr from c11 (offset bits all 0 for LD) + ByteBus 9
    -- (BitRange-13) check on `(aw_0 - offset_decoded)·inv(8)`. No
    -- extension equation (LD is not in the load-eq conjuncts of
    -- `MemoryBus.Spec`).
    sorry

end MemoryReadWriteChip.Spec
