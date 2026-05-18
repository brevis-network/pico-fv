import PicoFV.RV64IM.Constraints.MulChip
import PicoFV.RV64IM.Spec.MulGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MulChip — semantic specification

Five per-selector specs (`spec_MUL`, `spec_MULH`, `spec_MULHU`,
`spec_MULHSU`, `spec_MULW`) each derive
`ALUBus.Spec OPCODE a b c` for the appropriate ALU bus opcode:

| Selector active | Opcode |
|-----------------|--------|
| `is_mul = 1`    | 30     |
| `is_mulh = 1`   | 31     |
| `is_mulhu = 1`  | 32     |
| `is_mulhsu = 1` | 33     |
| `is_mulw = 1`   | 48     |

Each proof follows the same shape:
1. Use `selector_breakdown` to obtain `each_selector ∈ {0, 1}` plus
   the at-most-one fact `sum ∈ {0, 1}`.
2. From the active-selector hypothesis (e.g. `is_mul = 1`) plus the
   at-most-one fact, deduce that the other selectors are `0`.
3. Invoke `MulGadget.Spec.gadget_spec` (which yields
   `ALUBus.Spec (selector-encoded opcode) a b c`); under the
   substitutions from step 2, the selector-encoded opcode resolves to
   the concrete opcode `30 / 31 / 32 / 33 / 48`.

Because `MulGadget.Spec.gadget_spec` is currently `sorry`, the five
chip-level specs below are also `sorry`. The statements form the
binding interface that `CpuChip` will consume for `MUL` family
opcodes.
-/

namespace MulChip.Spec

  open RV64IM_Interactions
  open MulChip.ConstraintsAndBuses
  open MulChip.Interactions
  open MulChip.Interpretations

  set_option maxHeartbeats 1_000_000_000

  -- ========================================================================
  -- spec_MUL  (ALU opcode 30): low 64 bits of unsigned product.
  -- ========================================================================

  lemma spec_MUL
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulChip.Extraction.allHold air row)
    (h_is_mul : air.cols.values.is_mul row 0 = 1)
  :
    ALUBus.Spec 30
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨_, _, _, _, _, h_sum⟩ := selector_breakdown air row h_constraints
    have h_is_mulh   : air.cols.values.is_mulh   row 0 = 0 := by grind
    have h_is_mulhu  : air.cols.values.is_mulhu  row 0 = 0 := by grind
    have h_is_mulhsu : air.cols.values.is_mulhsu row 0 = 0 := by grind
    have h_is_mulw   : air.cols.values.is_mulw   row 0 = 0 := by grind
    have h_abs := allHold_abs air row h_constraints
    simp only [AbsConstraints] at h_abs
    obtain ⟨h_gadget, _, _, _, _, _, _⟩ := h_abs
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_ext_asm_append] at h_ext
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_wf_asm_append] at h_wf
    obtain ⟨ h_gadget_ext, _ ⟩ := h_ext
    obtain ⟨ h_gadget_wf, _ ⟩ := h_wf
    have h_gadget_spec := MulGadget.Spec.gadget_spec
      (air.cols.values.is_mul row 0 +
       air.cols.values.is_mulh row 0 +
       air.cols.values.is_mulhu row 0 +
       air.cols.values.is_mulhsu row 0 +
       air.cols.values.is_mulw row 0)
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulw row 0) (air.cols.values.is_mulhu row 0)
      (air.cols.values.is_mulhsu row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)
      h_gadget h_gadget_ext h_gadget_wf
      (by simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw])
      rfl
    simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw]
      at h_gadget_spec
    exact h_gadget_spec

  -- ========================================================================
  -- spec_MULH  (ALU opcode 31): high 64 bits of signed × signed.
  -- ========================================================================

  lemma spec_MULH
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulChip.Extraction.allHold air row)
    (h_is_mulh : air.cols.values.is_mulh row 0 = 1)
  :
    ALUBus.Spec 31
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨_, _, _, _, _, h_sum⟩ := selector_breakdown air row h_constraints
    have h_is_mul    : air.cols.values.is_mul    row 0 = 0 := by grind
    have h_is_mulhu  : air.cols.values.is_mulhu  row 0 = 0 := by grind
    have h_is_mulhsu : air.cols.values.is_mulhsu row 0 = 0 := by grind
    have h_is_mulw   : air.cols.values.is_mulw   row 0 = 0 := by grind
    have h_abs := allHold_abs air row h_constraints
    simp only [AbsConstraints] at h_abs
    obtain ⟨h_gadget, _, _, _, _, _, _⟩ := h_abs
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_ext_asm_append] at h_ext
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_wf_asm_append] at h_wf
    obtain ⟨ h_gadget_ext, _ ⟩ := h_ext
    obtain ⟨ h_gadget_wf, _ ⟩ := h_wf
    have h_gadget_spec := MulGadget.Spec.gadget_spec
      (air.cols.values.is_mul row 0 +
       air.cols.values.is_mulh row 0 +
       air.cols.values.is_mulhu row 0 +
       air.cols.values.is_mulhsu row 0 +
       air.cols.values.is_mulw row 0)
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulw row 0) (air.cols.values.is_mulhu row 0)
      (air.cols.values.is_mulhsu row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)
      h_gadget h_gadget_ext h_gadget_wf
      (by simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw])
      rfl
    simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw]
      at h_gadget_spec
    exact h_gadget_spec

  -- ========================================================================
  -- spec_MULHU  (ALU opcode 32): high 64 bits of unsigned × unsigned.
  -- ========================================================================

  lemma spec_MULHU
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulChip.Extraction.allHold air row)
    (h_is_mulhu : air.cols.values.is_mulhu row 0 = 1)
  :
    ALUBus.Spec 32
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨_, _, _, _, _, h_sum⟩ := selector_breakdown air row h_constraints
    have h_is_mul    : air.cols.values.is_mul    row 0 = 0 := by grind
    have h_is_mulh   : air.cols.values.is_mulh   row 0 = 0 := by grind
    have h_is_mulhsu : air.cols.values.is_mulhsu row 0 = 0 := by grind
    have h_is_mulw   : air.cols.values.is_mulw   row 0 = 0 := by grind
    have h_abs := allHold_abs air row h_constraints
    simp only [AbsConstraints] at h_abs
    obtain ⟨h_gadget, _, _, _, _, _, _⟩ := h_abs
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_ext_asm_append] at h_ext
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_wf_asm_append] at h_wf
    obtain ⟨ h_gadget_ext, _ ⟩ := h_ext
    obtain ⟨ h_gadget_wf, _ ⟩ := h_wf
    have h_gadget_spec := MulGadget.Spec.gadget_spec
      (air.cols.values.is_mul row 0 +
       air.cols.values.is_mulh row 0 +
       air.cols.values.is_mulhu row 0 +
       air.cols.values.is_mulhsu row 0 +
       air.cols.values.is_mulw row 0)
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulw row 0) (air.cols.values.is_mulhu row 0)
      (air.cols.values.is_mulhsu row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)
      h_gadget h_gadget_ext h_gadget_wf
      (by simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw])
      rfl
    simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw]
      at h_gadget_spec
    exact h_gadget_spec

  -- ========================================================================
  -- spec_MULHSU  (ALU opcode 33): high 64 bits of signed b · unsigned c.
  -- ========================================================================

  lemma spec_MULHSU
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulChip.Extraction.allHold air row)
    (h_is_mulhsu : air.cols.values.is_mulhsu row 0 = 1)
  :
    ALUBus.Spec 33
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    obtain ⟨_, _, _, _, _, h_sum⟩ := selector_breakdown air row h_constraints
    have h_is_mul    : air.cols.values.is_mul    row 0 = 0 := by grind
    have h_is_mulh   : air.cols.values.is_mulh   row 0 = 0 := by grind
    have h_is_mulhu  : air.cols.values.is_mulhu  row 0 = 0 := by grind
    have h_is_mulw   : air.cols.values.is_mulw   row 0 = 0 := by grind
    have h_abs := allHold_abs air row h_constraints
    simp only [AbsConstraints] at h_abs
    obtain ⟨h_gadget, _, _, _, _, _, _⟩ := h_abs
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_ext_asm_append] at h_ext
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_wf_asm_append] at h_wf
    obtain ⟨ h_gadget_ext, _ ⟩ := h_ext
    obtain ⟨ h_gadget_wf, _ ⟩ := h_wf
    have h_gadget_spec := MulGadget.Spec.gadget_spec
      (air.cols.values.is_mul row 0 +
       air.cols.values.is_mulh row 0 +
       air.cols.values.is_mulhu row 0 +
       air.cols.values.is_mulhsu row 0 +
       air.cols.values.is_mulw row 0)
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulw row 0) (air.cols.values.is_mulhu row 0)
      (air.cols.values.is_mulhsu row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0) (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0) (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0) (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0) (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0) (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0) (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0) (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0) (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0) (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0) (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0) (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0) (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0) (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0) (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0) (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0) (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)
      h_gadget h_gadget_ext h_gadget_wf
      (by simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw])
      rfl
    simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw]
      at h_gadget_spec
    exact h_gadget_spec

  -- ========================================================================
  -- spec_MULW  (ALU opcode 48): sign-extended low 32 bits of `b · c`.
  -- ========================================================================

  lemma spec_MULW
    [Field ExtF]
    (air : Valid_MulChip FKB ExtF) (row : ℕ)
    (h_ext : bus_row_ext_asm (bus_row air row))
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : MulChip.Extraction.allHold air row)
    (h_is_mulw : air.cols.values.is_mulw row 0 = 1)
  :
    ALUBus.Spec 48
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    -- Selector facts: each ∈ {0, 1} and sum ∈ {0, 1}.
    obtain ⟨_, _, _, _, _, h_sum⟩ := selector_breakdown air row h_constraints
    -- With `is_mulw = 1`, the sum has a `1` term so it can't be 0,
    -- and we have a `bool` check on each selector, so each other
    -- selector is forced to 0.
    have h_is_mul    : air.cols.values.is_mul    row 0 = 0 := by grind
    have h_is_mulh   : air.cols.values.is_mulh   row 0 = 0 := by grind
    have h_is_mulhu  : air.cols.values.is_mulhu  row 0 = 0 := by grind
    have h_is_mulhsu : air.cols.values.is_mulhsu row 0 = 0 := by grind
    -- Extract the chip's `AbsConstraints` (which contains the
    -- gadget's `AbsConstraints` as its first component).
    have h_abs := allHold_abs air row h_constraints
    simp only [AbsConstraints] at h_abs
    obtain ⟨h_gadget, _, _, _, _, _, _⟩ := h_abs
    -- Extract the gadget's bus `ext_asm` / `wf_asm` from the chip's
    -- via `bus_row_abs` + `_append` (`MulChip.AbsBuses = MulGadget.AbsBuses ++ <ALU entry>`).
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_ext_asm_append] at h_ext
    rw [bus_row_abs, MulChip.AbsBuses, bus_row_wf_asm_append] at h_wf
    obtain ⟨ h_gadget_ext, _ ⟩ := h_ext
    obtain ⟨ h_gadget_wf, _ ⟩ := h_wf
    -- Invoke the gadget's parametric spec — operand and result ranges
    -- are baked into the `ALUBus.Spec` conclusion, so no separate
    -- range hypotheses are needed.
    have h_gadget_spec := MulGadget.Spec.gadget_spec
      (air.cols.values.is_mul row 0 +
       air.cols.values.is_mulh row 0 +
       air.cols.values.is_mulhu row 0 +
       air.cols.values.is_mulhsu row 0 +
       air.cols.values.is_mulw row 0)
      (air.cols.values.is_mul row 0) (air.cols.values.is_mulh row 0)
      (air.cols.values.is_mulw row 0) (air.cols.values.is_mulhu row 0)
      (air.cols.values.is_mulhsu row 0)
      (air.cols.values.a_0 row 0) (air.cols.values.a_1 row 0)
      (air.cols.values.a_2 row 0) (air.cols.values.a_3 row 0)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
      (air.cols.values.mul_gadget.carry_0 row 0)
      (air.cols.values.mul_gadget.carry_1 row 0)
      (air.cols.values.mul_gadget.carry_2 row 0)
      (air.cols.values.mul_gadget.carry_3 row 0)
      (air.cols.values.mul_gadget.carry_4 row 0)
      (air.cols.values.mul_gadget.carry_5 row 0)
      (air.cols.values.mul_gadget.carry_6 row 0)
      (air.cols.values.mul_gadget.carry_7 row 0)
      (air.cols.values.mul_gadget.carry_8 row 0)
      (air.cols.values.mul_gadget.carry_9 row 0)
      (air.cols.values.mul_gadget.carry_10 row 0)
      (air.cols.values.mul_gadget.carry_11 row 0)
      (air.cols.values.mul_gadget.carry_12 row 0)
      (air.cols.values.mul_gadget.carry_13 row 0)
      (air.cols.values.mul_gadget.carry_14 row 0)
      (air.cols.values.mul_gadget.carry_15 row 0)
      (air.cols.values.mul_gadget.product_0 row 0)
      (air.cols.values.mul_gadget.product_1 row 0)
      (air.cols.values.mul_gadget.product_2 row 0)
      (air.cols.values.mul_gadget.product_3 row 0)
      (air.cols.values.mul_gadget.product_4 row 0)
      (air.cols.values.mul_gadget.product_5 row 0)
      (air.cols.values.mul_gadget.product_6 row 0)
      (air.cols.values.mul_gadget.product_7 row 0)
      (air.cols.values.mul_gadget.product_8 row 0)
      (air.cols.values.mul_gadget.product_9 row 0)
      (air.cols.values.mul_gadget.product_10 row 0)
      (air.cols.values.mul_gadget.product_11 row 0)
      (air.cols.values.mul_gadget.product_12 row 0)
      (air.cols.values.mul_gadget.product_13 row 0)
      (air.cols.values.mul_gadget.product_14 row 0)
      (air.cols.values.mul_gadget.product_15 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.b_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_0 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_1 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_2 row 0)
      (air.cols.values.mul_gadget.c_lower_byte.low_bytes_3 row 0)
      (air.cols.values.mul_gadget.b_msb row 0)
      (air.cols.values.mul_gadget.c_msb row 0)
      (air.cols.values.mul_gadget.product_msb.msb row 0)
      (air.cols.values.mul_gadget.b_sign_extend row 0)
      (air.cols.values.mul_gadget.c_sign_extend row 0)
      h_gadget
      h_gadget_ext
      h_gadget_wf
      (by simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw])
      rfl
    -- The gadget's selector-encoded opcode collapses to 48 under our
    -- selector substitutions.
    simp [h_is_mul, h_is_mulh, h_is_mulhu, h_is_mulhsu, h_is_mulw]
      at h_gadget_spec
    exact h_gadget_spec

end MulChip.Spec
