import PicoFV.RV64IM.Constraints.AddwGadget
import PicoFV.RV64IM.Spec.U16MSBGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# AddwGadget — semantic specification (parametric)

The `AddwGadget.Spec` namespace below states the *parametric* semantic
content of the gadget: under the gadget's constraints and external u16
range assumptions on the operand-low limbs, the result word satisfies
the actual 32-bit ADDW (low-32-bit addition with sign-extension to 64
bits), as captured by `RV64IM.execute_RTYPEW_pure ... .ADDW`.

Since `AddwGadget` is used in exactly one chip (`AddwChip`), this file
provides only the pure `gadget_spec`. There is no standalone
`Valid_AddwGadgetAir`, so no air-based `spec` wrapper or `ext_asrt` /
`wf_asrt` lemmas are defined here — the chip embedding the gadget
plumbs its own hypotheses through to `gadget_spec`.

The high two limbs of the full 64-bit result are produced by the chip
itself (not the gadget) as `msb * 65535`, which equals `0x0000` when
`msb = 0` and `0xFFFF` when `msb = 1` — exactly the sign-extension
pattern. The gadget pins `msb` to bit-15 of `value_1` via the third
byte-bus entry (`U16Range` on `2 * value_1 - msb * 65536`).
-/

namespace AddwGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec.

      The gadget itself only sees the *low 32 bits* of `b` and `c`
      (limbs 0..1). For the statement to match the way the chip will
      consume it (the chip naturally has the full 64-bit operands and
      strips to 32 via `BitVec.setWidth 32`), this lemma takes all four
      limbs of `b` and `c` as parameters but only requires u16 range
      hypotheses on the low two limbs — the high limbs (`b_2`, `b_3`,
      `c_2`, `c_3`) are irrelevant since `.setWidth 32` discards them.

      The conclusion is exactly the shape `ALUBus.Spec 40` expects: a
      `result_range` (all four `a_i` limbs < 65536, where the high two
      are the gadget-supplied `msb * 65535`) plus the equation
      `value = execute_RTYPEW_pure b_lo c_lo .ADDW` (which under the
      hood unfolds to `sign_extend (m := 64) (b_lo + c_lo)`). -/
  lemma gadget_spec
    (is_real
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     value_0 value_1 msb : FKB)
    (h_gadget_ext_asm :
      bus_row_ext_asm
        (AddwGadget.AbsBuses is_real value_0 value_1 msb))
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (AddwGadget.AbsBuses is_real value_0 value_1 msb))
    (h_gadget_constraints :
      AddwGadget.AbsConstraints
        is_real b_0 b_1 c_0 c_1 value_0 value_1 msb)
    (h_is_real : is_real = 1)
    (h_b_range :
      b_0.val < 65536 ∧ b_1.val < 65536)
    (h_c_range :
      c_0.val < 65536 ∧ c_1.val < 65536)
  :
    value_0.val < 65536 ∧
    value_1.val < 65536 ∧
    (msb * 65535 : FKB).val < 65536 ∧
    U64w.toBV #v[value_0, value_1, (msb * 65535 : FKB), (msb * 65535 : FKB)]
    =
    RV64IM.execute_RTYPEW_pure
      ((U64w.toBV #v[b_0, b_1, b_2, b_3]).setWidth 32)
      ((U64w.toBV #v[c_0, c_1, c_2, c_3]).setWidth 32)
      .ADDW
  := by
    simp [AbsBuses] at h_gadget_wf_asm h_gadget_ext_asm
    obtain ⟨ h_gadget_wf_asm, h_wf_msb ⟩ := h_gadget_wf_asm
    obtain ⟨ h_gadget_ext_asm, h_ext_msb ⟩ := h_gadget_ext_asm; clear h_gadget_ext_asm
    simp [bus_row_wf_asm, h_is_real, ByteBus.Spec] at h_gadget_wf_asm
    simp [AbsConstraints, sub_eq_zero, h_is_real] at h_gadget_constraints
    have msb_spec := U16MSBGadget.Spec.gadget_spec is_real _ _ h_wf_msb (by grind) h_is_real (by tauto)
    obtain ⟨ h0, h1, h2, h_cstr_msb ⟩ := h_gadget_constraints
    simp [h_gadget_wf_asm]
    split_ands
    . omega
    . trans (U32w.extend (#v[value_0, value_1]) true).toBV
      . simp [U32w.extend, U32w.ext]
        suffices h_msb :
          BitVec.ofNat 16 ↑(msb * 65535) =
            if U32w.negative #v[BitVec.ofNat 16 ↑value_0, BitVec.ofNat 16 ↑value_1] then 65535#16 else 0#16
        . congr
        . simp [← U32w.msb_1_negative, BitVec.msb_eq_decide]
          clear *- h_gadget_wf_asm msb_spec; grind
      . simp [RV64IM.execute_RTYPEW_pure]
        simp [U32w.extend_BitVec_extend, BitVec.extend]
        congr
        apply BitVec.eq_of_toNat_eq
        simp [U32w.toNat]
        repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
        obtain h0 | h0 := h0 <;>
        simp [h0] at h1 <;>
          obtain h1 | h1 := h1 <;>
          omega

end AddwGadget.Spec
