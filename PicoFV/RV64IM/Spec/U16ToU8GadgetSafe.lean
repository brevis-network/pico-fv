import PicoFV.RV64IM.Constraints.U16ToU8GadgetSafe

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# U16ToU8GadgetSafe — semantic specification (parametric)

`U16ToU8GadgetSafe` is self-contained: the four `U8Pair` byte-bus
lookups it emits force, *without any external range hypothesis on
`a`*, that each `a_i` is a valid u16 with canonical byte split

```
a_i.val = low_bytes_i.val + 256 · high_byte_i.val
       with low_bytes_i.val, high_byte_i.val < 256
```

where `high_byte_i := (a_i − low_bytes_i) · 2122383361`
(`2122383361 = 256⁻¹ mod FKB`).

The reason no external range check is needed: from
`low_bytes_i.val < 256` and `high_byte_i.val < 256` the natural-number
sum `low_bytes_i.val + 256 · high_byte_i.val ≤ 255 + 256·255 = 65535`
falls below the field prime `2130706433`, so the FKB identity
`a_i = low_bytes_i + 256 · high_byte_i` (which holds purely
algebraically because `256 · 256⁻¹ = 1`) lifts to a wrap-free
equality on `.val`. Uniqueness of `(quotient, remainder)` mod 256 in
`[0, 256)` then identifies the two bytes with `a_i.val / 256` and
`a_i.val % 256`.

The gadget has no algebraic constraints — everything below comes from
the four `U8Pair` byte-bus entries.
-/

namespace U16ToU8GadgetSafe.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000

  /-- Pure / parametric gadget spec. Per limb, exposes:
      * the u16 bound `a_i.val < 65536`,
      * the canonical byte split
        `low_bytes_i.val = a_i.val % 256`,
        `((a_i - low_bytes_i) * 2122383361).val = a_i.val / 256`,
      * and the two `< 256` byte bounds. -/
  lemma gadget_spec
    (is_real
     a_0 a_1 a_2 a_3
     low_bytes_0 low_bytes_1 low_bytes_2 low_bytes_3 : FKB)
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (U16ToU8GadgetSafe.AbsBuses is_real a_0 a_1 a_2 a_3
          low_bytes_0 low_bytes_1 low_bytes_2 low_bytes_3))
    (h_is_real : is_real = 1)
  :
    (a_0.val < 65536 ∧
     low_bytes_0.val < 256 ∧
     ((a_0 - low_bytes_0) * 2122383361).val < 256 ∧
     low_bytes_0.val = a_0.val % 256 ∧
     ((a_0 - low_bytes_0) * 2122383361).val = a_0.val / 256) ∧
    (a_1.val < 65536 ∧
     low_bytes_1.val < 256 ∧
     ((a_1 - low_bytes_1) * 2122383361).val < 256 ∧
     low_bytes_1.val = a_1.val % 256 ∧
     ((a_1 - low_bytes_1) * 2122383361).val = a_1.val / 256) ∧
    (a_2.val < 65536 ∧
     low_bytes_2.val < 256 ∧
     ((a_2 - low_bytes_2) * 2122383361).val < 256 ∧
     low_bytes_2.val = a_2.val % 256 ∧
     ((a_2 - low_bytes_2) * 2122383361).val = a_2.val / 256) ∧
    (a_3.val < 65536 ∧
     low_bytes_3.val < 256 ∧
     ((a_3 - low_bytes_3) * 2122383361).val < 256 ∧
     low_bytes_3.val = a_3.val % 256 ∧
     ((a_3 - low_bytes_3) * 2122383361).val = a_3.val / 256)
  := by
    simp [bus_row_wf_asm, U16ToU8GadgetSafe.AbsBuses, h_is_real, ByteBus.Spec]
      at h_gadget_wf_asm
    simp [h_gadget_wf_asm]
    obtain ⟨ h0, h1, h2, h3 ⟩ := h_gadget_wf_asm
    have eq0 := KoalaBear.inv256_prod_diff_div_mod h0.1 h0.2
    have eq1 := KoalaBear.inv256_prod_diff_div_mod h1.1 h1.2
    have eq2 := KoalaBear.inv256_prod_diff_div_mod h2.1 h2.2
    have eq3 := KoalaBear.inv256_prod_diff_div_mod h3.1 h3.2
    simp [eq0.2.2, eq1.2.2, eq2.2.2, eq3.2.2]
    simp [eq0, eq1, eq2, eq3]
    omega

end U16ToU8GadgetSafe.Spec
