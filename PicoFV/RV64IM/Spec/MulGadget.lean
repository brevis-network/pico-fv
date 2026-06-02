import PicoFV.RV64IM.Constraints.MulGadget
import PicoFV.RV64IM.Spec.U16MSBGadget
import PicoFV.RV64IM.Spec.U16ToU8GadgetSafe
import PicoFV.RV64IM.Spec.MulGadgetCore
import PicoFV.RV64IM.RVSail.Execution
import PicoFV.RV64IM.RVSail.Buses
import Mathlib.Tactic.LinearCombination

open Plonky3
open RV64IM

set_option maxHeartbeats 1_000_000_000

/-!
# MulGadget — semantic specification (parametric)

`MulGadget` computes (a window of) the 128-bit product `b · c` and
places it into the 64-bit output word `a`, with the window selected by
the active operation flag. The spec is a conjunction of selector-
conditional equations, one per supported opcode, expressed via the
Sail-derived pure semantics in `RVSail.Execution`:

The opcode is computed from the selector indicators (one-hot under the
parent invariant `is_real = is_mul + is_mulh + is_mulhu + is_mulhsu +
is_mulw`), so the conclusion is a single `ALUBus.Spec` claim rather
than a five-way conjunction:

```
opcode := is_mul · 30 + is_mulh · 31 + is_mulhu · 32 + is_mulhsu · 33 + is_mulw · 48
```

With `is_real = 1` and `is_real = sum_of_selectors`, exactly one
selector is `1` and the others `0`, so `opcode` resolves to one of
`{30, 31, 32, 33, 48}` (MUL / MULH / MULHU / MULHSU / MULW).
`ALUBus.Spec` then packages the u16 result range + operand range +
the canonical `execute_*_pure` equation for that opcode.

All 45 internal witness columns (`carry_0..15`, `product_0..15`,
`b_lower_byte_*`, `c_lower_byte_*`, `b_msb`, `c_msb`, `product_msb`,
`b_sign_extend`, `c_sign_extend`) are exposed as explicit parameters,
matching the rest of the gadget Specs in this directory.

The proof of `gadget_spec` is currently `sorry` — the algebraic
content (correct polynomial multiplication with 16-byte carry
propagation, sign-extension handling, and per-selector windowing) is
substantial and deferred. The statement is the binding interface that
`DivRemChip`'s two `MulGadget` instantiations will consume.
-/

namespace MulGadget.Spec

  open RV64IM_Interactions

  set_option maxHeartbeats 1_000_000_000
  set_option maxRecDepth 1_000_000

  /-- Compose two u8-ranged field elements into a `BitVec 16` via
      `low + high * 256`. Simpler sibling of `limb_decomp` — no
      `inv(256)` algebra, used for the chip's result limbs where both
      bytes are explicit. -/
  private lemma bv16_from_bytes (low high : FKB)
      (h_low : low.val < 256) (h_high : high.val < 256) :
      BitVec.ofNat 16 (low + high * 256 : FKB).val =
        BitVec.ofNat 8 high.val ++ BitVec.ofNat 8 low.val := by
    have h_high256 : (high * 256 : FKB).val = high.val * 256 := by grind
    have h_sum : (low + high * 256 : FKB).val = low.val + high.val * 256 := by grind
    rw [h_sum]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]; simp
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
    omega

  -- `core_mul_64` is the heavy schoolbook-multiplication identity; it
  -- lives in `Spec/MulGadgetCore.lean` to keep typechecking of this
  -- file fast. See that file for the lemma statement and proof.

  /-- Carry-chain lift, byte positions 0..15 (parametric in the bytes).

      The 16 `is_real * (...) = 0` FKB carry-chain constraints inside
      `MulGadget.AbsConstraints` are polynomial equations over the
      KoalaBear field. `core_mul_64` (in `Spec/MulGadgetCore.lean`)
      needs them as plain ℕ equations on the `Fin.val` of each byte /
      carry / product column. This lemma is the bridge.

      The 16 b-bytes (and 16 c-bytes) are exposed as **abstract**
      placeholders: `bb0..bb7` (low / high byte of `b_0..b_3`) and
      `bbS` (the sign-extension fill byte, reused for positions 8..15),
      analogously for `c`. At the call site you instantiate them with
      the actual byte expressions from the Pico extraction:

      ```
      bb0 ↦ b_lower_byte_0
      bb1 ↦ (b_0 - b_lower_byte_0) * 2122383361
      bb2 ↦ b_lower_byte_1
      bb3 ↦ (b_1 - b_lower_byte_1) * 2122383361
      bb4 ↦ b_lower_byte_2
      bb5 ↦ (b_2 - b_lower_byte_2) * 2122383361
      bb6 ↦ b_lower_byte_3
      bb7 ↦ (b_3 - b_lower_byte_3) * 2122383361
      bbS ↦ b_sign_extend * 255
      ```

      (and similarly for `c`). Lean unifies the placeholders with the
      literals at elaboration; nothing here cares about the shape of
      the underlying byte expression — only its u8 bound.

      The u8 bound on `bbS` (= `b_sign_extend * 255`) follows from
      `b_se_bool : b_sign_extend * (b_sign_extend - 1) = 0` at the
      call site. -/
  private lemma carry_chain_lift
    (is_real
     bb0 bb1 bb2 bb3 bb4 bb5 bb6 bb7 bbS
     cb0 cb1 cb2 cb3 cb4 cb5 cb6 cb7 cbS
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
       : FKB)
    -- raw `is_real * (...) = 0` carry-chain equations.
    (p0  : is_real * (product_0 - (bb0 * cb0 - carry_0 * 256)) = 0)
    (p1  : is_real * (product_1 - (bb0 * cb1 + bb1 * cb0 + carry_0 - carry_1 * 256)) = 0)
    (p2  : is_real *
             (product_2 - (bb0 * cb2 + bb1 * cb1 + bb2 * cb0 + carry_1 - carry_2 * 256)) = 0)
    (p3  : is_real *
             (product_3 -
               (bb0 * cb3 + bb1 * cb2 + bb2 * cb1 + bb3 * cb0 + carry_2 - carry_3 * 256)) = 0)
    (p4  : is_real *
             (product_4 -
               (bb0 * cb4 + bb1 * cb3 + bb2 * cb2 + bb3 * cb1 + bb4 * cb0
                + carry_3 - carry_4 * 256)) = 0)
    (p5  : is_real *
             (product_5 -
               (bb0 * cb5 + bb1 * cb4 + bb2 * cb3 + bb3 * cb2 + bb4 * cb1 + bb5 * cb0
                + carry_4 - carry_5 * 256)) = 0)
    (p6  : is_real *
             (product_6 -
               (bb0 * cb6 + bb1 * cb5 + bb2 * cb4 + bb3 * cb3 + bb4 * cb2 + bb5 * cb1
                + bb6 * cb0 + carry_5 - carry_6 * 256)) = 0)
    (p7  : is_real *
             (product_7 -
               (bb0 * cb7 + bb1 * cb6 + bb2 * cb5 + bb3 * cb4 + bb4 * cb3 + bb5 * cb2
                + bb6 * cb1 + bb7 * cb0 + carry_6 - carry_7 * 256)) = 0)
    (p8  : is_real *
             (product_8 -
               (bb0 * cbS + bb1 * cb7 + bb2 * cb6 + bb3 * cb5 + bb4 * cb4 + bb5 * cb3
                + bb6 * cb2 + bb7 * cb1 + bbS * cb0 + carry_7 - carry_8 * 256)) = 0)
    (p9  : is_real *
             (product_9 -
               (bb0 * cbS + bb1 * cbS + bb2 * cb7 + bb3 * cb6 + bb4 * cb5 + bb5 * cb4
                + bb6 * cb3 + bb7 * cb2 + bbS * cb1 + bbS * cb0 + carry_8 - carry_9 * 256)) = 0)
    (p10 : is_real *
             (product_10 -
               (bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cb7 + bb4 * cb6 + bb5 * cb5
                + bb6 * cb4 + bb7 * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0
                + carry_9 - carry_10 * 256)) = 0)
    (p11 : is_real *
             (product_11 -
               (bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cb7 + bb5 * cb6
                + bb6 * cb5 + bb7 * cb4 + bbS * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0
                + carry_10 - carry_11 * 256)) = 0)
    (p12 : is_real *
             (product_12 -
               (bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cb7
                + bb6 * cb6 + bb7 * cb5 + bbS * cb4 + bbS * cb3 + bbS * cb2 + bbS * cb1
                + bbS * cb0 + carry_11 - carry_12 * 256)) = 0)
    (p13 : is_real *
             (product_13 -
               (bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cbS
                + bb6 * cb7 + bb7 * cb6 + bbS * cb5 + bbS * cb4 + bbS * cb3 + bbS * cb2
                + bbS * cb1 + bbS * cb0 + carry_12 - carry_13 * 256)) = 0)
    (p14 : is_real *
             (product_14 -
               (bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cbS
                + bb6 * cbS + bb7 * cb7 + bbS * cb6 + bbS * cb5 + bbS * cb4 + bbS * cb3
                + bbS * cb2 + bbS * cb1 + bbS * cb0 + carry_13 - carry_14 * 256)) = 0)
    (p15 : is_real *
             (product_15 -
               (bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cbS
                + bb6 * cbS + bb7 * cbS + bbS * cb7 + bbS * cb6 + bbS * cb5 + bbS * cb4
                + bbS * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0
                + carry_14 - carry_15 * 256)) = 0)
    (h_is_real : is_real = 1)
    -- byte u8 bounds (abstract)
    (ub_bb0 : bb0.val < 256) (ub_bb1 : bb1.val < 256)
    (ub_bb2 : bb2.val < 256) (ub_bb3 : bb3.val < 256)
    (ub_bb4 : bb4.val < 256) (ub_bb5 : bb5.val < 256)
    (ub_bb6 : bb6.val < 256) (ub_bb7 : bb7.val < 256)
    (ub_bbS : bbS.val < 256)
    (ub_cb0 : cb0.val < 256) (ub_cb1 : cb1.val < 256)
    (ub_cb2 : cb2.val < 256) (ub_cb3 : cb3.val < 256)
    (ub_cb4 : cb4.val < 256) (ub_cb5 : cb5.val < 256)
    (ub_cb6 : cb6.val < 256) (ub_cb7 : cb7.val < 256)
    (ub_cbS : cbS.val < 256)
    -- carry u16 bounds
    (ub_cy0  : carry_0.val  < 65536) (ub_cy1  : carry_1.val  < 65536)
    (ub_cy2  : carry_2.val  < 65536) (ub_cy3  : carry_3.val  < 65536)
    (ub_cy4  : carry_4.val  < 65536) (ub_cy5  : carry_5.val  < 65536)
    (ub_cy6  : carry_6.val  < 65536) (ub_cy7  : carry_7.val  < 65536)
    (ub_cy8  : carry_8.val  < 65536) (ub_cy9  : carry_9.val  < 65536)
    (ub_cy10 : carry_10.val < 65536) (ub_cy11 : carry_11.val < 65536)
    (ub_cy12 : carry_12.val < 65536) (ub_cy13 : carry_13.val < 65536)
    (ub_cy14 : carry_14.val < 65536) (ub_cy15 : carry_15.val < 65536)
    -- product u8 bounds
    (ub_p0  : product_0.val  < 256) (ub_p1  : product_1.val  < 256)
    (ub_p2  : product_2.val  < 256) (ub_p3  : product_3.val  < 256)
    (ub_p4  : product_4.val  < 256) (ub_p5  : product_5.val  < 256)
    (ub_p6  : product_6.val  < 256) (ub_p7  : product_7.val  < 256)
    (ub_p8  : product_8.val  < 256) (ub_p9  : product_9.val  < 256)
    (ub_p10 : product_10.val < 256) (ub_p11 : product_11.val < 256)
    (ub_p12 : product_12.val < 256) (ub_p13 : product_13.val < 256)
    (ub_p14 : product_14.val < 256) (ub_p15 : product_15.val < 256)
  :
    -- i = 0
    (product_0.val + carry_0.val * 256
       = bb0.val * cb0.val)
    -- i = 1
    ∧ (product_1.val + carry_1.val * 256
         = bb0.val * cb1.val + bb1.val * cb0.val + carry_0.val)
    -- i = 2
    ∧ (product_2.val + carry_2.val * 256
         = bb0.val * cb2.val + bb1.val * cb1.val + bb2.val * cb0.val + carry_1.val)
    -- i = 3
    ∧ (product_3.val + carry_3.val * 256
         = bb0.val * cb3.val + bb1.val * cb2.val + bb2.val * cb1.val + bb3.val * cb0.val
           + carry_2.val)
    -- i = 4
    ∧ (product_4.val + carry_4.val * 256
         = bb0.val * cb4.val + bb1.val * cb3.val + bb2.val * cb2.val + bb3.val * cb1.val
           + bb4.val * cb0.val + carry_3.val)
    -- i = 5
    ∧ (product_5.val + carry_5.val * 256
         = bb0.val * cb5.val + bb1.val * cb4.val + bb2.val * cb3.val + bb3.val * cb2.val
           + bb4.val * cb1.val + bb5.val * cb0.val + carry_4.val)
    -- i = 6
    ∧ (product_6.val + carry_6.val * 256
         = bb0.val * cb6.val + bb1.val * cb5.val + bb2.val * cb4.val + bb3.val * cb3.val
           + bb4.val * cb2.val + bb5.val * cb1.val + bb6.val * cb0.val + carry_5.val)
    -- i = 7
    ∧ (product_7.val + carry_7.val * 256
         = bb0.val * cb7.val + bb1.val * cb6.val + bb2.val * cb5.val + bb3.val * cb4.val
           + bb4.val * cb3.val + bb5.val * cb2.val + bb6.val * cb1.val + bb7.val * cb0.val
           + carry_6.val)
    -- i = 8
    ∧ (product_8.val + carry_8.val * 256
         = bb0.val * cbS.val + bb1.val * cb7.val + bb2.val * cb6.val + bb3.val * cb5.val
           + bb4.val * cb4.val + bb5.val * cb3.val + bb6.val * cb2.val + bb7.val * cb1.val
           + bbS.val * cb0.val + carry_7.val)
    -- i = 9
    ∧ (product_9.val + carry_9.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cb7.val + bb3.val * cb6.val
           + bb4.val * cb5.val + bb5.val * cb4.val + bb6.val * cb3.val + bb7.val * cb2.val
           + bbS.val * cb1.val + bbS.val * cb0.val + carry_8.val)
    -- i = 10
    ∧ (product_10.val + carry_10.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cbS.val + bb3.val * cb7.val
           + bb4.val * cb6.val + bb5.val * cb5.val + bb6.val * cb4.val + bb7.val * cb3.val
           + bbS.val * cb2.val + bbS.val * cb1.val + bbS.val * cb0.val + carry_9.val)
    -- i = 11
    ∧ (product_11.val + carry_11.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cbS.val + bb3.val * cbS.val
           + bb4.val * cb7.val + bb5.val * cb6.val + bb6.val * cb5.val + bb7.val * cb4.val
           + bbS.val * cb3.val + bbS.val * cb2.val + bbS.val * cb1.val + bbS.val * cb0.val
           + carry_10.val)
    -- i = 12
    ∧ (product_12.val + carry_12.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cbS.val + bb3.val * cbS.val
           + bb4.val * cbS.val + bb5.val * cb7.val + bb6.val * cb6.val + bb7.val * cb5.val
           + bbS.val * cb4.val + bbS.val * cb3.val + bbS.val * cb2.val + bbS.val * cb1.val
           + bbS.val * cb0.val + carry_11.val)
    -- i = 13
    ∧ (product_13.val + carry_13.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cbS.val + bb3.val * cbS.val
           + bb4.val * cbS.val + bb5.val * cbS.val + bb6.val * cb7.val + bb7.val * cb6.val
           + bbS.val * cb5.val + bbS.val * cb4.val + bbS.val * cb3.val + bbS.val * cb2.val
           + bbS.val * cb1.val + bbS.val * cb0.val + carry_12.val)
    -- i = 14
    ∧ (product_14.val + carry_14.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cbS.val + bb3.val * cbS.val
           + bb4.val * cbS.val + bb5.val * cbS.val + bb6.val * cbS.val + bb7.val * cb7.val
           + bbS.val * cb6.val + bbS.val * cb5.val + bbS.val * cb4.val + bbS.val * cb3.val
           + bbS.val * cb2.val + bbS.val * cb1.val + bbS.val * cb0.val + carry_13.val)
    -- i = 15
    ∧ (product_15.val + carry_15.val * 256
         = bb0.val * cbS.val + bb1.val * cbS.val + bb2.val * cbS.val + bb3.val * cbS.val
           + bb4.val * cbS.val + bb5.val * cbS.val + bb6.val * cbS.val + bb7.val * cbS.val
           + bbS.val * cb7.val + bbS.val * cb6.val + bbS.val * cb5.val + bbS.val * cb4.val
           + bbS.val * cb3.val + bbS.val * cb2.val + bbS.val * cb1.val + bbS.val * cb0.val
           + carry_14.val)
  := by
    simp [h_is_real, sub_eq_zero, eq_sub_iff_add_eq]
      at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    have ub_mul : ∀ (a b : FKB) (ub_a : a.val < 256) (ub_b : b.val < 256), a.val * b.val ≤ 65025
    := by
      clear *-; intro a b ub_a ub_b
      nlinarith
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at *
    rw [Nat.mod_eq_of_lt (a := _ + _ * 256) (b := 2130706433) (by omega)] at *
    simp [*]; clear p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
                    ub_p0 ub_p1 ub_p2 ub_p3 ub_p4 ub_p5 ub_p6 ub_p7
                    ub_p8 ub_p9 ub_p10 ub_p11 ub_p12 ub_p13 ub_p14 ub_p15
    grind (splits := 16)

  /-- Pure / parametric gadget spec.

      Hypotheses: `MulGadget.AbsConstraints` on all column values, the
      gadget's `ext_asm` / `wf_asm` on `MulGadget.AbsBuses` (from which
      operand and result range bounds are derivable via the embedded
      `U16ToU8GadgetSafe` and product u8-pair byte-bus entries),
      `is_real = 1`, and the parent invariant
      `is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw`.

      No external range hypotheses on `a, b, c` — the byte-bus material
      lives inside `MulGadget.AbsBuses` itself, so the gadget derives
      those internally.

      Conclusion: `ALUBus.Spec opcode a b c` where `opcode` is
      selector-encoded. `ALUBus.Spec` for the MUL-family opcodes
      `{30, 31, 32, 33, 48}` already packages `result_range` (all four
      `a_i < 65536`) and `operand_range` (all four `b_i, c_i < 65536`)
      into the conclusion, so callers reading off ALU-bus consistency
      get the ranges for free — no separate range conjunct is needed.
      **Proof: `sorry`.** -/
  lemma gadget_spec
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
     b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
     c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
     b_msb c_msb product_msb
     b_sign_extend c_sign_extend : FKB)
    (h_gadget_constraints :
      MulGadget.AbsConstraints
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
        a_0 a_1 a_2 a_3
        b_0 b_1 b_2 b_3
        c_0 c_1 c_2 c_3
        carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
        carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
        product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
        product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
        b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
        c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
        b_msb c_msb product_msb
        b_sign_extend c_sign_extend)
    (h_gadget_ext_asm :
      bus_row_ext_asm
        (MulGadget.AbsBuses is_real is_mulw a_1
          b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
          carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
          carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
          product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
          product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
          b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
          c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
          b_msb c_msb product_msb))
    (h_gadget_wf_asm :
      bus_row_wf_asm
        (MulGadget.AbsBuses is_real is_mulw a_1
          b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
          carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
          carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
          product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
          product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
          b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
          c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
          b_msb c_msb product_msb))
    (h_is_real : is_real = 1)
    (h_real_eq_sum :
      is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw)
  :
    let opcode : FKB :=
      is_mul * 30 + is_mulh * 31 + is_mulhu * 32 + is_mulhsu * 33 + is_mulw * 48
    ALUBus.Spec opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
  := by
    -- ====================================================================
    -- COMMON SETUP — facts used by all five opcode branches.
    -- ====================================================================
    -- Call selector lemmas first (they consume `h_gadget_constraints`
    -- structurally, but we copy it for downstream use).
    have h_excl := MulGadget.Interpretations.selector_exclusivity
      is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
      a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
      carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
      carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
      product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
      product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
      b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
      c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
      b_msb c_msb product_msb b_sign_extend c_sign_extend
      h_gadget_constraints h_is_real h_real_eq_sum
    have h_breakdown := MulGadget.Interpretations.selector_breakdown
      is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
      a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
      carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
      carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
      product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
      product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
      b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
      c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
      b_msb c_msb product_msb b_sign_extend c_sign_extend
      h_gadget_constraints
    -- Decompose AbsConstraints into named conjuncts.
    -- AbsConstraints structure (in let-bound form for byte values):
    --   c0   : is_mulw bool
    --   c1   : product_msb bool
    --   c2   : b_sign_extend = (is_mulh + is_mulhsu) · b_msb
    --   c3   : c_sign_extend = is_mulh · c_msb
    --   c4..c19  : 16 polynomial-mult carry constraints
    --   c20..c31 : 12 result-selection constraints
    --   c32..c40 : 9 bool checks (b_msb, c_msb, b_sign_extend,
    --              c_sign_extend, is_mul/h/u/su/w)
    --   c41  : at-most-one (sum_of_selectors bool)
    --   c42  : is_real bool
    --   c43  : b_sign_extend = 1 ⇒ b_msb = 1
    --   c44  : c_sign_extend = 1 ⇒ c_msb = 1
    obtain ⟨c0, c1, c2, c3,
            p0, p1, p2, p3, p4, p5, p6, p7,
            p8, p9, p10, p11, p12, p13, p14, p15,
            a0_mulw, a0_mul, a0_mulh,
            a1_mulw, a1_mul, a1_mulh,
            a2_mulw, a2_mul, a2_mulh,
            a3_mulw, a3_mul, a3_mulh,
            b_msb_bool, c_msb_bool, b_se_bool, c_se_bool,
            is_mul_bool, is_mulh_bool, is_mulhu_bool, is_mulhsu_bool,
            is_mulw_bool, sum_bool, is_real_bool,
            b_se_msb, c_se_msb⟩ := h_gadget_constraints
    -- ====================================================================
    -- STEP 1: split `MulGadget.AbsBuses` into its three portions
    -- (U16ToU8 on b ‖ U16ToU8 on c ‖ chip-own remainder).
    -- ====================================================================
    rw [MulGadget.AbsBuses, bus_row_ext_asm_append, bus_row_ext_asm_append]
      at h_gadget_ext_asm
    rw [MulGadget.AbsBuses, bus_row_wf_asm_append, bus_row_wf_asm_append]
      at h_gadget_wf_asm
    obtain ⟨⟨h_b_ext, h_c_ext⟩, h_rest_ext⟩ := h_gadget_ext_asm
    obtain ⟨⟨h_b_wf, h_c_wf⟩, h_rest_wf⟩ := h_gadget_wf_asm
    -- ====================================================================
    -- STEP 2: invoke `U16ToU8GadgetSafe.Spec` for `b` and `c`.
    -- Each yields, per limb: `b_i.val < 65536`, low/high byte u8 bounds,
    -- and the canonical mod/div decomposition. Together these give
    -- `operand_range` for the ALU bus spec.
    -- ====================================================================
    have h_b_split := U16ToU8GadgetSafe.Spec.gadget_spec
      is_real b_0 b_1 b_2 b_3
      b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
      h_b_wf h_is_real
    have h_c_split := U16ToU8GadgetSafe.Spec.gadget_spec
      is_real c_0 c_1 c_2 c_3
      c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
      h_c_wf h_is_real
    -- Decompose the residual byte-bus portion (2 MSB lookups, 1
    -- `product_msb` consistency, 16 × u16 carry-range, 8 × u8-pair
    -- on product bytes) by unfolding `ByteBus.Spec`.
    simp [bus_row_wf_asm, h_is_real, ByteBus.Spec, and_assoc] at h_rest_wf
    -- ====================================================================
    -- STEP 3: lift the 16 carry-chain field equations to ℕ.
    -- ====================================================================
    -- Extract individual byte / carry / product bounds.
    -- From `h_b_split` (4 limbs, each yielding 5 facts:
    --   limb < 65536, low < 256, high < 256, low = limb % 256,
    --   high = limb / 256). We use only the byte bounds here.
    obtain ⟨⟨ub_b0, ub_blow0, ub_bhigh0, _, _⟩,
            ⟨ub_b1, ub_blow1, ub_bhigh1, _, _⟩,
            ⟨ub_b2, ub_blow2, ub_bhigh2, _, _⟩,
            ⟨ub_b3, ub_blow3, ub_bhigh3, _, _⟩⟩ := h_b_split
    obtain ⟨⟨ub_c0, ub_clow0, ub_chigh0, _, _⟩,
            ⟨ub_c1, ub_clow1, ub_chigh1, _, _⟩,
            ⟨ub_c2, ub_clow2, ub_chigh2, _, _⟩,
            ⟨ub_c3, ub_clow3, ub_chigh3, _, _⟩⟩ := h_c_split
    -- Sign-extend fill bytes are bounded: `b_sign_extend, c_sign_extend
    -- ∈ {0, 1}` (from `b_se_bool`, `c_se_bool`), so the corresponding
    -- byte expressions `b_sign_extend · 255`, `c_sign_extend · 255`
    -- have `.val < 256`.
    have h_bse_b : b_sign_extend = 0 ∨ b_sign_extend = 1 :=
      (mul_eq_zero.mp b_se_bool).imp id sub_eq_zero.mp
    have h_cse_b : c_sign_extend = 0 ∨ c_sign_extend = 1 :=
      (mul_eq_zero.mp c_se_bool).imp id sub_eq_zero.mp
    have ub_bse : (b_sign_extend * 255).val < 256 := by
      rcases h_bse_b with h | h <;> simp [h]
    have ub_cse : (c_sign_extend * 255).val < 256 := by
      rcases h_cse_b with h | h <;> simp [h]
    -- Carry u16-bounds and product u8-bounds from `h_rest_wf`. The bus
    -- entry order in `MulGadget.AbsBuses` is: 2 MSB byte lookups (b, c),
    -- 1 conditional U16MSBGadget entry (gated by `-is_mulw`), 16 ×
    -- U16Range on `carry_i`, 8 × U8Pair on `(product[2i], product[2i+1])`.
    -- After `simp [bus_row_wf_asm, h_is_real, ByteBus.Spec, and_assoc]`
    -- the entries split into a flat ∧-conjunction.
    obtain ⟨eq_bmsb, ub_bmsb, _ub_b3_top,
            eq_cmsb, ub_cmsb, _ub_c3_top,
            ub_a1_mulw,
            ub_cy0, ub_cy1, ub_cy2, ub_cy3, ub_cy4, ub_cy5, ub_cy6, ub_cy7,
            ub_cy8, ub_cy9, ub_cy10, ub_cy11, ub_cy12, ub_cy13, ub_cy14, ub_cy15,
            ub_pp0, ub_pp1, ub_pp2, ub_pp3, ub_pp4, ub_pp5, ub_pp6, ub_pp7,
            ub_pp8, ub_pp9, ub_pp10, ub_pp11, ub_pp12, ub_pp13, ub_pp14, ub_pp15
           ⟩ := h_rest_wf
    -- Lift the 16 FKB carry-chain equations to ℕ via `carry_chain_lift`.
    -- The byte placeholders are instantiated with the literal
    -- AbsConstraints byte expressions; Lean unifies them at elaboration.
    have h_chain_nat := carry_chain_lift
      is_real
      -- bb0..bb7, bbS
      b_lower_byte_0 ((b_0 - b_lower_byte_0) * 2122383361)
      b_lower_byte_1 ((b_1 - b_lower_byte_1) * 2122383361)
      b_lower_byte_2 ((b_2 - b_lower_byte_2) * 2122383361)
      b_lower_byte_3 ((b_3 - b_lower_byte_3) * 2122383361)
      (b_sign_extend * 255)
      -- cb0..cb7, cbS
      c_lower_byte_0 ((c_0 - c_lower_byte_0) * 2122383361)
      c_lower_byte_1 ((c_1 - c_lower_byte_1) * 2122383361)
      c_lower_byte_2 ((c_2 - c_lower_byte_2) * 2122383361)
      c_lower_byte_3 ((c_3 - c_lower_byte_3) * 2122383361)
      (c_sign_extend * 255)
      -- carries
      carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
      carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
      -- products
      product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
      product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
      -- 16 carry-chain FKB hypotheses
      p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
      h_is_real
      -- byte u8 bounds (low / high per limb, then sign-extend fill)
      ub_blow0 ub_bhigh0 ub_blow1 ub_bhigh1
      ub_blow2 ub_bhigh2 ub_blow3 ub_bhigh3 ub_bse
      ub_clow0 ub_chigh0 ub_clow1 ub_chigh1
      ub_clow2 ub_chigh2 ub_clow3 ub_chigh3 ub_cse
      -- carry u16 bounds (16)
      ub_cy0 ub_cy1 ub_cy2 ub_cy3 ub_cy4 ub_cy5 ub_cy6 ub_cy7
      ub_cy8 ub_cy9 ub_cy10 ub_cy11 ub_cy12 ub_cy13 ub_cy14 ub_cy15
      -- product u8 bounds (16)
      ub_pp0 ub_pp1 ub_pp2 ub_pp3 ub_pp4 ub_pp5 ub_pp6 ub_pp7
      ub_pp8 ub_pp9 ub_pp10 ub_pp11 ub_pp12 ub_pp13 ub_pp14 ub_pp15
    -- ====================================================================
    -- STEP 4: construct `bw`, `cw`, `prod` as `U128b`.
    -- Each byte is `BitVec.ofNat 8 fkb_byte.val`, which has
    -- `.toNat = fkb_byte.val` whenever `fkb_byte.val < 256`.
    -- ====================================================================
    -- Defining locally; not actually used yet since core_mul_64 below
    -- is sorry'd. Once step 3's `h_chain_nat` is filled in, these
    -- definitions feed into `core_mul_64`'s hypotheses.
    let bw : U128b := #v[
      BitVec.ofNat 8 b_lower_byte_0.val,
      BitVec.ofNat 8 ((b_0 - b_lower_byte_0) * 2122383361).val,
      BitVec.ofNat 8 b_lower_byte_1.val,
      BitVec.ofNat 8 ((b_1 - b_lower_byte_1) * 2122383361).val,
      BitVec.ofNat 8 b_lower_byte_2.val,
      BitVec.ofNat 8 ((b_2 - b_lower_byte_2) * 2122383361).val,
      BitVec.ofNat 8 b_lower_byte_3.val,
      BitVec.ofNat 8 ((b_3 - b_lower_byte_3) * 2122383361).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val,
      BitVec.ofNat 8 (b_sign_extend * 255).val ]
    let cw : U128b := #v[
      BitVec.ofNat 8 c_lower_byte_0.val,
      BitVec.ofNat 8 ((c_0 - c_lower_byte_0) * 2122383361).val,
      BitVec.ofNat 8 c_lower_byte_1.val,
      BitVec.ofNat 8 ((c_1 - c_lower_byte_1) * 2122383361).val,
      BitVec.ofNat 8 c_lower_byte_2.val,
      BitVec.ofNat 8 ((c_2 - c_lower_byte_2) * 2122383361).val,
      BitVec.ofNat 8 c_lower_byte_3.val,
      BitVec.ofNat 8 ((c_3 - c_lower_byte_3) * 2122383361).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val,
      BitVec.ofNat 8 (c_sign_extend * 255).val ]
    let prod : U128b := #v[
      BitVec.ofNat 8 product_0.val,  BitVec.ofNat 8 product_1.val,
      BitVec.ofNat 8 product_2.val,  BitVec.ofNat 8 product_3.val,
      BitVec.ofNat 8 product_4.val,  BitVec.ofNat 8 product_5.val,
      BitVec.ofNat 8 product_6.val,  BitVec.ofNat 8 product_7.val,
      BitVec.ofNat 8 product_8.val,  BitVec.ofNat 8 product_9.val,
      BitVec.ofNat 8 product_10.val, BitVec.ofNat 8 product_11.val,
      BitVec.ofNat 8 product_12.val, BitVec.ofNat 8 product_13.val,
      BitVec.ofNat 8 product_14.val, BitVec.ofNat 8 product_15.val ]
    -- ====================================================================
    -- STEP 5: apply `core_mul_64` to get the byte-level product identity.
    -- ====================================================================
    have h_core_mul :
      U128b.toBV prod = U128b.toBV bw * U128b.toBV cw
    := by
      -- Apply `core_mul_64` with the `U128b`s and the 16 carry values
      -- (as ℕ). This leaves 16 carry-chain goals, one per byte
      -- position; each goal has the shape
      --   `prod[i].toNat + cy_i * 256 = Σ_{j+k=i} bw[j].toNat * cw[k].toNat + cy_{i-1}`
      -- which after `simp` (unfolding the U128b literals + reducing
      -- `(BitVec.ofNat 8 v).toNat = v % 256 = v` via the bus bounds)
      -- matches the corresponding conjunct of `h_chain_nat`.
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7,
              h8, h9, h10, h11, h12, h13, h14, h15⟩ := h_chain_nat
      refine MulGadget.Spec.core_mul_64 bw cw prod
        carry_0.val carry_1.val carry_2.val carry_3.val
        carry_4.val carry_5.val carry_6.val carry_7.val
        carry_8.val carry_9.val carry_10.val carry_11.val
        carry_12.val carry_13.val carry_14.val carry_15.val
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      -- Common simp set for every conjunct: unfold the three U128b
      -- literals, reduce vector indexing, push `.toNat` inside
      -- `BitVec.ofNat`, replace `2 ^ 8` by `256`, and clear every
      -- `_ % 256` whose underlying `.val` is bounded by 256.
      all_goals (
        simp only [bw, cw, prod, Vector.getElem_mk,
                   List.getElem_toArray, List.getElem_cons_zero,
                   List.getElem_cons_succ, BitVec.toNat_ofNat,
                   show ((2:ℕ) ^ 8) = 256 from rfl,
                   Nat.mod_eq_of_lt ub_blow0, Nat.mod_eq_of_lt ub_bhigh0,
                   Nat.mod_eq_of_lt ub_blow1, Nat.mod_eq_of_lt ub_bhigh1,
                   Nat.mod_eq_of_lt ub_blow2, Nat.mod_eq_of_lt ub_bhigh2,
                   Nat.mod_eq_of_lt ub_blow3, Nat.mod_eq_of_lt ub_bhigh3,
                   Nat.mod_eq_of_lt ub_bse,
                   Nat.mod_eq_of_lt ub_clow0, Nat.mod_eq_of_lt ub_chigh0,
                   Nat.mod_eq_of_lt ub_clow1, Nat.mod_eq_of_lt ub_chigh1,
                   Nat.mod_eq_of_lt ub_clow2, Nat.mod_eq_of_lt ub_chigh2,
                   Nat.mod_eq_of_lt ub_clow3, Nat.mod_eq_of_lt ub_chigh3,
                   Nat.mod_eq_of_lt ub_cse,
                   Nat.mod_eq_of_lt ub_pp0, Nat.mod_eq_of_lt ub_pp1,
                   Nat.mod_eq_of_lt ub_pp2, Nat.mod_eq_of_lt ub_pp3,
                   Nat.mod_eq_of_lt ub_pp4, Nat.mod_eq_of_lt ub_pp5,
                   Nat.mod_eq_of_lt ub_pp6, Nat.mod_eq_of_lt ub_pp7,
                   Nat.mod_eq_of_lt ub_pp8, Nat.mod_eq_of_lt ub_pp9,
                   Nat.mod_eq_of_lt ub_pp10, Nat.mod_eq_of_lt ub_pp11,
                   Nat.mod_eq_of_lt ub_pp12, Nat.mod_eq_of_lt ub_pp13,
                   Nat.mod_eq_of_lt ub_pp14, Nat.mod_eq_of_lt ub_pp15])
      exacts [h0, h1, h2, h3, h4, h5, h6, h7,
              h8, h9, h10, h11, h12, h13, h14, h15]
    -- ====================================================================
    -- Cleanup after Steps 3-5. Drop hypotheses that are fully consumed
    -- by `carry_chain_lift` and `core_mul_64`, plus a few redundant
    -- ones (`_ub_b3_top` ≡ `ub_bhigh3`, `ub_bmsb` is trivial since
    -- `b_msb ∈ {0,1}`, `c0` ≡ `is_mulw_bool`). What remains in scope
    -- for Steps 6-7 is the byte-product identity `h_core_mul`, all
    -- byte / limb u8 / u16 bounds, the sign / msb / result-selection
    -- constraints, and the selector breakdown + exclusivity lemmas.
    -- ====================================================================
    clear -- 16 raw FKB carry-chain equations (subsumed by `h_core_mul`)
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
          -- ℕ-lifted chain (consumed by `core_mul_64`)
          h_chain_nat
          -- 16 carry u16 bounds (only used during the lift)
          ub_cy0 ub_cy1 ub_cy2 ub_cy3 ub_cy4 ub_cy5 ub_cy6 ub_cy7
          ub_cy8 ub_cy9 ub_cy10 ub_cy11 ub_cy12 ub_cy13 ub_cy14 ub_cy15
          -- redundant top-byte / b_msb / c_msb bounds
          _ub_b3_top _ub_c3_top ub_bmsb ub_cmsb
          -- bus residuals not needed downstream
          h_b_ext h_c_ext h_b_wf h_c_wf h_rest_ext
          -- bool checks subsumed by `h_breakdown` / `h_bse_b` / `h_cse_b`
          c0
          is_mul_bool is_mulh_bool is_mulhu_bool is_mulhsu_bool is_mulw_bool
          sum_bool is_real_bool b_se_bool c_se_bool
    -- ====================================================================
    -- Universal sign-extension bridge (parametric in `b_sign_extend` /
    -- `c_sign_extend`).
    --
    -- The 16-byte `bw` literal we built in Step 4 has its low 8 bytes
    -- as the byte-view of `b` (low / high byte of each u16 limb) and
    -- its upper 8 bytes filled with `b_sign_extend * 255` (= 0 if
    -- `b_sign_extend = 0`, = 255 if `b_sign_extend = 1`). That is
    -- *definitionally* `U64b.extend`'s shape with the sign bit
    -- `!(b_sign_extend = 0)`:
    --
    --   • `b_sign_extend = 0` → upper bytes all 0 → zero-extend
    --   • `b_sign_extend = 1` → upper bytes all 255 → sign-extend, but
    --     `b_se_msb : b_sign_extend = 1 → b_msb = 1` forces `b` to be
    --     negative (via `eq_bmsb`), matching `U64b.ext`'s definition.
    --
    -- Proving this once here means each opcode branch can immediately
    -- rewrite `bw` (resp. `cw`) to a clean `U64b.extend` expression,
    -- and then use `U64b.extend_BitVec_extend` to fold it into a
    -- `BitVec.extend _ 128 with_sign` on `b`'s BitVec view. The same
    -- bridge serves the unsigned cases (MUL, MULHU, MULW — where the
    -- selector forces `b_sign_extend = 0`) and the signed cases (MULH,
    -- MULHSU — where `b_sign_extend = b_msb`).
    -- ====================================================================
    have eq_bw : bw = (U64w.toU64b #v[b_0, b_1, b_2, b_3]).extend !decide (b_sign_extend = 0)
    := by
      replace eq_bmsb : b_msb = if b_3.val / 256 < 128 then 0 else 1
        := by simp [eq_bmsb]; congr 1; simp [Fin.lt_def, *]
      subst bw; simp [*]
      clear *- ub_b0 ub_b1 ub_b2 ub_b3 h_bse_b ub_bse eq_bmsb b_se_msb
      simp [U64w.toU64b, U64b.extend]
      obtain h_bse | h_bse := h_bse_b <;> simp [*, U64b.ext, ← BitVec.toNat_inj]
      . omega
      . rw [if_pos]
        . omega
        . simp [← U64b.msb_7_negative, BitVec.msb_eq_decide]
          simp_all [sub_eq_zero]
          omega
    have eq_cw : cw = (U64w.toU64b #v[c_0, c_1, c_2, c_3]).extend !decide (c_sign_extend = 0)
    := by
      replace eq_cmsb : c_msb = if c_3.val / 256 < 128 then 0 else 1
        := by simp [eq_cmsb]; congr 1; simp [Fin.lt_def, *]
      subst cw; simp [*]
      clear *- ub_c0 ub_c1 ub_c2 ub_c3 h_cse_b ub_cse eq_cmsb c_se_msb
      simp [U64w.toU64b, U64b.extend]
      obtain h_cse | h_cse := h_cse_b <;> simp [*, U64b.ext, ← BitVec.toNat_inj]
      . omega
      . rw [if_pos]
        . omega
        . simp [← U64b.msb_7_negative, BitVec.msb_eq_decide]
          simp_all [sub_eq_zero]
          omega
    -- ====================================================================
    -- STEPS 6+7: per-opcode case-split. We branch via `by_cases` on
    -- each of `is_mul, is_mulh, is_mulhu, is_mulhsu = 1` in turn. In
    -- each positive branch the four other selectors are pinned to `0`
    -- by `h_excl`; in the final (all-negated) branch the remaining
    -- selector `is_mulw` is forced to `1` by `h_real_eq_sum + h_is_real`.
    -- Each branch then:
    --   • simplifies the encoded `opcode` to its literal value (30 /
    --     31 / 32 / 33 / 48),
    --   • derives `b_sign_extend` and `c_sign_extend` from `c2` / `c3`
    --     using the now-known selector values,
    --   • bridges `U128b.toBV bw / cw` to `(s|z)ext128 (U64w.toBV b)`
    --     / `(s|z)ext128 (U64w.toBV c)`,
    --   • extracts the correct 64-bit window of `U128b.toBV prod` and
    --     matches it against the corresponding `execute_*_pure`.
    -- ====================================================================
    -- Unfold the selector-encoded opcode to expose the arithmetic
    -- expression to `by_cases` substitutions.
    show ALUBus.Spec
           (is_mul * 30 + is_mulh * 31 + is_mulhu * 32 + is_mulhsu * 33
            + is_mulw * 48)
           a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
    -- Project `h_excl` into its five per-opcode exclusivity implications.
    have h_mul_excl    := h_excl.1
    have h_mulh_excl   := h_excl.2.1
    have h_mulhu_excl  := h_excl.2.2.1
    have h_mulhsu_excl := h_excl.2.2.2.1
    have h_mulw_excl   := h_excl.2.2.2.2
    by_cases h_mul : is_mul = 1
    . -- MUL case (opcode = 30). Other selectors pinned to 0.
      obtain ⟨h_mulh_0, h_mulhu_0, h_mulhsu_0, h_mulw_0⟩ := h_mul_excl h_mul
      -- From `c2 : b_se - (is_mulh + is_mulhsu) * b_msb = 0`, with
      -- `is_mulh = is_mulhsu = 0` we get `b_sign_extend = 0`.
      -- From `c3 : c_se - is_mulh * c_msb = 0`, with `is_mulh = 0` we get
      -- `c_sign_extend = 0`. So MUL is fully *unsigned* — the upper 8
      -- bytes of `bw, cw` are all `0`, and `U128b.toBV bw = zext128 b`,
      -- `U128b.toBV cw = zext128 c`. The result is the low 64 bits.
      have h_bse : b_sign_extend = 0 := by
        rw [h_mulh_0, h_mulhsu_0] at c2
        linear_combination c2
      have h_cse : c_sign_extend = 0 := by
        rw [h_mulh_0] at c3
        linear_combination c3
      subst bw cw
            is_mul is_mulh is_mulhu is_mulhsu is_mulw
            b_sign_extend c_sign_extend
      simp [sub_eq_zero] at *
      subst a_0 a_1 a_2 a_3
      simp [ALUBus.Spec, ALUBus.operandRange]
      constructor
      . clear *- ub_pp0 ub_pp1 ub_pp2 ub_pp3 ub_pp4 ub_pp5 ub_pp6 ub_pp7
        grind
      . constructor
        . clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
          grind
        . simp_all [execute_MUL_pure]
          trans (BitVec.extractLsb 63 0 prod.toBV)
          . subst prod; simp
            repeat rw [bv16_from_bytes _ _ (by assumption) (by assumption)]
            simp [U64w.toBV, U64b.toBV]
            repeat rw [BitVec.append_assoc]
            rfl
          . simp [h_core_mul, U64w.extend_BitVec_extend]
    . -- Not MUL: pin `is_mul = 0` from `h_breakdown`.
      have h_mul_0 : is_mul = 0 := h_breakdown.1.resolve_right h_mul
      by_cases h_mulh : is_mulh = 1
      . -- MULH case (opcode = 31). Signed × signed, high 64 bits.
        obtain ⟨_h_mul_0', h_mulhu_0, h_mulhsu_0, h_mulw_0⟩ := h_mulh_excl h_mulh
        replace eq_bmsb : b_msb = if (b_3.val < 32768) then 0 else 1
        := by
          rw [eq_bmsb]
          rw [show b_3.val = b_3.val % 256 + (b_3.val / 256) * 256 by clear *- ub_b3; grind]
          simp [Fin.lt_def, *]; clear *- ub_b3
          grind
        replace eq_cmsb : c_msb = if (c_3.val < 32768) then 0 else 1
        := by
          rw [eq_cmsb]
          rw [show c_3.val = c_3.val % 256 + (c_3.val / 256) * 256 by clear *- ub_c3; grind]
          simp [Fin.lt_def, *]; clear *- ub_c3
          grind
        subst is_mulh is_mulhsu b_msb c_msb; simp [sub_eq_zero] at *
        replace eq_bw : bw = (U64w.toU64b #v[BitVec.ofNat 16 ↑b_0, BitVec.ofNat 16 ↑b_1, BitVec.ofNat 16 ↑b_2, BitVec.ofNat 16 ↑b_3]).extend true
        := by
          simp [eq_bw]
          split_ifs at c2 with h_if <;> simp [c2]
          . simp [U64b.extend, U64b.ext]
            simp [← U64b.msb_7_negative, BitVec.msb_eq_decide]
            simp [U64w.toU64b]
            clear *- h_if
            omega
        replace eq_cw : cw = (U64w.toU64b #v[BitVec.ofNat 16 ↑c_0, BitVec.ofNat 16 ↑c_1, BitVec.ofNat 16 ↑c_2, BitVec.ofNat 16 ↑c_3]).extend true
        := by
          simp [eq_cw]
          split_ifs at c3 with h_if <;> simp [c3]
          . simp [U64b.extend, U64b.ext]
            simp [← U64b.msb_7_negative, BitVec.msb_eq_decide]
            simp [U64w.toU64b]
            clear *- h_if
            omega
        simp [eq_bw, eq_cw] at h_core_mul
        subst is_mul is_mulhu is_mulw
        simp at *
        subst a_0 a_1 a_2 a_3
        simp [ALUBus.Spec, ALUBus.operandRange]
        constructor
        . clear *- ub_pp8 ub_pp9 ub_pp10 ub_pp11 ub_pp12 ub_pp13 ub_pp14 ub_pp15
          grind
        . constructor
          . clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
            grind
          . trans (BitVec.extractLsb 127 64 prod.toBV)
            . subst prod; simp
              repeat rw [bv16_from_bytes _ _ (by assumption) (by assumption)]
              simp [U64w.toBV, U64b.toBV]
              repeat rw [BitVec.append_assoc]
              rfl
            . simp [h_core_mul, execute_MUL_pure, U64w.extend_BitVec_extend]
      . have h_mulh_0 : is_mulh = 0 := h_breakdown.2.1.resolve_right h_mulh
        by_cases h_mulhu : is_mulhu = 1
        . -- MULHU case (opcode = 32). Unsigned × unsigned, high 64 bits.
          obtain ⟨_h_mul_0', _h_mulh_0', h_mulhsu_0, h_mulw_0⟩ := h_mulhu_excl h_mulhu
          -- Like MUL: both b_sign_extend and c_sign_extend are 0 because
          -- `is_mulh = is_mulhsu = 0`. The only difference is the
          -- extract window: MULHU is the high 64 bits of `b · c`.
          have h_bse : b_sign_extend = 0 := by
            rw [h_mulh_0, h_mulhsu_0] at c2
            linear_combination c2
          have h_cse : c_sign_extend = 0 := by
            rw [h_mulh_0] at c3
            linear_combination c3
          subst bw cw
                is_mul is_mulh is_mulhu is_mulhsu is_mulw
                b_sign_extend c_sign_extend
          simp [sub_eq_zero] at *
          subst a_0 a_1 a_2 a_3
          simp [ALUBus.Spec, ALUBus.operandRange]
          constructor
          . clear *- ub_pp8 ub_pp9 ub_pp10 ub_pp11 ub_pp12 ub_pp13 ub_pp14 ub_pp15
            grind
          . constructor
            . clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
              grind
            . simp_all [execute_MUL_pure]
              trans (BitVec.extractLsb 127 64 prod.toBV)
              . subst prod; simp
                repeat rw [bv16_from_bytes _ _ (by assumption) (by assumption)]
                simp [U64w.toBV, U64b.toBV]
                repeat rw [BitVec.append_assoc]
                rfl
              . simp [h_core_mul, U64w.extend_BitVec_extend]
        . have h_mulhu_0 : is_mulhu = 0 := h_breakdown.2.2.1.resolve_right h_mulhu
          by_cases h_mulhsu : is_mulhsu = 1
          . -- MULHSU case (opcode = 33). Signed × unsigned, high 64 bits.
            -- Hybrid of MULH (signed b → `eq_bw` with `.extend true`) and
            -- MULHU (unsigned c → substitute `c_sign_extend = 0` directly).
            obtain ⟨_h_mul_0', _h_mulh_0', _h_mulhu_0', h_mulw_0⟩ :=
              h_mulhsu_excl h_mulhsu
            replace eq_bmsb : b_msb = if (b_3.val < 32768) then 0 else 1
            := by
              rw [eq_bmsb]
              rw [show b_3.val = b_3.val % 256 + (b_3.val / 256) * 256
                  by clear *- ub_b3; grind]
              simp [Fin.lt_def, *]; clear *- ub_b3
              grind
            -- `c_sign_extend = 0` follows from `c3` once `is_mulh = 0`.
            have h_cse : c_sign_extend = 0 := by
              rw [h_mulh_0] at c3
              linear_combination c3
            subst is_mulh is_mulhsu b_msb c_sign_extend
            simp [sub_eq_zero] at *
            replace eq_bw : bw = (U64w.toU64b
                #v[BitVec.ofNat 16 ↑b_0, BitVec.ofNat 16 ↑b_1,
                   BitVec.ofNat 16 ↑b_2, BitVec.ofNat 16 ↑b_3]).extend true
            := by
              simp [eq_bw]
              split_ifs at c2 with h_if <;> simp [c2]
              . simp [U64b.extend, U64b.ext]
                simp [← U64b.msb_7_negative, BitVec.msb_eq_decide]
                simp [U64w.toU64b]
                clear *- h_if
                omega
            simp [eq_bw, eq_cw] at h_core_mul
            subst is_mul is_mulhu is_mulw
            simp at *
            subst a_0 a_1 a_2 a_3
            simp [ALUBus.Spec, ALUBus.operandRange]
            constructor
            . clear *- ub_pp8 ub_pp9 ub_pp10 ub_pp11 ub_pp12 ub_pp13 ub_pp14 ub_pp15
              grind
            . constructor
              . clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
                grind
              . trans (BitVec.extractLsb 127 64 prod.toBV)
                . subst prod; simp
                  repeat rw [bv16_from_bytes _ _ (by assumption) (by assumption)]
                  simp [U64w.toBV, U64b.toBV]
                  repeat rw [BitVec.append_assoc]
                  rfl
                . simp [h_core_mul, execute_MUL_pure, U64w.extend_BitVec_extend]
          . have h_mulhsu_0 : is_mulhsu = 0 := h_breakdown.2.2.2.1.resolve_right h_mulhsu
            -- Remaining case: must be MULW (opcode = 48). From
            -- `h_is_real = 1` and `h_real_eq_sum`, with the four other
            -- selectors `= 0`, we get `is_mulw = 1`.
            have h_mulw : is_mulw = 1 := by
              have h_sum := h_real_eq_sum
              rw [h_is_real, h_mul_0, h_mulh_0, h_mulhu_0, h_mulhsu_0]
                at h_sum
              linear_combination -h_sum
            -- MULW (opcode = 48). The spec computes the 32-bit signed
            -- product `b.setWidth 32 ·ₛ c.setWidth 32 : BitVec 32` and
            -- sign-extends it back to 64 bits. The chip's witnesses
            -- describe the same value, but the path is different:
            --
            --   • The 128-bit `prod` is computed *unsigned* — both
            --     `b_sign_extend` and `c_sign_extend` are forced to 0
            --     (since `is_mulh = is_mulhsu = 0` in `c2` / `c3`), so
            --     the upper 8 bytes of `bw` and `cw` are zero and
            --     `prod.toBV = (zext128 b) * (zext128 c)`.
            --
            --   • The result limbs come from two different sources:
            --       — `a_0 = product_0 + product_1·256` and
            --         `a_1 = product_2 + product_3·256` — the *low 32
            --         bits* of `prod` (bytes 0..3);
            --       — `a_2 = a_3 = product_msb · 65535` — the 16-bit
            --         "all-zeros or all-ones" sign-extension fill,
            --         where `product_msb ∈ {0,1}` is forced by the
            --         U16MSBGadget consistency check `ub_a1_mulw` to
            --         be the top bit of `a_1` (hence the top bit of
            --         the low-32 product).
            --
            -- The mismatch between *unsigned 128-bit* (chip) and
            -- *signed 32-bit* (spec) is resolved by the fact that
            -- signedness vanishes modulo `2 ^ 32`: multiplication on
            -- BitVecs is congruence-preserving, so
            --   `(b_unsigned · c_unsigned).setWidth 32`
            -- and
            --   `BitVec.ofInt 32 (b_signed.toInt · c_signed.toInt)`
            -- coincide. The bridge below makes this explicit.
            have h_bse : b_sign_extend = 0 := by
              rw [h_mulh_0, h_mulhsu_0] at c2
              linear_combination c2
            have h_cse : c_sign_extend = 0 := by
              rw [h_mulh_0] at c3
              linear_combination c3
            subst bw cw
                  is_mul is_mulh is_mulhu is_mulhsu is_mulw
                  b_sign_extend c_sign_extend
            rw [eq_bw, eq_cw] at h_core_mul; clear eq_bw eq_cw
            simp [sub_eq_zero] at *
            subst a_0 a_1 a_2 a_3
            simp [ALUBus.Spec, ALUBus.operandRange]
            constructor
            . -- result_range: low 32 bits via `pp_0..pp_3`, upper 32
              -- bits via `product_msb ∈ {0,1}` (from `c1`).
              clear *- ub_pp0 ub_pp1 ub_pp2 ub_pp3 c1
              grind
            . constructor
              . clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
                grind
              . -- Bridge plan: factor the equality through the
                -- half-way point `(U32w.extend prod_low_32 true).toBV`,
                -- which simultaneously captures
                --   (a) the chip-side fill: `a_2 = a_3 = product_msb · 65535`
                --       are exactly `U32w.extend true`'s sign-extension bytes;
                --   (b) the spec-side fill: `sign_extend (result32) 64`
                --       is the same form via `U32w.extend_BitVec_extend`.
                --
                -- Step 0 (this line): reshape the spec's
                -- `BitVec.setWidth 32` on `b` / `c` into the u16-limb
                -- pair `U32w.toBV #v[b_0, b_1]` (resp. `c`) so the
                -- proof speaks exclusively in chip-native u16 limbs.
                trans ((U32w.extend #v[BitVec.ofNat 16 ↑(product_0 + product_1 * 256), BitVec.ofNat 16 ↑(product_2 + product_3 * 256)]) true).toBV
                . -- Chip side: rewrite the chip's 4-limb output
                  --   `U64w.toBV #v[low_0, low_1, msb·65535, msb·65535]`
                  -- as `(U32w.extend #v[low_0, low_1] true).toBV`. The
                  -- low limbs match literally; the only non-trivial
                  -- step is identifying `product_msb · 65535` with the
                  -- `0`-or-`0xFFFF` fill that `U32w.ext true` emits.
                  -- The condition is exactly "the top bit of the
                  -- low-32 result is `1`", which by `ub_a1_mulw` (the
                  -- U16MSBGadget consistency check) coincides with
                  -- `product_msb = 1`.
                  simp [U32w.extend, U32w.ext, ← U32w.msb_1_negative, BitVec.msb_eq_decide]
                  suffices h_prod_msb_fill : BitVec.ofNat 16 (product_msb * 65535).val = if 32768 ≤ (product_2 + product_3 * 256).val % 65536 then 65535#16 else 0#16
                  . simp [h_prod_msb_fill]
                  . -- Case-split on `product_msb ∈ {0, 1}` (from `c1`);
                    -- in each branch `ub_a1_mulw` pins the top-bit
                    -- condition of `a_1 = product_2 + product_3 · 256`.
                    simp [← BitVec.toNat_inj]
                    clear *- ub_a1_mulw ub_pp2 ub_pp3 c1
                    obtain c1 | c1 := c1 <;> simp [c1] at ub_a1_mulw ⊢
                    . split_ifs with h_if <;> simp [Fin.val_add, Fin.val_mul] at *
                      rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)] at ub_a1_mulw h_if
                      grind
                    . split_ifs with h_if <;> simp [Fin.val_add, Fin.val_mul] at *
                      rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)] at h_if
                      grind
                . -- Spec side: `(U32w.extend prod_low_32 true).toBV`
                  --             = `execute_MULW_pure (b.setWidth 32) (c.setWidth 32)`.
                  -- After `U32w.extend_BitVec_extend` both sides reduce
                  -- to `(?_ : BitVec 32).signExtend 64`; the residual
                  -- content is *the signed 32-bit product equals the
                  -- unsigned 32-bit product mod `2 ^ 32`*. We prove
                  -- this via `h_low_32_prod` by lifting `h_core_mul`
                  -- (the 128-bit unsigned product identity from Step 5)
                  -- to ℕ and reducing both sides modulo `2 ^ 32`.
                  simp [U32w.extend_BitVec_extend, BitVec.extend]
                  simp [execute_MULW_pure]
                  suffices h_low_32_prod :
                    (U32w.toBV #v[BitVec.ofNat 16 ↑(product_0 + product_1 * 256), BitVec.ofNat 16 ↑(product_2 + product_3 * 256)]) =
                    (U32w.toBV #v[BitVec.ofNat 16 ↑b_0, BitVec.ofNat 16 ↑b_1] * U32w.toBV #v[BitVec.ofNat 16 ↑c_0, BitVec.ofNat 16 ↑c_1])
                  . simp [h_low_32_prod]
                  . -- Open `h_core_mul` at the `.toNat` level, clear the
                    -- `% 256` mods on every prod / b / c byte using the
                    -- u8 bounds, re-aggregate at u16-limb level, and
                    -- close mod `KB_prime` / `2 ^ 16` with `omega`.
                    subst prod
                    clear *- ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
                             ub_pp0 ub_pp1 ub_pp2 ub_pp3 ub_pp4 ub_pp5 ub_pp6 ub_pp7
                             ub_pp8 ub_pp9 ub_pp10 ub_pp11 ub_pp12 ub_pp13 ub_pp14 ub_pp15
                             h_core_mul
                    simp [← BitVec.toNat_inj] at h_core_mul ⊢
                    simp [U128b.toNat, U64w.toNat] at h_core_mul
                    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at h_core_mul
                    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)] at h_core_mul
                    ring_nf at h_core_mul
                    simp [U32w.toNat, Fin.val_add, Fin.val_mul]
                    repeat rw [Nat.mod_eq_of_lt (b := KB_prime) (by omega)]
                    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
                    ring_nf
                    omega

end MulGadget.Spec
