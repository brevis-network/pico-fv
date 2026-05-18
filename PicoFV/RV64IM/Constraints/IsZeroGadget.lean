import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.IsZeroGadget
import PicoFV.RV64IM.Airs.IsZeroGadget

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# IsZeroGadget — abstract constraints & buses

`IsZeroGadget`'s Pico Rust source is `vm/src/chips/gadgets/is_zero.rs`
at commit `22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. Smallest gadget
in the codebase: 2 owned columns (`inverse`, `result`) plus the
externally-supplied `input` and `is_real` selector.

The standard "multiplicative inverse" trick for zero-testing in
arithmetic circuits:

- `result = 1 - inverse · input`   forces `result = 1` when `input = 0`
  (any `inverse` works, prover picks `0`).
- `result · (result - 1) = 0`      forces `result ∈ {0, 1}`. Combined
  with the previous, when `input ≠ 0` and the prover picks the right
  `inverse = input⁻¹`, the product is `1`, so `result = 0`.
- `result · input = 0`             closes the soundness gap: if the
  prover gave a *wrong* `inverse` when `input ≠ 0`, `result` could land
  on `1` via the first equation, but this constraint would then force
  `input = 0` (a contradiction with `input ≠ 0`).

All three constraints are gated by `is_real` — when the row is
inactive (`is_real = 0`), every constraint is trivially satisfied. The
gadget does *not* enforce `is_real ∈ {0, 1}` itself; that's the
parent's responsibility (`IsZeroWordGadget` enforces it, for
instance).

## Algebraic constraints (3, all gated by `is_real`)

| # | Form                                              | Purpose                      |
|---|---------------------------------------------------|------------------------------|
| 0 | `is_real · ((1 - inverse · input) - result) = 0`  | defines `result`             |
| 1 | `is_real · result · (result - 1) = 0`             | `result ∈ {0, 1}` when real  |
| 2 | `is_real · result · input = 0`                    | `result = 1 ⇒ input = 0`     |

The gadget contributes *no* bus entries — `AbsBuses` is the empty
`BusRow`.

This file therefore provides only the *parametric* `AbsConstraints`
and (empty) `AbsBuses` predicates; there is no standalone wrapping Air
to identify against beyond the bare `IsZeroGadgetAir`.
-/

namespace IsZeroGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `IsZeroGadget`
      asserts on a row, expressed parametrically in the 2 column
      values it owns plus the parent-supplied `input` and `is_real`.
      All three are gated by `is_real`. -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real input inverse result : F)
  : Prop :=
    (is_real * ((1 - inverse * input) - result) = 0) ∧
    (is_real * (result * (result - 1)) = 0) ∧
    (is_real * (result * input) = 0)

  /-- The Pico `IsZeroGadget` contributes no bus entries. -/
  def AbsBuses
    (_is_real _input _inverse _result : FKB)
  : BusRow :=
    {
      Program := [],
      ALU := [],
      Byte := [],
      State := [],
      Memory := []
    }

end IsZeroGadget
