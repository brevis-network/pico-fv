import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# IsZeroGadget (64-bit)

Lean formalisation of `IsZeroGadget` from
`vm/src/chips/gadgets/is_zero.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct IsZeroGadget<T> {
    pub inverse: T,
    pub result: T,
}
```

The gadget itself owns 2 columns (`inverse`, `result`). Its `eval` semantics
(per row, gated by an `is_real` expression supplied by the parent) are:

- `result = 1 - inverse * input`
- `result * (result - 1) = 0`   (boolean)
- `result * input = 0`          (forces `result = 0` when `input ≠ 0`)

The standalone Lean extraction wraps this with the input value and an
`is_real` column for testing in isolation; the wrapped Air therefore has 4
columns total.

## Wrapped extraction column layout (4 columns total)

| Group   | Columns          | Count |
|---------|------------------|-------|
| Input   | input            | 1     |
| Gadget  | inverse, result  | 2     |
| Control | is_real          | 1     |
-/

-- ============================================================================
-- IsZeroGadget — gadget-only column struct (matches the Rust struct).
-- This is meant to be embedded in parent chips via SubAir.
-- ============================================================================

#define_subair "IsZeroGadget" using "pico_encapsulation" where
  Column["inverse"]
  Column["result"]

-- ============================================================================
-- IsZeroGadgetExtractionCols — the wrapped form used by the standalone Air
-- extraction (input + gadget + is_real).
-- ============================================================================

#define_subair "IsZeroGadgetExtractionCols" using "pico_encapsulation" where
  Column["input"]
  SubAir["gadget": "IsZeroGadget" width := 2]
  Column["is_real"]

-- ============================================================================
-- Air definition (wraps the extraction)
-- ============================================================================

#define_air "IsZeroGadgetAir" using "pico_encapsulation" where
  MainSubAir["cols": "IsZeroGadgetExtractionCols" width := 4]
