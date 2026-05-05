import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# AddGadget (64-bit)

Lean formalisation of `AddGadget` from
`vm/src/chips/gadgets/add.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct AddGadget<T> {
    /// The result of `a + b`.
    pub value: Word<T>,
}
```

`Word<T>` is `[T; 4]` (four 16-bit limbs forming a 64-bit value). The gadget
itself owns only the result word; per-limb carries are reconstructed lazily
in the `eval` body and pinned to {0, 1} via a single boolean check per limb.

The standalone Lean extraction wraps this with input operands `b`, `c`, and
an `is_real` column for testing in isolation; the wrapped Air therefore has
13 columns total (4 + 4 + 4 + 1).
-/

-- ============================================================================
-- AddGadget — gadget-only column struct (4 columns: value: Word)
-- ============================================================================

#define_subair "AddGadget" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  Column["value_2"]
  Column["value_3"]

-- ============================================================================
-- AddGadgetExtractionCols — wrapped form for the standalone Air extraction
-- ============================================================================

#define_subair "AddGadgetExtractionCols" using "pico_encapsulation" where
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  SubAir["gadget": "AddGadget" width := 4]
  Column["is_real"]

-- ============================================================================
-- Air definition (wraps the extraction)
-- ============================================================================

#define_air "AddGadgetAir" using "pico_encapsulation" where
  MainSubAir["cols": "AddGadgetExtractionCols" width := 13]
