import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# SubGadget (64-bit)

Lean formalisation of `SubGadget` from
`vm/src/chips/gadgets/sub.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct SubGadget<T> {
    /// The result of `a - b`.
    pub value: Word<T>,
}
```

Same shape as `AddGadget` (4-limb result word). Per-limb borrows are
reconstructed lazily in `eval` and pinned to {0, 1} via a single boolean
check per limb.
-/

-- ============================================================================
-- SubGadget — gadget-only column struct (4 columns: value: Word)
-- ============================================================================

#define_subair "SubGadget" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  Column["value_2"]
  Column["value_3"]
