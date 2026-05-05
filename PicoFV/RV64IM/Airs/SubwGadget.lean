import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# SubwGadget (64-bit)

Lean formalisation of `SubwGadget` from
`vm/src/chips/gadgets/subw.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct SubwGadget<T> {
    /// The result of the SUBW gadget.
    pub value: [T; WORD_SIZE / 2],   // [T; 2]

    /// The msb of the result.
    pub msb: U16MSBGadget<T>,
}
```

Same shape as `AddwGadget`: layout is 2 + 1 = 3 columns total.
-/

-- ============================================================================
-- SubwGadget — gadget-only column struct (3 columns)
-- ============================================================================

#define_subair "SubwGadget" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  SubAir["msb": "U16MSBGadget" width := 1]
