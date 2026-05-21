import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# U16MSBGadget (64-bit)

Lean formalisation of `U16MSBGadget` from
`vm/src/chips/gadgets/msb.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct U16MSBGadget<T> {
    pub msb: T,
}
```

Single-column gadget that captures the most significant bit of a u16 value.
The parent supplies the source u16 expression and gates evaluation through
`is_real`; this struct stores only the boolean MSB witness.
-/

-- ============================================================================
-- U16MSBGadget — gadget-only column struct
-- ============================================================================

#define_subair "U16MSBGadget" using "pico_encapsulation" where
  Column["msb"]
