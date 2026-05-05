import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# U16ToU8Gadget (64-bit)

Lean formalisation of `U16ToU8Gadget` from
`vm/src/chips/gadgets/u16_to_u8.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct U16ToU8Gadget<T> {
    pub low_bytes: [T; WORD_SIZE],   // WORD_SIZE = 4
}
```

Stores the low byte of each of a Word's four u16 limbs (4 bytes total). The
high bytes are reconstructed inline from the parent as
`(limb_i - low_bytes_i) * inv(256)`, with the byte bus enforcing both halves
are valid 8-bit values.
-/

-- ============================================================================
-- U16ToU8Gadget — gadget-only column struct (4 columns)
-- ============================================================================

#define_subair "U16ToU8Gadget" using "pico_encapsulation" where
  Column["low_bytes_0"]
  Column["low_bytes_1"]
  Column["low_bytes_2"]
  Column["low_bytes_3"]
