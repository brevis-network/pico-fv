import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# LtUnsignedGadget (64-bit)

Lean formalisation of `LtUnsignedGadget` from
`vm/src/chips/gadgets/lt_unsigned.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct LtUnsignedGadget<T> {
    /// Boolean flags to indicate the first byte in which the remainder is smaller than c.
    pub byte_flags: [T; WORD_SIZE],   // WORD_SIZE = 4

    /// The comparison byte for a (remainder).
    pub a_comparison_byte: T,

    /// The comparison byte for b (c).
    pub b_comparison_byte: T,
}
```

Layout: 4 + 1 + 1 = 6 columns total.
-/

-- ============================================================================
-- LtUnsignedGadget — gadget-only column struct (6 columns)
-- ============================================================================

#define_subair "LtUnsignedGadget" using "pico_encapsulation" where
  Column["byte_flags_0"]
  Column["byte_flags_1"]
  Column["byte_flags_2"]
  Column["byte_flags_3"]
  Column["a_comparison_byte"]
  Column["b_comparison_byte"]
