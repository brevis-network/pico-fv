import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# LtWordU16Gadget (64-bit)

Lean formalisation of `LtWordU16Gadget` from
`vm/src/chips/gadgets/lt_word_u16.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct LtWordU16Gadget<T> {
    /// Boolean flags indicating which limb pair is the most-significant differing one.
    pub u16_flags: [T; WORD_SIZE],          // WORD_SIZE = 4

    /// The inverse of (a_limb - b_limb) at the differing position.
    pub not_eq_inv: T,

    /// The two u16 limbs being compared (from the first differing position).
    pub comparison_limbs: [T; 2],

    /// The LT bit: 1 if a_comparison_limb < b_comparison_limb, 0 otherwise.
    pub bit: T,
}
```

Layout: 4 + 1 + 2 + 1 = 8 columns total.
-/

-- ============================================================================
-- LtWordU16Gadget — gadget-only column struct (8 columns)
-- ============================================================================

#define_subair "LtWordU16Gadget" using "pico_encapsulation" where
  Column["u16_flags_0"]
  Column["u16_flags_1"]
  Column["u16_flags_2"]
  Column["u16_flags_3"]
  Column["not_eq_inv"]
  Column["comparison_limbs_0"]
  Column["comparison_limbs_1"]
  Column["bit"]
