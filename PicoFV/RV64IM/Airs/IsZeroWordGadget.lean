import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.IsZeroGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# IsZeroWordGadget (64-bit)

Lean formalisation of `IsZeroWordGadget` from
`vm/src/chips/gadgets/is_zero_word.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct IsZeroWordGadget<T> {
    /// `IsZeroGadget` to check if each byte in the input word is zero.
    pub is_zero_byte: [IsZeroGadget<T>; WORD_SIZE],   // WORD_SIZE = 4

    /// A boolean flag indicating whether the lower word (the bottom 16 bits ...) is 0.
    /// This equals `is_zero_byte[0] * is_zero_byte[1]`.
    pub is_lower_half_zero: T,

    /// A boolean flag indicating whether the upper word (the top 16 bits ...) is 0.
    /// This equals `is_zero_byte[2] * is_zero_byte[3]`.
    pub is_upper_half_zero: T,

    /// A boolean flag indicating whether the word is zero. This equals the product of
    /// `is_lower_half_zero` and `is_upper_half_zero`.
    pub result: T,
}
```

Layout: 4 × 2 (per-limb `IsZeroGadget`) + 1 + 1 + 1 = 11 columns.

The standalone Lean extraction wraps this with the input value (4 limbs)
and an `is_real` column: 4 + 11 + 1 = 16 columns total.
-/

-- ============================================================================
-- IsZeroWordGadget — gadget-only column struct (11 columns)
-- ============================================================================

#define_subair "IsZeroWordGadget" using "pico_encapsulation" where
  SubAir["is_zero_byte_0": "IsZeroGadget" width := 2]
  SubAir["is_zero_byte_1": "IsZeroGadget" width := 2]
  SubAir["is_zero_byte_2": "IsZeroGadget" width := 2]
  SubAir["is_zero_byte_3": "IsZeroGadget" width := 2]
  Column["is_lower_half_zero"]
  Column["is_upper_half_zero"]
  Column["result"]

-- ============================================================================
-- IsZeroWordGadgetExtractionCols — wrapped form (input + gadget + is_real)
-- ============================================================================

#define_subair "IsZeroWordGadgetExtractionCols" using "pico_encapsulation" where
  Column["input_0"]
  Column["input_1"]
  Column["input_2"]
  Column["input_3"]
  SubAir["gadget": "IsZeroWordGadget" width := 11]
  Column["is_real"]

-- ============================================================================
-- Air definition (wraps the extraction)
-- ============================================================================

#define_air "IsZeroWordGadgetAir" using "pico_encapsulation" where
  MainSubAir["cols": "IsZeroWordGadgetExtractionCols" width := 16]
