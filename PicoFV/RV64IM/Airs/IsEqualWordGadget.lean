import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.IsZeroWordGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# IsEqualWordGadget (64-bit)

Lean formalisation of `IsEqualWordGadget` from
`vm/src/chips/gadgets/is_equal_word.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct IsEqualWordGadget<T> {
    /// A gadget to check whether the differences in limbs are all 0.
    pub is_diff_zero: IsZeroWordGadget<T>,
}
```

Same shape as `IsZeroWordGadget` (11 cols); the `eval` body feeds the per-limb
differences `a_i - b_i` into the underlying `IsZeroGadget`s instead of the raw
limbs.

The standalone Lean extraction wraps with two input words (`a`, `b`) plus
`is_real`: 4 + 4 + 11 + 1 = 20 columns total.
-/

-- ============================================================================
-- IsEqualWordGadget — gadget-only column struct (11 columns, same as IsZeroWord)
-- ============================================================================

#define_subair "IsEqualWordGadget" using "pico_encapsulation" where
  SubAir["is_diff_zero": "IsZeroWordGadget" width := 11]

-- ============================================================================
-- IsEqualWordGadgetExtractionCols — wrapped form (a + b + gadget + is_real)
-- ============================================================================

#define_subair "IsEqualWordGadgetExtractionCols" using "pico_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  SubAir["gadget": "IsEqualWordGadget" width := 11]
  Column["is_real"]

-- ============================================================================
-- Air definition (wraps the extraction)
-- ============================================================================

#define_air "IsEqualWordGadgetAir" using "pico_encapsulation" where
  MainSubAir["cols": "IsEqualWordGadgetExtractionCols" width := 20]
