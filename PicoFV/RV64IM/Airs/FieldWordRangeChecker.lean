import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.IsZeroGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# FieldWordRangeChecker (64-bit)

Lean formalisation of `FieldWordRangeChecker` from
`vm/src/chips/gadgets/field_range_check/word_range.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct FieldWordRangeChecker<T> {
    /// Most sig byte LE bit decomposition.
    pub most_sig_byte_decomp: [T; 8],

    /// Check the range of the last byte.
    pub upper_all_one: IsZeroGadget<T>,
}
```

Layout: 8 + 2 = 10 columns total.

Used by `EcallCols` in `riscv_cpu` to range-check `operand_to_check` Word
values that must fit within a field-element-friendly range.
-/

-- ============================================================================
-- FieldWordRangeChecker — gadget-only column struct (10 columns)
-- ============================================================================

#define_subair "FieldWordRangeChecker" using "pico_encapsulation" where
  Column["most_sig_byte_decomp_0"]
  Column["most_sig_byte_decomp_1"]
  Column["most_sig_byte_decomp_2"]
  Column["most_sig_byte_decomp_3"]
  Column["most_sig_byte_decomp_4"]
  Column["most_sig_byte_decomp_5"]
  Column["most_sig_byte_decomp_6"]
  Column["most_sig_byte_decomp_7"]
  SubAir["upper_all_one": "IsZeroGadget" width := 2]
