import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# BitWiseGadget (64-bit)

Lean formalisation of `BitWiseGadget` from
`vm/src/chips/gadgets/bitwise.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct BitWiseGadget<T> {
    /// The result of the bitwise operation in bytes.
    pub result: [T; WORD_BYTE_SIZE],   // WORD_BYTE_SIZE = 8
}
```

Stores the byte-level result of a bitwise operation (XOR/OR/AND) on a
64-bit Word. Each byte is range-checked and validated against the byte bus
by the parent chip.
-/

-- ============================================================================
-- BitWiseGadget — gadget-only column struct (8 columns)
-- ============================================================================

#define_subair "BitWiseGadget" using "pico_encapsulation" where
  Column["result_0"]
  Column["result_1"]
  Column["result_2"]
  Column["result_3"]
  Column["result_4"]
  Column["result_5"]
  Column["result_6"]
  Column["result_7"]
