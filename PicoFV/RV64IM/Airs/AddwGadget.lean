import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# AddwGadget (64-bit)

Lean formalisation of `AddwGadget` from
`vm/src/chips/gadgets/addw.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct AddwGadget<T> {
    /// The result of the ADDW gadget.
    pub value: [T; WORD_SIZE / 2],   // [T; 2] — only the low 32 bits matter

    /// The msb of the result.
    pub msb: U16MSBGadget<T>,
}
```

Layout: 2 + 1 = 3 columns total. The high two limbs of the full 64-bit
result word are sign-extended from `msb` by the parent chip.
-/

-- ============================================================================
-- AddwGadget — gadget-only column struct (3 columns)
-- ============================================================================

#define_subair "AddwGadget" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  SubAir["msb": "U16MSBGadget" width := 1]
