import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.LtWordU16Gadget
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# LtSignedGadget (64-bit)

Lean formalisation of `LtSignedGadget` from
`vm/src/chips/gadgets/lt_signed.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct LtSignedGadget<T> {
    /// The result of the SLTU operation.
    pub result: LtWordU16Gadget<T>,

    /// The most significant bit of operand b if `is_signed` is true.
    pub b_msb: U16MSBGadget<T>,

    /// The most significant bit of operand c if `is_signed` is true.
    pub c_msb: U16MSBGadget<T>,
}
```

Layout: 8 (`LtWordU16Gadget`) + 1 (`U16MSBGadget`) + 1 (`U16MSBGadget`) = 10
columns total.
-/

-- ============================================================================
-- LtSignedGadget — gadget-only column struct (10 columns)
-- ============================================================================

#define_subair "LtSignedGadget" using "pico_encapsulation" where
  SubAir["result": "LtWordU16Gadget" width := 8]
  SubAir["b_msb": "U16MSBGadget" width := 1]
  SubAir["c_msb": "U16MSBGadget" width := 1]
