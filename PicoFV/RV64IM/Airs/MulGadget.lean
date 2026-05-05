import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.U16ToU8Gadget
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# MulGadget (64-bit)

Lean formalisation of `MulGadget` from
`vm/src/chips/gadgets/mul.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct MulGadget<T> {
    pub carry: [T; LONG_WORD_BYTE_SIZE],          // LONG_WORD_BYTE_SIZE = 16
    pub product: [T; LONG_WORD_BYTE_SIZE],        // 16
    pub b_lower_byte: U16ToU8Gadget<T>,           // 4
    pub c_lower_byte: U16ToU8Gadget<T>,           // 4
    pub b_msb: T,                                 // 1
    pub c_msb: T,                                 // 1
    pub product_msb: U16MSBGadget<T>,             // 1
    pub b_sign_extend: T,                         // 1
    pub c_sign_extend: T,                         // 1
}
```

Layout: 16 + 16 + 4 + 4 + 1 + 1 + 1 + 1 + 1 = 45 columns total.
-/

-- ============================================================================
-- MulGadget — gadget-only column struct (45 columns)
-- ============================================================================

#define_subair "MulGadget" using "pico_encapsulation" where
  -- carry: [T; LONG_WORD_BYTE_SIZE = 16]
  Column["carry_0"]
  Column["carry_1"]
  Column["carry_2"]
  Column["carry_3"]
  Column["carry_4"]
  Column["carry_5"]
  Column["carry_6"]
  Column["carry_7"]
  Column["carry_8"]
  Column["carry_9"]
  Column["carry_10"]
  Column["carry_11"]
  Column["carry_12"]
  Column["carry_13"]
  Column["carry_14"]
  Column["carry_15"]
  -- product: [T; LONG_WORD_BYTE_SIZE = 16]
  Column["product_0"]
  Column["product_1"]
  Column["product_2"]
  Column["product_3"]
  Column["product_4"]
  Column["product_5"]
  Column["product_6"]
  Column["product_7"]
  Column["product_8"]
  Column["product_9"]
  Column["product_10"]
  Column["product_11"]
  Column["product_12"]
  Column["product_13"]
  Column["product_14"]
  Column["product_15"]
  -- b_lower_byte: U16ToU8Gadget = 4
  SubAir["b_lower_byte": "U16ToU8Gadget" width := 4]
  -- c_lower_byte: U16ToU8Gadget = 4
  SubAir["c_lower_byte": "U16ToU8Gadget" width := 4]
  -- Single columns
  Column["b_msb"]
  Column["c_msb"]
  SubAir["product_msb": "U16MSBGadget" width := 1]
  Column["b_sign_extend"]
  Column["c_sign_extend"]
