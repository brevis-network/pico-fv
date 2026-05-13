import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
-- bitwise_u16.rs:61-62 calls `eval_u16_to_u8_unsafe` for both b_low_bytes and c_low_bytes.
import PicoFV.RV64IM.Airs.U16ToU8GadgetUnsafe
import PicoFV.RV64IM.Airs.BitwiseGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# BitWiseU16Gadget (64-bit)

Lean formalisation of `BitWiseU16Gadget` from
`vm/src/chips/gadgets/bitwise_u16.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct BitWiseU16Gadget<T> {
    /// Lower byte of the limbs of `b`.
    pub b_low_bytes: U16ToU8Gadget<T>,

    /// Lower byte of the limbs of `c`.
    pub c_low_bytes: U16ToU8Gadget<T>,

    /// The bitwise operation over bytes.
    pub bitwise: BitWiseGadget<T>,
}
```

Lifts a per-byte `BitWiseGadget` to operate on 4×16-bit-limb operands by
holding the lower bytes of each limb explicitly (`b_low_bytes`, `c_low_bytes`
— 4 bytes each). The high byte of each limb is reconstructed inline as
`(limb_i - low_byte_i) * inv(256)`.

Layout: 4 + 4 + 8 = 16 columns total.
-/

-- ============================================================================
-- BitWiseU16Gadget — gadget-only column struct (16 columns)
-- ============================================================================

#define_subair "BitWiseU16Gadget" using "pico_encapsulation" where
  SubAir["b_low_bytes": "U16ToU8Gadget" width := 4]
  SubAir["c_low_bytes": "U16ToU8Gadget" width := 4]
  SubAir["bitwise": "BitWiseGadget" width := 8]
