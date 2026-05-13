import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# U16ToU8Gadget (Unsafe variant, 64-bit)

Lean formalisation of `U16ToU8Gadget::eval_u16_to_u8_unsafe` from
`vm/src/chips/gadgets/u16_to_u8.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct U16ToU8Gadget<T> {
    pub low_bytes: [T; WORD_SIZE],   // 4 bytes
}

impl<F: Field> U16ToU8Gadget<F> {
    pub fn eval_u16_to_u8_unsafe<CB>(builder, a, cols) -> [CB::Expr; WORD_SIZE]
}
```

The **unsafe** variant populates `low_bytes` with the low byte of each u16
limb and returns the per-limb high byte expression
`(limb_i - low_bytes_i) * inv(256)` — but adds **no constraints and no
byte-bus lookups**. Range-checking the low/high bytes is the caller's
responsibility.

The shared 4-column gadget struct (`U16ToU8Gadget`) is defined here so that
both the Safe wrapper and any chip that embeds the gadget can reference it.
The Pico extraction's wrapped test Air uses 9 columns: `a` (4 limbs) +
`u16_to_u8` (4 low bytes) + `is_real` (1). Matches
`Extraction/U16ToU8GadgetUnsafe.lean` (0 algebraic constraints, 0 bus
interactions).
-/

-- ============================================================================
-- U16ToU8Gadget — shared 4-column struct (used by both variants and embedded
-- in BitWiseU16Gadget / MulGadget / EcallCols).
-- ============================================================================

#define_subair "U16ToU8Gadget" using "pico_encapsulation" where
  Column["low_bytes_0"]
  Column["low_bytes_1"]
  Column["low_bytes_2"]
  Column["low_bytes_3"]

-- ============================================================================
-- U16ToU8GadgetUnsafeExtractionCols — wrapped form (a + gadget + is_real)
-- ============================================================================

#define_subair "U16ToU8GadgetUnsafeExtractionCols" using "pico_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  SubAir["u16_to_u8": "U16ToU8Gadget" width := 4]
  Column["is_real"]

-- ============================================================================
-- Air definition (wraps the unsafe extraction — 0 constraints, 0 bus)
-- ============================================================================

#define_air "U16ToU8GadgetUnsafe" using "pico_encapsulation" where
  MainSubAir["cols": "U16ToU8GadgetUnsafeExtractionCols" width := 9]
