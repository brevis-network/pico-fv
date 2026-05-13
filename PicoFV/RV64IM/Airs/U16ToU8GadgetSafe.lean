import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.U16ToU8GadgetUnsafe

open Plonky3

set_option linter.unusedVariables false

/-!
# U16ToU8Gadget (Safe variant, 64-bit)

Lean formalisation of `U16ToU8Gadget::eval_u16_to_u8_safe` from
`vm/src/chips/gadgets/u16_to_u8.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
impl<F: Field> U16ToU8Gadget<F> {
    pub fn eval_u16_to_u8_safe<CB>(builder, a, cols, is_real) -> [CB::Expr; WORD_SIZE] {
        let ret = Self::eval_u16_to_u8_unsafe(builder, a, cols);
        // … plus 4 byte-bus range checks gated by `is_real` …
        ret
    }
}
```

The **safe** variant calls `eval_u16_to_u8_unsafe` first (so the columns and
returned expressions are identical to Unsafe) and then adds 4 byte-bus
lookups — one per limb — that range-check the `(low_byte, high_byte)` pair
against byte-bus opcode `(4, 7)`. Range-checking is **enforced** here, unlike
the Unsafe variant where the caller is responsible.

The wrapped extraction Air has 9 columns (same as Unsafe): `a` (4 limbs) +
`u16_to_u8` (4 low bytes) + `is_real` (1). Matches
`Extraction/U16ToU8GadgetSafe.lean` (0 algebraic constraints, 4 bus
interactions).

The bare 4-column `U16ToU8Gadget` subair is defined in
`U16ToU8GadgetUnsafe.lean` and re-used here.
-/

-- ============================================================================
-- U16ToU8GadgetSafeExtractionCols — wrapped form (a + gadget + is_real)
-- ============================================================================

#define_subair "U16ToU8GadgetSafeExtractionCols" using "pico_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  SubAir["u16_to_u8": "U16ToU8Gadget" width := 4]
  Column["is_real"]

-- ============================================================================
-- Air definition (wraps the safe extraction — 0 constraints, 4 bus lookups)
-- ============================================================================

#define_air "U16ToU8GadgetSafe" using "pico_encapsulation" where
  MainSubAir["cols": "U16ToU8GadgetSafeExtractionCols" width := 9]
