import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.BitwiseU16Gadget

open Plonky3

set_option linter.unusedVariables false

/-!
# BitwiseChip (64-bit)

Lean formalisation of `BitwiseCols` / `BitwiseValueCols` from
`vm/src/chips/chips/alu/bitwise/columns.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct BitwiseCols<T> {
    pub values: [BitwiseValueCols<T>; BITWISE_DATAPAR],   // BITWISE_DATAPAR = 1
}

pub struct BitwiseValueCols<T> {
    pub b: Word<T>,
    pub c: Word<T>,
    pub bitwise: BitWiseU16Gadget<T>,
    pub is_xor: T,
    pub is_or: T,
    pub is_and: T,
}
```

Layout: 4 (b) + 4 (c) + 16 (`BitWiseU16Gadget`) + 1 + 1 + 1 = 27 columns.
This matches the extraction at `Extraction/BitwiseChip.lean`.
-/

-- ============================================================================
-- BitwiseValueCols (27 columns)
-- ============================================================================

#define_subair "BitwiseValueCols" using "pico_encapsulation" where
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  SubAir["bitwise": "BitWiseU16Gadget" width := 16]
  Column["is_xor"]
  Column["is_or"]
  Column["is_and"]

-- ============================================================================
-- BitwiseCols (27 columns — single BitwiseValueCols)
-- ============================================================================

#define_subair "BitwiseCols" using "pico_encapsulation" where
  SubAir["values": "BitwiseValueCols" width := 27]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "BitwiseChip" using "pico_encapsulation" where
  MainSubAir["cols": "BitwiseCols" width := 27]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_xor + is_or + is_and (the "is_real" multiplier)
def Valid_BitwiseValueCols.is_real
  [Field F]
  (c : Valid_BitwiseValueCols F) (row rotation : ℕ)
: F :=
  c.is_xor row rotation +
  c.is_or row rotation +
  c.is_and row rotation

@[pico_encapsulation]
lemma BitwiseValueCols.is_real_def
  [Field F]
  (c : Valid_BitwiseValueCols F) (row rotation : ℕ)
:
  c.is_xor row rotation +
  c.is_or row rotation +
  c.is_and row rotation =
  c.is_real row rotation
:= rfl
