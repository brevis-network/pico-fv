import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.LtSignedGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# LtChip (64-bit)

Lean formalisation of `LtCols` / `LtValueCols` from
`vm/src/chips/chips/alu/lt/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct LtCols<F: Copy> {
    pub values: [LtValueCols<F>; LT_DATAPAR],   // LT_DATAPAR = 1
}

pub struct LtValueCols<F: Copy> {
    pub is_slt: F,
    pub is_slt_u: F,
    pub a: Word<F>,
    pub b: Word<F>,
    pub c: Word<F>,
    pub lt_signed: LtSignedGadget<F>,
}
```

Layout: 1 + 1 + 4 + 4 + 4 + 10 (`LtSignedGadget`) = 24 columns. This matches
the extraction at `Extraction/LtChip.lean`.
-/

-- ============================================================================
-- LtValueCols (24 columns)
-- ============================================================================

#define_subair "LtValueCols" using "pico_encapsulation" where
  Column["is_slt"]
  Column["is_slt_u"]
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  SubAir["lt_signed": "LtSignedGadget" width := 10]

-- ============================================================================
-- LtCols (24 columns)
-- ============================================================================

#define_subair "LtCols" using "pico_encapsulation" where
  SubAir["values": "LtValueCols" width := 24]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "LtChip" using "pico_encapsulation" where
  MainSubAir["cols": "LtCols" width := 24]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_slt + is_slt_u (the "is_real" multiplier)
def Valid_LtValueCols.is_real
  [Field F]
  (c : Valid_LtValueCols F) (row rotation : ℕ)
: F :=
  c.is_slt row rotation +
  c.is_slt_u row rotation

@[pico_encapsulation]
lemma LtValueCols.is_real_def
  [Field F]
  (c : Valid_LtValueCols F) (row rotation : ℕ)
:
  c.is_slt row rotation +
  c.is_slt_u row rotation =
  c.is_real row rotation
:= rfl
