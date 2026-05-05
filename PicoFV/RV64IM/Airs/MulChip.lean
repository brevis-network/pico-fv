import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.MulGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# MulChip (64-bit)

Lean formalisation of `MulCols` / `MulValueCols` from
`vm/src/chips/chips/alu/mul/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct MulCols<T: Copy> {
    pub values: [MulValueCols<T>; MUL_DATAPAR],   // MUL_DATAPAR = 1
}

pub struct MulValueCols<F: Copy> {
    pub a: Word<F>,
    pub b: Word<F>,
    pub c: Word<F>,
    pub mul_gadget: MulGadget<F>,
    pub is_mul: F,
    pub is_mulh: F,
    pub is_mulhu: F,
    pub is_mulhsu: F,
    pub is_mulw: F,
}
```

Layout: 4 (a) + 4 (b) + 4 (c) + 45 (`MulGadget`) + 5 selectors = 62 columns.
This matches the extraction at `Extraction/MulChip.lean`.
-/

-- ============================================================================
-- MulValueCols (62 columns)
-- ============================================================================

#define_subair "MulValueCols" using "pico_encapsulation" where
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
  SubAir["mul_gadget": "MulGadget" width := 45]
  Column["is_mul"]
  Column["is_mulh"]
  Column["is_mulhu"]
  Column["is_mulhsu"]
  Column["is_mulw"]

-- ============================================================================
-- MulCols (62 columns)
-- ============================================================================

#define_subair "MulCols" using "pico_encapsulation" where
  SubAir["values": "MulValueCols" width := 62]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "MulChip" using "pico_encapsulation" where
  MainSubAir["cols": "MulCols" width := 62]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw (the "is_real" multiplier)
def Valid_MulValueCols.is_real
  [Field F]
  (c : Valid_MulValueCols F) (row rotation : ℕ)
: F :=
  c.is_mul row rotation +
  c.is_mulh row rotation +
  c.is_mulhu row rotation +
  c.is_mulhsu row rotation +
  c.is_mulw row rotation

@[pico_encapsulation]
lemma MulValueCols.is_real_def
  [Field F]
  (c : Valid_MulValueCols F) (row rotation : ℕ)
:
  c.is_mul row rotation +
  c.is_mulh row rotation +
  c.is_mulhu row rotation +
  c.is_mulhsu row rotation +
  c.is_mulw row rotation =
  c.is_real row rotation
:= rfl
