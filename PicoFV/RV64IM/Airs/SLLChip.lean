import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# SLLChip (64-bit)

Lean formalisation of `ShiftLeftCols` / `ShiftLeftValueCols` from
`vm/src/chips/chips/alu/sll/columns.rs` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

```rust
pub struct ShiftLeftCols<F: Copy + Sized> {
    pub values: [ShiftLeftValueCols<F>; SLL_DATAPAR],   // SLL_DATAPAR = 1
}

pub struct ShiftLeftValueCols<F: Copy + Sized> {
    pub a: Word<F>,
    pub b: Word<F>,
    pub c: Word<F>,
    pub c_bits: [F; 6],
    pub v_01: F,
    pub v_012: F,
    pub v_0123: F,
    pub shift_u16: [F; 4],
    pub lower_limb: Word<F>,
    pub higher_limb: Word<F>,
    pub limb_result: Word<F>,
    pub sllw_msb: U16MSBGadget<F>,
    pub is_sll: F,
    pub is_sllw: F,
}
```

Layout: 4+4+4+6+1+1+1+4+4+4+4+1+1+1 = 40 columns. Matches the extraction at
`Extraction/SLLChip.lean`.
-/

-- ============================================================================
-- ShiftLeftValueCols (40 columns)
-- ============================================================================

#define_subair "ShiftLeftValueCols" using "pico_encapsulation" where
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
  Column["c_bits_0"]
  Column["c_bits_1"]
  Column["c_bits_2"]
  Column["c_bits_3"]
  Column["c_bits_4"]
  Column["c_bits_5"]
  Column["v_01"]
  Column["v_012"]
  Column["v_0123"]
  Column["shift_u16_0"]
  Column["shift_u16_1"]
  Column["shift_u16_2"]
  Column["shift_u16_3"]
  Column["lower_limb_0"]
  Column["lower_limb_1"]
  Column["lower_limb_2"]
  Column["lower_limb_3"]
  Column["higher_limb_0"]
  Column["higher_limb_1"]
  Column["higher_limb_2"]
  Column["higher_limb_3"]
  Column["limb_result_0"]
  Column["limb_result_1"]
  Column["limb_result_2"]
  Column["limb_result_3"]
  SubAir["sllw_msb": "U16MSBGadget" width := 1]
  Column["is_sll"]
  Column["is_sllw"]

-- ============================================================================
-- ShiftLeftCols (40 columns)
-- ============================================================================

#define_subair "ShiftLeftCols" using "pico_encapsulation" where
  SubAir["values": "ShiftLeftValueCols" width := 40]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "SLLChip" using "pico_encapsulation" where
  MainSubAir["cols": "ShiftLeftCols" width := 40]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_sll + is_sllw (the "is_real" multiplier)
def Valid_ShiftLeftValueCols.is_real
  [Field F]
  (c : Valid_ShiftLeftValueCols F) (row rotation : ℕ)
: F :=
  c.is_sll row rotation +
  c.is_sllw row rotation

@[pico_encapsulation]
lemma ShiftLeftValueCols.is_real_def
  [Field F]
  (c : Valid_ShiftLeftValueCols F) (row rotation : ℕ)
:
  c.is_sll row rotation +
  c.is_sllw row rotation =
  c.is_real row rotation
:= rfl
