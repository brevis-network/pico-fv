import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# ShiftRightChip (64-bit)

Lean formalisation of `ShiftRightCols` / `ShiftRightValueCols` from
`vm/src/chips/chips/alu/sr/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct ShiftRightCols<F: Copy> {
    pub values: [ShiftRightValueCols<F>; SR_DATAPAR],   // SR_DATAPAR = 1
}

pub struct ShiftRightValueCols<F: Copy> {
    pub a: Word<F>,
    pub b: Word<F>,
    pub c_for_lookup: Word<F>,
    pub b_msb: U16MSBGadget<F>,
    pub srw_msb: U16MSBGadget<F>,
    pub c_bits: [F; 6],
    pub c: F,
    pub imm_c: F,
    pub sra_msb_v0123: F,
    pub v_0123: F,
    pub v_012: F,
    pub v_01: F,
    pub lower_limb: Word<F>,
    pub higher_limb: Word<F>,
    pub limb_result: [F; WORD_SIZE],   // WORD_SIZE = 4
    pub shift_u16: [F; 4],
    pub is_srl: F,
    pub is_sra: F,
    pub is_srlw: F,
    pub is_sraw: F,
    pub is_w_imm: F,
}
```

Layout: 4+4+4+1+1+6+1+1+1+1+1+1+4+4+4+4+1+1+1+1+1 = 47 columns. Matches the
extraction at `Extraction/ShiftRightChip.lean`.
-/

-- ============================================================================
-- ShiftRightValueCols (47 columns)
-- ============================================================================

#define_subair "ShiftRightValueCols" using "pico_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_for_lookup_0"]
  Column["c_for_lookup_1"]
  Column["c_for_lookup_2"]
  Column["c_for_lookup_3"]
  SubAir["b_msb": "U16MSBGadget" width := 1]
  SubAir["srw_msb": "U16MSBGadget" width := 1]
  Column["c_bits_0"]
  Column["c_bits_1"]
  Column["c_bits_2"]
  Column["c_bits_3"]
  Column["c_bits_4"]
  Column["c_bits_5"]
  Column["c"]
  Column["imm_c"]
  Column["sra_msb_v0123"]
  Column["v_0123"]
  Column["v_012"]
  Column["v_01"]
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
  Column["shift_u16_0"]
  Column["shift_u16_1"]
  Column["shift_u16_2"]
  Column["shift_u16_3"]
  Column["is_srl"]
  Column["is_sra"]
  Column["is_srlw"]
  Column["is_sraw"]
  Column["is_w_imm"]

-- ============================================================================
-- ShiftRightCols (47 columns)
-- ============================================================================

#define_subair "ShiftRightCols" using "pico_encapsulation" where
  SubAir["values": "ShiftRightValueCols" width := 47]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "ShiftRightChip" using "pico_encapsulation" where
  MainSubAir["cols": "ShiftRightCols" width := 47]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_srl + is_sra + is_srlw + is_sraw (the "is_real" multiplier)
def Valid_ShiftRightValueCols.is_real
  [Field F]
  (c : Valid_ShiftRightValueCols F) (row rotation : ℕ)
: F :=
  c.is_srl row rotation +
  c.is_sra row rotation +
  c.is_srlw row rotation +
  c.is_sraw row rotation

@[pico_encapsulation]
lemma ShiftRightValueCols.is_real_def
  [Field F]
  (c : Valid_ShiftRightValueCols F) (row rotation : ℕ)
:
  c.is_srl row rotation +
  c.is_sra row rotation +
  c.is_srlw row rotation +
  c.is_sraw row rotation =
  c.is_real row rotation
:= rfl
