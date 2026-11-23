import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.MulGadget
import PicoFV.RV64IM.Airs.LtWordU16Gadget
import PicoFV.RV64IM.Airs.AddGadget
import PicoFV.RV64IM.Airs.IsZeroWordGadget
import PicoFV.RV64IM.Airs.IsEqualWordGadget
import PicoFV.RV64IM.Airs.U16MSBGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# DivRemChip (64-bit)

Lean formalisation of `DivRemCols` / `DivRemValueCols` from
`vm/src/chips/chips/alu/divrem/columns.rs` at commit
`2acc7c1828fb4ec1bed5963511bb370870c5b608` (Pico v3.1.1).

```rust
pub struct DivRemCols<F: Copy> {
    pub values: [DivRemValueCols<F>; DIVREM_DATAPAR],   // DIVREM_DATAPAR = 1
}

pub struct DivRemValueCols<F: Copy> {
    pub a: Word<F>,
    pub b: Word<F>,
    pub c: Word<F>,
    pub b_raw: Word<F>,
    pub c_raw: Word<F>,
    pub quotient: Word<F>,
    pub quotient_comp: Word<F>,
    pub remainder_comp: Word<F>,
    pub remainder: Word<F>,
    pub abs_remainder: Word<F>,
    pub abs_c: Word<F>,
    pub max_abs_c_or_1: Word<F>,
    pub c_times_quotient: [F; LONG_WORD_SIZE],         // LONG_WORD_SIZE = 8
    pub c_times_quotient_lower: MulGadget<F>,          // 45
    pub c_times_quotient_upper: MulGadget<F>,          // 45
    pub remainder_lt_gadget: LtWordU16Gadget<F>,       // 8
    pub c_neg_gadget: AddGadget<F>,                    // 4
    pub rem_neg_gadget: AddGadget<F>,                  // 4
    pub carry: [F; LONG_WORD_SIZE],                    // 8
    pub is_c_0: IsZeroWordGadget<F>,                   // 11
    pub is_div: F,
    pub is_divu: F,
    pub is_rem: F,
    pub is_remu: F,
    pub is_divw: F,
    pub is_remw: F,
    pub is_divuw: F,
    pub is_remuw: F,
    pub is_overflow: F,
    pub is_overflow_b: IsEqualWordGadget<F>,           // 11
    pub is_overflow_c: IsEqualWordGadget<F>,           // 11
    pub b_msb: U16MSBGadget<F>,                        // 1
    pub rem_msb: U16MSBGadget<F>,                      // 1
    pub c_msb: U16MSBGadget<F>,                        // 1
    pub quot_msb: U16MSBGadget<F>,                     // 1
    pub b_neg: F,
    pub b_neg_not_overflow: F,
    pub b_not_neg_not_overflow: F,
    pub is_real_not_word: F,
    pub rem_neg: F,
    pub c_neg: F,
    pub abs_c_alu_event: F,
    pub abs_rem_alu_event: F,
    pub is_real: F,
    pub remainder_check_multiplicity: F,
}
```

Layout: 4*12 (12 Words) + 8 (`c_times_quotient`) + 45 (`c_times_quotient_lower`)
+ 45 (`c_times_quotient_upper`) + 8 (`remainder_lt_gadget`) + 4 (`c_neg_gadget`)
+ 4 (`rem_neg_gadget`) + 8 (`carry`) + 11 (`is_c_0`) + 8 (op selectors) + 1
(`is_overflow`) + 11 (`is_overflow_b`) + 11 (`is_overflow_c`) + 4 (4 ×
`U16MSBGadget`) + 4 (`b_neg`/etc.) + 4 (`rem_neg`/etc.) + 2
(`is_real`/`remainder_check_multiplicity`) = 226 columns.

`b` and `c` are the operands in computational form (for word operations the
low 32 bits, zero- or sign-extended); `b_raw` and `c_raw` are the register
values the CPU sent, which the ALU bus carries.

This matches the extraction at `Extraction/DivRemChip.lean`.
-/

-- ============================================================================
-- DivRemValueCols (226 columns)
-- ============================================================================

#define_subair "DivRemValueCols" using "pico_encapsulation" where
  -- a (Word) — output operand
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  -- b (Word) — first input operand
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  -- c (Word) — second input operand
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  -- b_raw (Word) — first input operand as read from the register
  Column["b_raw_0"]
  Column["b_raw_1"]
  Column["b_raw_2"]
  Column["b_raw_3"]
  -- c_raw (Word) — second input operand as read from the register
  Column["c_raw_0"]
  Column["c_raw_1"]
  Column["c_raw_2"]
  Column["c_raw_3"]
  -- quotient (Word)
  Column["quotient_0"]
  Column["quotient_1"]
  Column["quotient_2"]
  Column["quotient_3"]
  -- quotient_comp (Word)
  Column["quotient_comp_0"]
  Column["quotient_comp_1"]
  Column["quotient_comp_2"]
  Column["quotient_comp_3"]
  -- remainder_comp (Word)
  Column["remainder_comp_0"]
  Column["remainder_comp_1"]
  Column["remainder_comp_2"]
  Column["remainder_comp_3"]
  -- remainder (Word)
  Column["remainder_0"]
  Column["remainder_1"]
  Column["remainder_2"]
  Column["remainder_3"]
  -- abs_remainder (Word)
  Column["abs_remainder_0"]
  Column["abs_remainder_1"]
  Column["abs_remainder_2"]
  Column["abs_remainder_3"]
  -- abs_c (Word)
  Column["abs_c_0"]
  Column["abs_c_1"]
  Column["abs_c_2"]
  Column["abs_c_3"]
  -- max_abs_c_or_1 (Word)
  Column["max_abs_c_or_1_0"]
  Column["max_abs_c_or_1_1"]
  Column["max_abs_c_or_1_2"]
  Column["max_abs_c_or_1_3"]
  -- c_times_quotient ([F; LONG_WORD_SIZE = 8])
  Column["c_times_quotient_0"]
  Column["c_times_quotient_1"]
  Column["c_times_quotient_2"]
  Column["c_times_quotient_3"]
  Column["c_times_quotient_4"]
  Column["c_times_quotient_5"]
  Column["c_times_quotient_6"]
  Column["c_times_quotient_7"]
  -- c_times_quotient_lower (MulGadget = 45)
  SubAir["c_times_quotient_lower": "MulGadget" width := 45]
  -- c_times_quotient_upper (MulGadget = 45)
  SubAir["c_times_quotient_upper": "MulGadget" width := 45]
  -- remainder_lt_gadget (LtWordU16Gadget = 8)
  SubAir["remainder_lt_gadget": "LtWordU16Gadget" width := 8]
  -- c_neg_gadget (AddGadget = 4)
  SubAir["c_neg_gadget": "AddGadget" width := 4]
  -- rem_neg_gadget (AddGadget = 4)
  SubAir["rem_neg_gadget": "AddGadget" width := 4]
  -- carry ([F; LONG_WORD_SIZE = 8])
  Column["carry_0"]
  Column["carry_1"]
  Column["carry_2"]
  Column["carry_3"]
  Column["carry_4"]
  Column["carry_5"]
  Column["carry_6"]
  Column["carry_7"]
  -- is_c_0 (IsZeroWordGadget = 11)
  SubAir["is_c_0": "IsZeroWordGadget" width := 11]
  -- Operation selectors
  Column["is_div"]
  Column["is_divu"]
  Column["is_rem"]
  Column["is_remu"]
  Column["is_divw"]
  Column["is_remw"]
  Column["is_divuw"]
  Column["is_remuw"]
  -- Overflow flag
  Column["is_overflow"]
  -- is_overflow_b (IsEqualWordGadget = 11)
  SubAir["is_overflow_b": "IsEqualWordGadget" width := 11]
  -- is_overflow_c (IsEqualWordGadget = 11)
  SubAir["is_overflow_c": "IsEqualWordGadget" width := 11]
  -- MSB gadgets (4 × U16MSBGadget = 4)
  SubAir["b_msb": "U16MSBGadget" width := 1]
  SubAir["rem_msb": "U16MSBGadget" width := 1]
  SubAir["c_msb": "U16MSBGadget" width := 1]
  SubAir["quot_msb": "U16MSBGadget" width := 1]
  -- Sign / overflow bookkeeping
  Column["b_neg"]
  Column["b_neg_not_overflow"]
  Column["b_not_neg_not_overflow"]
  Column["is_real_not_word"]
  Column["rem_neg"]
  Column["c_neg"]
  -- ALU event selectors
  Column["abs_c_alu_event"]
  Column["abs_rem_alu_event"]
  -- Realness flag and remainder check multiplicity
  Column["is_real"]
  Column["remainder_check_multiplicity"]

-- ============================================================================
-- DivRemCols (226 columns — single DivRemValueCols, DIVREM_DATAPAR = 1)
-- ============================================================================

#define_subair "DivRemCols" using "pico_encapsulation" where
  SubAir["values": "DivRemValueCols" width := 226]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "DivRemChip" using "pico_encapsulation" where
  MainSubAir["cols": "DivRemCols" width := 226]

-- ============================================================================
-- Computed values
-- ============================================================================

-- Rust: is_div + is_rem (signed operations)
def Valid_DivRemValueCols.is_signed
  [Field F]
  (c : Valid_DivRemValueCols F) (row rotation : ℕ)
: F :=
  c.is_div row rotation +
  c.is_rem row rotation

@[pico_encapsulation]
lemma DivRemValueCols.is_signed_def
  [Field F]
  (c : Valid_DivRemValueCols F) (row rotation : ℕ)
:
  c.is_div row rotation +
  c.is_rem row rotation =
  c.is_signed row rotation
:= rfl
