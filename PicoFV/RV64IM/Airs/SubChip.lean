import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# SubChip (64-bit)

Lean formalisation of `SubCols` / `SubValueCols` from
`vm/src/chips/chips/alu/sub/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct SubCols<F> {
    pub values: [SubValueCols<F>; ADD_DATAPAR],   // ADD_DATAPAR = 1
}

pub struct SubValueCols<F> {
    pub sub_operation: SubGadget<F>,
    pub operand_1: Word<F>,
    pub operand_2: Word<F>,
    pub is_sub: F,
}
```

Layout: 4 (`SubGadget`) + 4 (operand_1) + 4 (operand_2) + 1 (`is_sub`) = 13
columns total.
-/

-- ============================================================================
-- SubValueCols (13 columns)
-- ============================================================================

#define_subair "SubValueCols" using "pico_encapsulation" where
  SubAir["sub_operation": "SubGadget" width := 4]
  Column["operand_1_0"]
  Column["operand_1_1"]
  Column["operand_1_2"]
  Column["operand_1_3"]
  Column["operand_2_0"]
  Column["operand_2_1"]
  Column["operand_2_2"]
  Column["operand_2_3"]
  Column["is_sub"]

-- ============================================================================
-- SubCols (13 columns — single SubValueCols, ADD_DATAPAR = 1)
-- ============================================================================

#define_subair "SubCols" using "pico_encapsulation" where
  SubAir["values": "SubValueCols" width := 13]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "SubChip" using "pico_encapsulation" where
  MainSubAir["cols": "SubCols" width := 13]
