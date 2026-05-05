import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubwGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# SubwChip (64-bit)

Lean formalisation of `SubwCols` / `SubwValueCols` from
`vm/src/chips/chips/alu/subw/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct SubwCols<F> {
    pub values: [SubwValueCols<F>; ADD_DATAPAR],   // ADD_DATAPAR = 1
}

pub struct SubwValueCols<F> {
    pub subw_operation: SubwGadget<F>,
    pub operand_1: Word<F>,
    pub operand_2: Word<F>,
    pub is_subw: F,
}
```

Layout: 3 (`SubwGadget`) + 4 (operand_1) + 4 (operand_2) + 1 (`is_subw`) = 12
columns total.
-/

-- ============================================================================
-- SubwValueCols (12 columns)
-- ============================================================================

#define_subair "SubwValueCols" using "pico_encapsulation" where
  SubAir["subw_operation": "SubwGadget" width := 3]
  Column["operand_1_0"]
  Column["operand_1_1"]
  Column["operand_1_2"]
  Column["operand_1_3"]
  Column["operand_2_0"]
  Column["operand_2_1"]
  Column["operand_2_2"]
  Column["operand_2_3"]
  Column["is_subw"]

-- ============================================================================
-- SubwCols (12 columns — single SubwValueCols, ADD_DATAPAR = 1)
-- ============================================================================

#define_subair "SubwCols" using "pico_encapsulation" where
  SubAir["values": "SubwValueCols" width := 12]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "SubwChip" using "pico_encapsulation" where
  MainSubAir["cols": "SubwCols" width := 12]
