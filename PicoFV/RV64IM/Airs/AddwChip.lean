import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.AddwGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# AddwChip (64-bit)

Lean formalisation of `AddwCols` / `AddwValueCols` from
`vm/src/chips/chips/alu/addw/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct AddwCols<F> {
    pub values: [AddwValueCols<F>; ADD_DATAPAR],   // ADD_DATAPAR = 1
}

pub struct AddwValueCols<F> {
    pub addw_operation: AddwGadget<F>,
    pub operand_1: Word<F>,
    pub operand_2: Word<F>,
    pub is_addw: F,
}
```

Layout: 3 (`AddwGadget`) + 4 (operand_1) + 4 (operand_2) + 1 (`is_addw`) = 12
columns total.
-/

-- ============================================================================
-- AddwValueCols (12 columns)
-- ============================================================================

#define_subair "AddwValueCols" using "pico_encapsulation" where
  SubAir["addw_operation": "AddwGadget" width := 3]
  Column["operand_1_0"]
  Column["operand_1_1"]
  Column["operand_1_2"]
  Column["operand_1_3"]
  Column["operand_2_0"]
  Column["operand_2_1"]
  Column["operand_2_2"]
  Column["operand_2_3"]
  Column["is_addw"]

-- ============================================================================
-- AddwCols (12 columns — single AddwValueCols, ADD_DATAPAR = 1)
-- ============================================================================

#define_subair "AddwCols" using "pico_encapsulation" where
  SubAir["values": "AddwValueCols" width := 12]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "AddwChip" using "pico_encapsulation" where
  MainSubAir["cols": "AddwCols" width := 12]
