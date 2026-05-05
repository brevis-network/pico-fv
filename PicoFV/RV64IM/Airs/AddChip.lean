import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.AddGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# AddChip (64-bit)

Lean formalisation of `AddCols` / `AddValueCols` from
`vm/src/chips/chips/alu/add/columns.rs` at commit
`1d13964da22c7cf660eb6ee312c9c08ab6f76126`.

```rust
pub struct AddCols<F> {
    pub values: [AddValueCols<F>; ADD_DATAPAR],   // ADD_DATAPAR = 1
}

pub struct AddValueCols<F> {
    pub add_operation: AddGadget<F>,
    pub operand_1: Word<F>,
    pub operand_2: Word<F>,
    pub is_add: F,
}
```

Layout: 4 (`AddGadget`) + 4 (operand_1) + 4 (operand_2) + 1 (`is_add`) = 13
columns total.
-/

-- ============================================================================
-- AddValueCols (13 columns)
-- ============================================================================

#define_subair "AddValueCols" using "pico_encapsulation" where
  SubAir["add_operation": "AddGadget" width := 4]
  Column["operand_1_0"]
  Column["operand_1_1"]
  Column["operand_1_2"]
  Column["operand_1_3"]
  Column["operand_2_0"]
  Column["operand_2_1"]
  Column["operand_2_2"]
  Column["operand_2_3"]
  Column["is_add"]

-- ============================================================================
-- AddCols (13 columns — single AddValueCols, ADD_DATAPAR = 1)
-- ============================================================================

#define_subair "AddCols" using "pico_encapsulation" where
  SubAir["values": "AddValueCols" width := 13]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "AddChip" using "pico_encapsulation" where
  MainSubAir["cols": "AddCols" width := 13]
