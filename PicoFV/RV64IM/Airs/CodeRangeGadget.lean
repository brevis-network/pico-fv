import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# CodeRangeGadget (64-bit)

Lean formalisation of `CodeRangeCols` from `vm/src/chips/gadgets/code_range.rs` at Pico v3.2.0
(`fcfa504624657d0c417c43f1233d5d891f293ff9`).

```rust
pub struct CodeRangeCols<T> {
    pub code_start: [T; 2],
    pub code_end: [T; 2],
    pub below: T,
    pub borrow: T,
    pub distance: [T; 2],
}
```

The gadget checks that a write of `width` bytes at `addr` misses the program's code,
`[code_start, code_end)`. The caller supplies `addr` as two 16-bit pieces, `width` and the
`is_store` flag. The standalone wrapper `extractor/src/gadgets.rs` lays out those inputs around
the gadget's 8 columns: 12 columns in all.
-/

-- ============================================================================
-- CodeRangeGadget — gadget-only column struct (8 columns)
-- ============================================================================

#define_subair "CodeRangeGadget" using "pico_encapsulation" where
  Column["code_start_0"]
  Column["code_start_1"]
  Column["code_end_0"]
  Column["code_end_1"]
  Column["below"]
  Column["borrow"]
  Column["distance_0"]
  Column["distance_1"]

-- ============================================================================
-- CodeRangeGadgetExtractionCols — wrapped form for the standalone Air extraction
-- ============================================================================

#define_subair "CodeRangeGadgetExtractionCols" using "pico_encapsulation" where
  Column["addr_0"]
  Column["addr_1"]
  Column["store_width"]
  SubAir["gadget": "CodeRangeGadget" width := 8]
  Column["is_store"]

-- ============================================================================
-- Air definition (wraps the extraction)
-- ============================================================================

#define_air "CodeRangeGadgetAir" using "pico_encapsulation" where
  MainSubAir["cols": "CodeRangeGadgetExtractionCols" width := 12]
