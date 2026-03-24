import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV32IM.Extraction.Attributes
import PicoFV.RV32IM.Airs.Attributes

open Plonky3

set_option linter.unusedVariables false

/-!
# Shared Sub-air definitions

Common column structures reused across multiple AIR definitions (CpuAir, MemoryReadWriteAir, etc.).

Rust sources:
- MemoryAccessCols / MemoryReadCols:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_memory/read_write/columns.rs
- MemoryReadWriteCols:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_memory/read_write/columns.rs
-/

-- ============================================================================
-- Shared sub-air definitions
-- ============================================================================

-- Rust: MemoryAccessCols (9 columns)
-- Fields: value (Word = 4), prev_chunk, prev_clk, compare_clk, diff_16bit_limb, diff_8bit_limb
#define_subair "MemoryAccessCols" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  Column["value_2"]
  Column["value_3"]
  Column["prev_chunk"]
  Column["prev_clk"]
  Column["compare_clk"]
  Column["diff_16bit_limb"]
  Column["diff_8bit_limb"]

-- Rust: MemoryReadWriteCols (13 columns = prev_value:4 + MemoryAccessCols:9)
-- MemoryReadCols is structurally identical to MemoryAccessCols, so we reuse it directly.
#define_subair "MemoryReadWriteCols" using "pico_encapsulation" where
  Column["prev_value_0"]
  Column["prev_value_1"]
  Column["prev_value_2"]
  Column["prev_value_3"]
  SubAir["access": "MemoryAccessCols" width := 9]
