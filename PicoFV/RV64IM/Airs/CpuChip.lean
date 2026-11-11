import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs

open Plonky3

set_option linter.unusedVariables false

/-!
# CpuChip (Pico v3.1.1, 58 columns)

Column layout of `CpuCols` in `vm/src/chips/chips/riscv_cpu/columns.rs` at the pinned commit
(`2acc7c1828fb`), which asserts `NUM_CPU_COLS == 58` (`columns.rs:20`).

```text
 0      clk                     28-31  op_a_access.prev_value
 1      num_extra_clk           32-35  op_a_access.access.value
 2-3    pc (2 limbs)            36-37  op_a_access.access.{diff_16bit_limb, diff_hi9}
 4-5    next_pc (2 limbs)       38-41  op_b_access.access.value
 6      opcode                  42-43  op_b_access.access.{diff_16bit_limb, diff_hi9}
 7      op_a (register index)   44-47  op_c_access.access.value
 8-10   op_b (limb0, limb1, sign) 48-49 op_c_access.access.{diff_16bit_limb, diff_hi9}
 11-13  op_c (limb0, limb1, sign) 50   a_gt_b
 14     op_a_0 (rd is x0)       51     a_lt_b
 15-27  opcode selectors (13)   52     is_halt
                                53     is_real
                                54     is_last
                                55     is_alu_not_x0
                                56     jalr_lsb
                                57     pc_carry
```

Names follow the 2.x Lean files where the meaning is the same, so the equivalence proofs have
less to rename: Pico's `instruction.op_a` (the register index, one column since 3.x) is
`instruction.op_a_0`, and Pico's `instruction.op_a_0` (the "destination is x0" flag) is
`instruction.op_a_is_x0`. `op_b` and `op_c` are Pico's `SignExtImm`: `op_b_0`, `op_b_1` are
bits 0..16 and 16..32 and `op_b_sign` stands for bits 32..64.

The register accesses use Pico's "lite" layouts (`riscv_memory/read_write/columns.rs:383-415`):
no committed previous chunk or clock; the previous clock is `clk - (diff_16bit_limb +
diff_hi9 * 2^16) - 1`. They are defined here, beside the 2.x shapes in `SubAirs.lean`, which the
memory chip still uses.
-/

-- ============================================================================
-- Lite register-access layouts (6 and 10 columns)
-- ============================================================================

#define_subair "MemoryAccessLiteCols" using "pico_encapsulation" where
  Column["value_0"]
  Column["value_1"]
  Column["value_2"]
  Column["value_3"]
  Column["diff_16bit_limb"]
  Column["diff_hi9"]

#define_subair "MemoryReadLiteCols" using "pico_encapsulation" where
  SubAir["access": "MemoryAccessLiteCols" width := 6]

#define_subair "MemoryReadWriteLiteCols" using "pico_encapsulation" where
  Column["prev_value_0"]
  Column["prev_value_1"]
  Column["prev_value_2"]
  Column["prev_value_3"]
  SubAir["access": "MemoryAccessLiteCols" width := 6]

-- ============================================================================
-- InstructionCols (9 columns)
-- ============================================================================

#define_subair "InstructionCols" using "pico_encapsulation" where
  Column["opcode"]
  Column["op_a_0"]
  Column["op_b_0"]
  Column["op_b_1"]
  Column["op_b_sign"]
  Column["op_c_0"]
  Column["op_c_1"]
  Column["op_c_sign"]
  Column["op_a_is_x0"]

-- ============================================================================
-- OpcodeSelectorCols (13 columns)
-- ============================================================================

#define_subair "OpcodeSelectorCols" using "pico_encapsulation" where
  Column["imm_b"]
  Column["imm_c"]
  Column["is_ecall"]
  Column["is_memory"]
  Column["is_store"]
  Column["is_beq"]
  Column["is_bne"]
  Column["is_blt"]
  Column["is_bge"]
  Column["is_bltu"]
  Column["is_bgeu"]
  Column["is_jalr"]
  Column["is_jal"]

-- ============================================================================
-- CpuCols (58 columns)
-- ============================================================================

#define_subair "CpuCols" using "pico_encapsulation" where
  Column["clk"]
  Column["num_extra_clk"]
  Column["pc_0"]
  Column["pc_1"]
  Column["next_pc_0"]
  Column["next_pc_1"]
  SubAir["instruction": "InstructionCols" width := 9]
  SubAir["opcode_selector": "OpcodeSelectorCols" width := 13]
  SubAir["op_a_access": "MemoryReadWriteLiteCols" width := 10]
  SubAir["op_b_access": "MemoryReadLiteCols" width := 6]
  SubAir["op_c_access": "MemoryReadLiteCols" width := 6]
  Column["a_gt_b"]
  Column["a_lt_b"]
  Column["is_halt"]
  Column["is_real"]
  Column["is_last"]
  Column["is_alu_not_x0"]
  Column["jalr_lsb"]
  Column["pc_carry"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "CpuChip" using "pico_encapsulation" where
  MainSubAir["cols": "CpuCols" width := 58]
