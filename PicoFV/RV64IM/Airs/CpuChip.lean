import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs
import PicoFV.RV64IM.Airs.IsZeroGadget
-- EcallCols.syscall_code_bytes is evaluated with both variants depending on path:
--   ecall/constraints.rs:47  → eval_u16_to_u8_safe   (main syscall path)
--   ecall/constraints.rs:296 → eval_u16_to_u8_unsafe (is_commit path)
--   ecall/constraints.rs:332 → eval_u16_to_u8_unsafe (is_commit_deferred_proofs path)
import PicoFV.RV64IM.Airs.U16ToU8GadgetSafe
import PicoFV.RV64IM.Airs.U16ToU8GadgetUnsafe

open Plonky3

set_option linter.unusedVariables false

/-!
# CpuChip (64-bit)

Lean formalisation of `CpuCols` and its sub-structures from
`vm/src/chips/chips/riscv_cpu/...` at commit
`22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`.

Sub-structures (from `instruction/columns.rs`, `opcode_selector/columns.rs`,
`opcode_specific/columns.rs`, `auipc/columns.rs`, `branch/columns.rs`,
`ecall/columns.rs`, `jump/columns.rs`):

```rust
pub struct InstructionCols<T> {
    pub opcode: T,
    pub op_a: Word<T>,                                    // 4
    pub op_b: Word<T>,                                    // 4
    pub op_c: Word<T>,                                    // 4
    pub op_a_0: T,
}                                                          // total: 14

pub struct OpcodeSelectorCols<T> {
    // 4 + 11 (memory) + 6 (branch) + 2 (jump) + 2 (misc) = 25 selectors
    pub imm_b: T, pub imm_c: T, pub is_alu: T, pub is_ecall: T,
    pub is_lb: T, pub is_lbu: T, pub is_lh: T, pub is_lhu: T,
    pub is_lw: T, pub is_lwu: T, pub is_ld: T,
    pub is_sb: T, pub is_sh: T, pub is_sw: T, pub is_sd: T,
    pub is_beq: T, pub is_bne: T, pub is_blt: T, pub is_bge: T,
    pub is_bltu: T, pub is_bgeu: T,
    pub is_jalr: T, pub is_jal: T,
    pub is_auipc: T, pub is_unimpl: T,
}                                                          // total: 25

pub struct BranchCols<T> { a_eq_b: T, a_gt_b: T, a_lt_b: T }    //  3
pub struct AuipcCols<T>(PhantomData<T>);                        //  0
pub struct JumpCols<T> { pub jalr_lsb: T }                       //  1
pub struct EcallCols<T> {
    pub syscall_code_bytes: U16ToU8Gadget<T>,                 //  4
    pub is_enter_unconstrained: IsZeroGadget<T>,              //  2
    pub is_hint_len: IsZeroGadget<T>,                         //  2
    pub is_halt: IsZeroGadget<T>,                             //  2
    pub is_commit: IsZeroGadget<T>,                           //  2
    pub is_commit_deferred_proofs: IsZeroGadget<T>,           //  2
    pub index_bitmap: [T; PV_DIGEST_NUM_WORDS],               //  8
    pub operand_range_check_cols: FieldWordRangeChecker<T>,   // 10
    pub operand_to_check: Word<T>,                            //  4
}                                                              // total: 36

pub union OpcodeSpecificCols<T> {                              // size = max = 36
    branch: BranchCols<T>, jump: JumpCols<T>,
    auipc: AuipcCols<T>, ecall: EcallCols<T>,
}
```

Top-level `CpuCols` (132 columns total):
```rust
pub struct CpuCols<T> {
    pub chunk: T,
    pub clk: T,
    pub clk_16bit_limb: T,
    pub clk_8bit_limb: T,
    pub num_extra_clk: T,
    pub pc: Addr<T>,                          //  3
    pub next_pc: Addr<T>,                     //  3
    pub instruction: InstructionCols<T>,      // 14
    pub opcode_selector: OpcodeSelectorCols<T>, // 25
    pub op_a_access: MemoryReadWriteCols<T>,  // 13
    pub op_b_access: MemoryReadCols<T>,       //  9
    pub op_c_access: MemoryReadCols<T>,       //  9
    pub opcode_specific: OpcodeSpecificCols<T>, // 36
    pub is_real: T,
    pub branching: T,
    pub not_branching: T,
    pub ecall_mul_send_to_table: T,
    pub ecall_range_check_operand: T,
    pub is_sequential_instr: T,
    pub pc_carry_a: [T; 5],
    pub pc_carry_b: [T; 4],
}
```

Layout: 5 + 3 + 3 + 14 + 25 + 13 + 9 + 9 + 36 + 6 + 5 + 4 = **132 columns**.
This matches `Extraction/CpuChip.lean`.
-/

-- ============================================================================
-- InstructionCols (14 columns)
-- ============================================================================

#define_subair "InstructionCols" using "pico_encapsulation" where
  Column["opcode"]
  Column["op_a_0"]
  Column["op_a_1"]
  Column["op_a_2"]
  Column["op_a_3"]
  Column["op_b_0"]
  Column["op_b_1"]
  Column["op_b_2"]
  Column["op_b_3"]
  Column["op_c_0"]
  Column["op_c_1"]
  Column["op_c_2"]
  Column["op_c_3"]
  Column["op_a_is_x0"]

-- ============================================================================
-- OpcodeSelectorCols (25 columns)
-- ============================================================================

#define_subair "OpcodeSelectorCols" using "pico_encapsulation" where
  Column["imm_b"]
  Column["imm_c"]
  Column["is_alu"]
  Column["is_ecall"]
  Column["is_lb"]
  Column["is_lbu"]
  Column["is_lh"]
  Column["is_lhu"]
  Column["is_lw"]
  Column["is_lwu"]
  Column["is_ld"]
  Column["is_sb"]
  Column["is_sh"]
  Column["is_sw"]
  Column["is_sd"]
  Column["is_beq"]
  Column["is_bne"]
  Column["is_blt"]
  Column["is_bge"]
  Column["is_bltu"]
  Column["is_bgeu"]
  Column["is_jalr"]
  Column["is_jal"]
  Column["is_auipc"]
  Column["is_unimpl"]

-- ============================================================================
-- OpcodeSpecificCols (36 columns)
--
-- This is a Rust `union` of BranchCols(3), JumpCols(1), AuipcCols(0),
-- EcallCols(36); the layout therefore mirrors `EcallCols` (the largest member).
-- We expose it via 36 generic `specific_<i>` columns; per-variant lemmas in
-- the constraint helper files re-interpret the relevant prefix. For JALR,
-- the union's first slot (`specific_0`) carries the `jalr_lsb` witness
-- (bit 0 of `rs1 + imm`).
-- ============================================================================

#define_subair "OpcodeSpecificCols" using "pico_encapsulation" where
  Column["specific_0"]
  Column["specific_1"]
  Column["specific_2"]
  Column["specific_3"]
  Column["specific_4"]
  Column["specific_5"]
  Column["specific_6"]
  Column["specific_7"]
  Column["specific_8"]
  Column["specific_9"]
  Column["specific_10"]
  Column["specific_11"]
  Column["specific_12"]
  Column["specific_13"]
  Column["specific_14"]
  Column["specific_15"]
  Column["specific_16"]
  Column["specific_17"]
  Column["specific_18"]
  Column["specific_19"]
  Column["specific_20"]
  Column["specific_21"]
  Column["specific_22"]
  Column["specific_23"]
  Column["specific_24"]
  Column["specific_25"]
  Column["specific_26"]
  Column["specific_27"]
  Column["specific_28"]
  Column["specific_29"]
  Column["specific_30"]
  Column["specific_31"]
  Column["specific_32"]
  Column["specific_33"]
  Column["specific_34"]
  Column["specific_35"]

-- ============================================================================
-- CpuCols (132 columns)
-- ============================================================================

#define_subair "CpuCols" using "pico_encapsulation" where
  Column["chunk"]
  Column["clk"]
  Column["clk_16bit_limb"]
  Column["clk_8bit_limb"]
  Column["num_extra_clk"]
  -- pc: Addr<T> = [T; 3]
  Column["pc_0"]
  Column["pc_1"]
  Column["pc_2"]
  -- next_pc: Addr<T> = [T; 3]
  Column["next_pc_0"]
  Column["next_pc_1"]
  Column["next_pc_2"]
  SubAir["instruction": "InstructionCols" width := 14]
  SubAir["opcode_selector": "OpcodeSelectorCols" width := 25]
  SubAir["op_a_access": "MemoryReadWriteCols" width := 13]
  SubAir["op_b_access": "MemoryReadCols" width := 9]
  SubAir["op_c_access": "MemoryReadCols" width := 9]
  SubAir["opcode_specific": "OpcodeSpecificCols" width := 36]
  Column["is_real"]
  Column["branching"]
  Column["not_branching"]
  Column["ecall_mul_send_to_table"]
  Column["ecall_range_check_operand"]
  Column["is_sequential_instr"]
  -- pc_carry_a: [T; 5]
  Column["pc_carry_a_0"]
  Column["pc_carry_a_1"]
  Column["pc_carry_a_2"]
  Column["pc_carry_a_3"]
  Column["pc_carry_a_4"]
  -- pc_carry_b: [T; 4]
  Column["pc_carry_b_0"]
  Column["pc_carry_b_1"]
  Column["pc_carry_b_2"]
  Column["pc_carry_b_3"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "CpuChip" using "pico_encapsulation" where
  MainSubAir["cols": "CpuCols" width := 132]
