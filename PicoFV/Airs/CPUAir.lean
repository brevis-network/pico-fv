import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import PicoFV.Extraction.Attributes
import PicoFV.Airs.Attributes

set_option linter.unusedVariables false

/-!
# CpuAir

Lean formalisation of the Pico RISC-V CPU chip AIR.

Rust sources:
- CpuCols struct:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_cpu/columns.rs#L21
- InstructionCols:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_cpu/instruction/columns.rs
- OpcodeSelectorCols:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_cpu/opcode_selector/columns.rs
- OpcodeSpecificCols (union, size = JumpCols = 38):
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_cpu/opcode_specific/columns.rs
- MemoryReadWriteCols / MemoryReadCols:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_memory/read_write/columns.rs
- Constraint eval:
  https://github.com/brevis-network/pico/blob/f8617c9c4b540cf31f8b07f6144c93d04799f0f4/vm/src/chips/chips/riscv_cpu/constraints.rs#L26

## Column layout (117 columns total)

| Group                              | Columns | Count |
|------------------------------------|---------|-------|
| Chunk & clock                      | chunk, clk, clk_16bit_limb, clk_8bit_limb | 4 |
| Program counter                    | pc, next_pc | 2 |
| InstructionCols                    | opcode, a_{0..3}, b_{0..3}, c_{0..3}, a_is_0 | 14 |
| OpcodeSelectorCols                 | imm_b, imm_c, is_alu, is_ecall, is_{lb..sw}, is_{beq..bgeu}, is_jalr, is_jal, is_auipc, is_unimpl | 22 |
| MemoryReadWriteCols (op_a_access)  | prev_value_{0..3}, access.{value_{0..3}, prev_chunk, prev_clk, compare_clk, diff_16bit_limb, diff_8bit_limb} | 13 |
| MemoryAccessCols (op_b_access)     | value_{0..3}, prev_chunk, prev_clk, compare_clk, diff_16bit_limb, diff_8bit_limb | 9 |
| MemoryAccessCols (op_c_access)     | value_{0..3}, prev_chunk, prev_clk, compare_clk, diff_16bit_limb, diff_8bit_limb | 9 |
| OpcodeSpecificCols (opaque array)  | specific_{0..37} | 38 |
| Control flags                      | is_real, branching, not_branching, ecall_mul_send_to_table, ecall_range_check_operand, is_sequential_instr | 6 |

## OpcodeSpecificCols

In Rust this is a `union` of BranchCols (31), JumpCols (38), AuipcCols (14), EcallCols (32).
The largest member is JumpCols at 38 elements. We model it as an opaque array of 38 elements;
each constraint helper file interprets the relevant subset.

### BranchCols flat layout (31 columns)

| Offset | Field | Size |
|--------|-------|------|
| 0..3   | pc (Word) | 4 |
| 4..11  | pc_range_checker.most_sig_byte_decomp | 8 |
| 12     | pc_range_checker.upper_all_one.inverse | 1 |
| 13     | pc_range_checker.upper_all_one.result | 1 |
| 14..17 | next_pc (Word) | 4 |
| 18..25 | next_pc_range_checker.most_sig_byte_decomp | 8 |
| 26     | next_pc_range_checker.upper_all_one.inverse | 1 |
| 27     | next_pc_range_checker.upper_all_one.result | 1 |
| 28     | a_eq_b | 1 |
| 29     | a_gt_b | 1 |
| 30     | a_lt_b | 1 |

### JumpCols flat layout (38 columns)

| Offset | Field | Size |
|--------|-------|------|
| 0..3   | pc (Word) | 4 |
| 4..13  | pc_range_checker (FieldWordRangeChecker) | 10 |
| 14..17 | next_pc (Word) | 4 |
| 18..27 | next_pc_range_checker (FieldWordRangeChecker) | 10 |
| 28..37 | op_a_range_checker (FieldWordRangeChecker) | 10 |

### AuipcCols flat layout (14 columns)

| Offset | Field | Size |
|--------|-------|------|
| 0..3   | pc (Word) | 4 |
| 4..13  | pc_range_checker (FieldWordRangeChecker) | 10 |

### EcallCols flat layout (32 columns)

| Offset | Field | Size |
|--------|-------|------|
| 0..1   | is_enter_unconstrained (IsZeroGadget: inverse, result) | 2 |
| 2..3   | is_hint_len (IsZeroGadget) | 2 |
| 4..5   | is_halt (IsZeroGadget) | 2 |
| 6..7   | is_commit (IsZeroGadget) | 2 |
| 8..9   | is_commit_deferred_proofs (IsZeroGadget) | 2 |
| 10..17 | index_bitmap (PV_DIGEST_NUM_WORDS = 8) | 8 |
| 18..25 | operand_range_check_cols.most_sig_byte_decomp | 8 |
| 26     | operand_range_check_cols.upper_all_one.inverse | 1 |
| 27     | operand_range_check_cols.upper_all_one.result | 1 |
| 28..31 | operand_to_check (Word) | 4 |
-/

-- ============================================================================
-- Sub-air definitions
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

-- Rust: InstructionCols (14 columns)
-- Fields: opcode, op_a (Word = 4), op_b (Word = 4), op_c (Word = 4), op_a_0 (is x0 flag)
#define_subair "InstructionCols" using "pico_encapsulation" where
  Column["opcode"]
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  Column["a_is_0"]

-- Rust: OpcodeSelectorCols (22 columns)
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
  Column["is_sb"]
  Column["is_sh"]
  Column["is_sw"]
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

-- Rust: OpcodeSpecificCols (38 columns, opaque array)
-- Union of BranchCols (31), JumpCols (38), AuipcCols (14), EcallCols (32).
-- Modelled as flat array; constraint helpers interpret the relevant subset.
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
  Column["specific_36"]
  Column["specific_37"]

-- ============================================================================
-- CpuCols (117 columns total)
-- ============================================================================

#define_subair "CpuCols" using "pico_encapsulation" where
  Column["chunk"]
  Column["clk"]
  Column["clk_16bit_limb"]
  Column["clk_8bit_limb"]
  Column["pc"]
  Column["next_pc"]
  SubAir["instruction": "InstructionCols" width := 14]
  SubAir["opcode_selector": "OpcodeSelectorCols" width := 22]
  SubAir["op_a_access": "MemoryReadWriteCols" width := 13]
  SubAir["op_b_access": "MemoryAccessCols" width := 9]
  SubAir["op_c_access": "MemoryAccessCols" width := 9]
  SubAir["opcode_specific": "OpcodeSpecificCols" width := 38]
  Column["is_real"]
  Column["branching"]
  Column["not_branching"]
  Column["ecall_mul_send_to_table"]
  Column["ecall_range_check_operand"]
  Column["is_sequential_instr"]

-- ============================================================================
-- Air definition
-- ============================================================================

#define_air "CpuAir" using "pico_encapsulation" where
  MainSubAir["cols": "CpuCols" width := 117]

-- ============================================================================
-- Instruction classification flags
-- Rust: CpuAir::is_alu_instruction, is_memory_instruction, is_store_instruction
-- ============================================================================

def Valid_CpuCols.is_memory_instruction
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
: F :=
  c.opcode_selector.is_lb row rotation +
  c.opcode_selector.is_lbu row rotation +
  c.opcode_selector.is_lh row rotation +
  c.opcode_selector.is_lhu row rotation +
  c.opcode_selector.is_lw row rotation +
  c.opcode_selector.is_sb row rotation +
  c.opcode_selector.is_sh row rotation +
  c.opcode_selector.is_sw row rotation

@[pico_encapsulation]
lemma CpuCols.is_memory_instruction_def
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
:
  c.opcode_selector.is_lb row rotation +
  c.opcode_selector.is_lbu row rotation +
  c.opcode_selector.is_lh row rotation +
  c.opcode_selector.is_lhu row rotation +
  c.opcode_selector.is_lw row rotation +
  c.opcode_selector.is_sb row rotation +
  c.opcode_selector.is_sh row rotation +
  c.opcode_selector.is_sw row rotation =
  c.is_memory_instruction row rotation
:= rfl

def Valid_CpuCols.is_branch_instruction
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
: F :=
  c.opcode_selector.is_beq row rotation +
  c.opcode_selector.is_bne row rotation +
  c.opcode_selector.is_blt row rotation +
  c.opcode_selector.is_bge row rotation +
  c.opcode_selector.is_bltu row rotation +
  c.opcode_selector.is_bgeu row rotation

@[pico_encapsulation]
lemma CpuCols.is_branch_instruction_def
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
:
  c.opcode_selector.is_beq row rotation +
  c.opcode_selector.is_bne row rotation +
  c.opcode_selector.is_blt row rotation +
  c.opcode_selector.is_bge row rotation +
  c.opcode_selector.is_bltu row rotation +
  c.opcode_selector.is_bgeu row rotation =
  c.is_branch_instruction row rotation
:= rfl

def Valid_CpuCols.is_store_instruction
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
: F :=
  c.opcode_selector.is_sb row rotation +
  c.opcode_selector.is_sh row rotation +
  c.opcode_selector.is_sw row rotation

@[pico_encapsulation]
lemma CpuCols.is_store_instruction_def
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
:
  c.opcode_selector.is_sb row rotation +
  c.opcode_selector.is_sh row rotation +
  c.opcode_selector.is_sw row rotation =
  c.is_store_instruction row rotation
:= rfl

-- Rust: CpuAir::is_alu_instruction (simply opcode_selector.is_alu)
def Valid_CpuCols.is_alu_instruction
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
: F :=
  c.opcode_selector.is_alu row rotation

@[pico_encapsulation]
lemma CpuCols.is_alu_instruction_def
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
:
  c.opcode_selector.is_alu row rotation =
  c.is_alu_instruction row rotation
:= rfl

-- Rust: jump/constraints.rs — is_jal + is_jalr
def Valid_CpuCols.is_jump_instruction
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
: F :=
  c.opcode_selector.is_jal row rotation +
  c.opcode_selector.is_jalr row rotation

@[pico_encapsulation]
lemma CpuCols.is_jump_instruction_def
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
:
  c.opcode_selector.is_jal row rotation +
  c.opcode_selector.is_jalr row rotation =
  c.is_jump_instruction row rotation
:= rfl

-- Rust: branch/constraints.rs — is_blt + is_bge
def Valid_CpuCols.use_signed_comparison
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
: F :=
  c.opcode_selector.is_blt row rotation +
  c.opcode_selector.is_bge row rotation

@[pico_encapsulation]
lemma CpuCols.use_signed_comparison_def
  [Field F]
  (c : Valid_CpuCols F) (row rotation : ℕ)
:
  c.opcode_selector.is_blt row rotation +
  c.opcode_selector.is_bge row rotation =
  c.use_signed_comparison row rotation
:= rfl

-- ============================================================================
-- OpcodeSpecificCols: BranchCols interpretation (specific_0..30)
-- Rust: branch/columns.rs — BranchCols<T>
-- Layout: pc(4), pc_range_checker(10), next_pc(4), next_pc_range_checker(10),
--         a_eq_b(1), a_gt_b(1), a_lt_b(1) = 31
-- ============================================================================

def Valid_CpuCols.branch_pc (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.opcode_specific.specific_0 row rotation
  | 1 => c.opcode_specific.specific_1 row rotation
  | 2 => c.opcode_specific.specific_2 row rotation
  | 3 => c.opcode_specific.specific_3 row rotation

def Valid_CpuCols.branch_next_pc (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.opcode_specific.specific_14 row rotation
  | 1 => c.opcode_specific.specific_15 row rotation
  | 2 => c.opcode_specific.specific_16 row rotation
  | 3 => c.opcode_specific.specific_17 row rotation

def Valid_CpuCols.branch_a_eq_b
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_28 row rotation

def Valid_CpuCols.branch_a_gt_b
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_29 row rotation

def Valid_CpuCols.branch_a_lt_b
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_30 row rotation

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_pc_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_0 row rotation = c.branch_pc 0 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_pc_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_1 row rotation = c.branch_pc 1 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_pc_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_2 row rotation = c.branch_pc 2 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_pc_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_3 row rotation = c.branch_pc 3 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_next_pc_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_14 row rotation = c.branch_next_pc 0 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_next_pc_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_15 row rotation = c.branch_next_pc 1 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_next_pc_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_16 row rotation = c.branch_next_pc 2 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_next_pc_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_17 row rotation = c.branch_next_pc 3 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_a_eq_b_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_28 row rotation = c.branch_a_eq_b row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_a_gt_b_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_29 row rotation = c.branch_a_gt_b row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuCols.branch_a_lt_b_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_30 row rotation = c.branch_a_lt_b row rotation := rfl

-- ============================================================================
-- OpcodeSpecificCols: JumpCols interpretation (specific_0..37)
-- Rust: jump/columns.rs — JumpCols<T>
-- Layout: pc(4), pc_range_checker(10), next_pc(4), next_pc_range_checker(10),
--         op_a_range_checker(10) = 38
-- Note: pc and next_pc share the same offsets as BranchCols.
-- ============================================================================

-- jump_pc and jump_next_pc alias branch_pc and branch_next_pc (same offsets 0..3, 14..17)
abbrev Valid_CpuCols.jump_pc := @Valid_CpuCols.branch_pc
abbrev Valid_CpuCols.jump_next_pc := @Valid_CpuCols.branch_next_pc

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_pc_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_0 row rotation = c.jump_pc 0 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_pc_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_1 row rotation = c.jump_pc 1 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_pc_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_2 row rotation = c.jump_pc 2 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_pc_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_3 row rotation = c.jump_pc 3 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_next_pc_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_14 row rotation = c.jump_next_pc 0 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_next_pc_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_15 row rotation = c.jump_next_pc 1 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_next_pc_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_16 row rotation = c.jump_next_pc 2 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuCols.jump_next_pc_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_17 row rotation = c.jump_next_pc 3 row rotation := rfl

-- ============================================================================
-- OpcodeSpecificCols: AuipcCols interpretation (specific_0..13)
-- Rust: auipc/columns.rs — AuipcCols<T>
-- Layout: pc(4), pc_range_checker(10) = 14
-- Note: pc shares the same offsets as BranchCols/JumpCols.
-- ============================================================================

-- auipc_pc aliases branch_pc (same offsets 0..3)
abbrev Valid_CpuCols.auipc_pc := @Valid_CpuCols.branch_pc

@[cpu_auipc_cols_simplification]
lemma CpuCols.auipc_pc_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_0 row rotation = c.auipc_pc 0 row rotation := rfl

@[cpu_auipc_cols_simplification]
lemma CpuCols.auipc_pc_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_1 row rotation = c.auipc_pc 1 row rotation := rfl

@[cpu_auipc_cols_simplification]
lemma CpuCols.auipc_pc_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_2 row rotation = c.auipc_pc 2 row rotation := rfl

@[cpu_auipc_cols_simplification]
lemma CpuCols.auipc_pc_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_3 row rotation = c.auipc_pc 3 row rotation := rfl

-- ============================================================================
-- OpcodeSpecificCols: EcallCols interpretation (specific_0..31)
-- Rust: ecall/columns.rs — EcallCols<T>
-- Layout: is_enter_unconstrained(2), is_hint_len(2), is_halt(2), is_commit(2),
--         is_commit_deferred_proofs(2), index_bitmap(8),
--         operand_range_check_cols(10), operand_to_check(4) = 32
-- Each IsZeroGadget = (inverse, result), so result is at odd offsets.
-- ============================================================================

-- IsZeroGadget results (the boolean outputs)
def Valid_CpuCols.ecall_is_enter_unconstrained
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_1 row rotation

def Valid_CpuCols.ecall_is_hint_len
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_3 row rotation

def Valid_CpuCols.ecall_is_halt
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_5 row rotation

def Valid_CpuCols.ecall_is_commit
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_7 row rotation

def Valid_CpuCols.ecall_is_commit_deferred_proofs
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_9 row rotation

-- IsZeroGadget inverses
def Valid_CpuCols.ecall_is_enter_unconstrained_inv
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_0 row rotation

def Valid_CpuCols.ecall_is_hint_len_inv
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_2 row rotation

def Valid_CpuCols.ecall_is_halt_inv
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_4 row rotation

def Valid_CpuCols.ecall_is_commit_inv
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_6 row rotation

def Valid_CpuCols.ecall_is_commit_deferred_proofs_inv
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_8 row rotation

-- index_bitmap[0..7] at specific_10..17
def Valid_CpuCols.ecall_index_bitmap (i : Fin 8)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.opcode_specific.specific_10 row rotation
  | 1 => c.opcode_specific.specific_11 row rotation
  | 2 => c.opcode_specific.specific_12 row rotation
  | 3 => c.opcode_specific.specific_13 row rotation
  | 4 => c.opcode_specific.specific_14 row rotation
  | 5 => c.opcode_specific.specific_15 row rotation
  | 6 => c.opcode_specific.specific_16 row rotation
  | 7 => c.opcode_specific.specific_17 row rotation

-- operand_to_check (Word) at specific_28..31
def Valid_CpuCols.ecall_operand_to_check (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.opcode_specific.specific_28 row rotation
  | 1 => c.opcode_specific.specific_29 row rotation
  | 2 => c.opcode_specific.specific_30 row rotation
  | 3 => c.opcode_specific.specific_31 row rotation

-- IsZeroGadget inverse folding lemmas
@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_enter_unconstrained_inv_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_0 row rotation = c.ecall_is_enter_unconstrained_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_enter_unconstrained_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_1 row rotation = c.ecall_is_enter_unconstrained row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_hint_len_inv_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_2 row rotation = c.ecall_is_hint_len_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_hint_len_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_3 row rotation = c.ecall_is_hint_len row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_halt_inv_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_4 row rotation = c.ecall_is_halt_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_halt_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_5 row rotation = c.ecall_is_halt row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_commit_inv_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_6 row rotation = c.ecall_is_commit_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_commit_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_7 row rotation = c.ecall_is_commit row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_commit_deferred_proofs_inv_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_8 row rotation = c.ecall_is_commit_deferred_proofs_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_is_commit_deferred_proofs_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_9 row rotation = c.ecall_is_commit_deferred_proofs row rotation := rfl

-- index_bitmap folding lemmas
@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_10 row rotation = c.ecall_index_bitmap 0 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_11 row rotation = c.ecall_index_bitmap 1 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_12 row rotation = c.ecall_index_bitmap 2 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_13 row rotation = c.ecall_index_bitmap 3 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_4_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_14 row rotation = c.ecall_index_bitmap 4 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_5_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_15 row rotation = c.ecall_index_bitmap 5 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_6_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_16 row rotation = c.ecall_index_bitmap 6 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_index_bitmap_7_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_17 row rotation = c.ecall_index_bitmap 7 row rotation := rfl

-- operand_to_check folding lemmas
@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_operand_to_check_0_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_28 row rotation = c.ecall_operand_to_check 0 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_operand_to_check_1_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_29 row rotation = c.ecall_operand_to_check 1 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_operand_to_check_2_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_30 row rotation = c.ecall_operand_to_check 2 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_operand_to_check_3_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_31 row rotation = c.ecall_operand_to_check 3 row rotation := rfl

-- ============================================================================
-- Syscall-derived computed values
-- Rust: ecall/constraints.rs
-- syscall_code = op_a_access.prev_value(), interpreted as LE bytes:
--   byte 0 = syscall_id, byte 1 = send_to_table, byte 2 = num_extra_cycles
-- ============================================================================

-- Rust: syscall_id = syscall_code[0] = op_a_access.prev_value_0
def Valid_CpuCols.syscall_id
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.op_a_access.prev_value_0 row rotation

@[cpu_syscall_derived_simplification]
lemma CpuCols.syscall_id_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.op_a_access.prev_value_0 row rotation = c.syscall_id row rotation := rfl

-- Rust: send_to_table = syscall_code[1] = op_a_access.prev_value_1
def Valid_CpuCols.send_to_table
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.op_a_access.prev_value_1 row rotation

@[cpu_syscall_derived_simplification]
lemma CpuCols.send_to_table_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.op_a_access.prev_value_1 row rotation = c.send_to_table row rotation := rfl

-- Rust: num_extra_cycles = syscall_code[2] * is_ecall
-- (only nonzero when the instruction is an ecall)
def Valid_CpuCols.num_extra_cycles
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.op_a_access.prev_value_2 row rotation *
  c.opcode_selector.is_ecall row rotation

@[cpu_syscall_derived_simplification]
lemma CpuCols.num_extra_cycles_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.op_a_access.prev_value_2 row rotation *
  c.opcode_selector.is_ecall row rotation =
  c.num_extra_cycles row rotation := rfl

-- Rust: is_halt (in constraint context) = ecall_is_halt.result * is_ecall
def Valid_CpuCols.is_halt
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.ecall_is_halt row rotation *
  c.opcode_selector.is_ecall row rotation

@[cpu_syscall_derived_simplification]
lemma CpuCols.is_halt_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.ecall_is_halt row rotation *
  c.opcode_selector.is_ecall row rotation =
  c.is_halt row rotation := rfl

-- ============================================================================
-- Clock derived values
-- Rust: chunk_clk/constraints.rs
-- ============================================================================

-- Rust: expected_next_clk = clk + 4 + num_extra_cycles
def Valid_CpuCols.expected_next_clk
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.clk row rotation + 4 + c.num_extra_cycles row rotation

@[cpu_syscall_derived_simplification]
lemma CpuCols.expected_next_clk_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.clk row rotation + 4 + c.num_extra_cycles row rotation =
  c.expected_next_clk row rotation := rfl

-- ============================================================================
-- Commit derived values
-- Rust: ecall/constraints.rs — eval_commit
-- ============================================================================

-- Rust: bitmap_sum = sum of index_bitmap[0..7]
def Valid_CpuCols.ecall_bitmap_sum
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.opcode_specific.specific_10 row rotation +
  c.opcode_specific.specific_11 row rotation +
  c.opcode_specific.specific_12 row rotation +
  c.opcode_specific.specific_13 row rotation +
  c.opcode_specific.specific_14 row rotation +
  c.opcode_specific.specific_15 row rotation +
  c.opcode_specific.specific_16 row rotation +
  c.opcode_specific.specific_17 row rotation

@[cpu_ecall_cols_simplification]
lemma CpuCols.ecall_bitmap_sum_def [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) :
  c.opcode_specific.specific_10 row rotation +
  c.opcode_specific.specific_11 row rotation +
  c.opcode_specific.specific_12 row rotation +
  c.opcode_specific.specific_13 row rotation +
  c.opcode_specific.specific_14 row rotation +
  c.opcode_specific.specific_15 row rotation +
  c.opcode_specific.specific_16 row rotation +
  c.opcode_specific.specific_17 row rotation =
  c.ecall_bitmap_sum row rotation := rfl

-- ============================================================================
-- Word value accessors
-- Rust: CpuCols methods op_a_val(), op_b_val(), op_c_val()
-- op_a_val() = op_a_access.access.value (the current value in the read-write slot)
-- op_b_val() = op_b_access.value (read-only slot)
-- op_c_val() = op_c_access.value (read-only slot)
-- ============================================================================

def Valid_CpuCols.op_a_val (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.op_a_access.access.value_0 row rotation
  | 1 => c.op_a_access.access.value_1 row rotation
  | 2 => c.op_a_access.access.value_2 row rotation
  | 3 => c.op_a_access.access.value_3 row rotation

def Valid_CpuCols.op_b_val (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.op_b_access.value_0 row rotation
  | 1 => c.op_b_access.value_1 row rotation
  | 2 => c.op_b_access.value_2 row rotation
  | 3 => c.op_b_access.value_3 row rotation

def Valid_CpuCols.op_c_val (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.op_c_access.value_0 row rotation
  | 1 => c.op_c_access.value_1 row rotation
  | 2 => c.op_c_access.value_2 row rotation
  | 3 => c.op_c_access.value_3 row rotation

-- Rust: Word::reduce() = limb[0] + limb[1]*2^8 + limb[2]*2^16 + limb[3]*2^24
def Valid_CpuCols.op_a_val_reduce
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.op_a_val 0 row rotation +
  c.op_a_val 1 row rotation * 256 +
  c.op_a_val 2 row rotation * 65536 +
  c.op_a_val 3 row rotation * 16777216

def Valid_CpuCols.op_b_val_reduce
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.op_b_val 0 row rotation +
  c.op_b_val 1 row rotation * 256 +
  c.op_b_val 2 row rotation * 65536 +
  c.op_b_val 3 row rotation * 16777216

def Valid_CpuCols.op_c_val_reduce
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.op_c_val 0 row rotation +
  c.op_c_val 1 row rotation * 256 +
  c.op_c_val 2 row rotation * 65536 +
  c.op_c_val 3 row rotation * 16777216

-- Rust: op_a_access.prev_value() (the value before the write)
def Valid_CpuCols.op_a_prev_val (i : Fin 4)
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  match i with
  | 0 => c.op_a_access.prev_value_0 row rotation
  | 1 => c.op_a_access.prev_value_1 row rotation
  | 2 => c.op_a_access.prev_value_2 row rotation
  | 3 => c.op_a_access.prev_value_3 row rotation

-- Rust: branch_cols.pc.reduce() / jump_columns.pc.reduce() / auipc_columns.pc.reduce()
def Valid_CpuCols.branch_pc_reduce
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.branch_pc 0 row rotation +
  c.branch_pc 1 row rotation * 256 +
  c.branch_pc 2 row rotation * 65536 +
  c.branch_pc 3 row rotation * 16777216

def Valid_CpuCols.branch_next_pc_reduce
  [Field F] (c : Valid_CpuCols F) (row rotation : ℕ) : F :=
  c.branch_next_pc 0 row rotation +
  c.branch_next_pc 1 row rotation * 256 +
  c.branch_next_pc 2 row rotation * 65536 +
  c.branch_next_pc 3 row rotation * 16777216

-- jump_pc_reduce and auipc_pc_reduce are the same as branch_pc_reduce (same offsets)
abbrev Valid_CpuCols.jump_pc_reduce := @Valid_CpuCols.branch_pc_reduce
abbrev Valid_CpuCols.jump_next_pc_reduce := @Valid_CpuCols.branch_next_pc_reduce
abbrev Valid_CpuCols.auipc_pc_reduce := @Valid_CpuCols.branch_pc_reduce

-- ============================================================================
-- Lifted CpuCols lemmas to CpuAir level
-- These are the same folding lemmas but operating on air.cols instead of c
-- ============================================================================

@[pico_encapsulation]
lemma CpuAir.is_memory_instruction_def
  [Field F] [Field ExtF]
  (air : Valid_CpuAir F ExtF) (row rotation : ℕ)
:
  air.cols.opcode_selector.is_lb row rotation +
  air.cols.opcode_selector.is_lbu row rotation +
  air.cols.opcode_selector.is_lh row rotation +
  air.cols.opcode_selector.is_lhu row rotation +
  air.cols.opcode_selector.is_lw row rotation +
  air.cols.opcode_selector.is_sb row rotation +
  air.cols.opcode_selector.is_sh row rotation +
  air.cols.opcode_selector.is_sw row rotation =
  air.cols.is_memory_instruction row rotation
:= rfl

@[pico_encapsulation]
lemma CpuAir.is_branch_instruction_def
  [Field F] [Field ExtF]
  (air : Valid_CpuAir F ExtF) (row rotation : ℕ)
:
  air.cols.opcode_selector.is_beq row rotation +
  air.cols.opcode_selector.is_bne row rotation +
  air.cols.opcode_selector.is_blt row rotation +
  air.cols.opcode_selector.is_bge row rotation +
  air.cols.opcode_selector.is_bltu row rotation +
  air.cols.opcode_selector.is_bgeu row rotation =
  air.cols.is_branch_instruction row rotation
:= rfl

@[pico_encapsulation]
lemma CpuAir.is_store_instruction_def
  [Field F] [Field ExtF]
  (air : Valid_CpuAir F ExtF) (row rotation : ℕ)
:
  air.cols.opcode_selector.is_sb row rotation +
  air.cols.opcode_selector.is_sh row rotation +
  air.cols.opcode_selector.is_sw row rotation =
  air.cols.is_store_instruction row rotation
:= rfl

@[pico_encapsulation]
lemma CpuAir.is_alu_instruction_def
  [Field F] [Field ExtF]
  (air : Valid_CpuAir F ExtF) (row rotation : ℕ)
:
  air.cols.opcode_selector.is_alu row rotation =
  air.cols.is_alu_instruction row rotation
:= rfl

@[pico_encapsulation]
lemma CpuAir.is_jump_instruction_def
  [Field F] [Field ExtF]
  (air : Valid_CpuAir F ExtF) (row rotation : ℕ)
:
  air.cols.opcode_selector.is_jal row rotation +
  air.cols.opcode_selector.is_jalr row rotation =
  air.cols.is_jump_instruction row rotation
:= rfl

@[pico_encapsulation]
lemma CpuAir.use_signed_comparison_def
  [Field F] [Field ExtF]
  (air : Valid_CpuAir F ExtF) (row rotation : ℕ)
:
  air.cols.opcode_selector.is_blt row rotation +
  air.cols.opcode_selector.is_bge row rotation =
  air.cols.use_signed_comparison row rotation
:= rfl

-- ============================================================================
-- BranchCols interpretation
-- ============================================================================

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_pc_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_0 row rotation = air.cols.branch_pc 0 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_pc_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_1 row rotation = air.cols.branch_pc 1 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_pc_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_2 row rotation = air.cols.branch_pc 2 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_pc_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_3 row rotation = air.cols.branch_pc 3 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_next_pc_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_14 row rotation = air.cols.branch_next_pc 0 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_next_pc_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_15 row rotation = air.cols.branch_next_pc 1 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_next_pc_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_16 row rotation = air.cols.branch_next_pc 2 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_next_pc_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_17 row rotation = air.cols.branch_next_pc 3 row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_a_eq_b_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_28 row rotation = air.cols.branch_a_eq_b row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_a_gt_b_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_29 row rotation = air.cols.branch_a_gt_b row rotation := rfl

@[cpu_branch_cols_simplification]
lemma CpuAir.branch_a_lt_b_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_30 row rotation = air.cols.branch_a_lt_b row rotation := rfl

-- ============================================================================
-- JumpCols interpretation
-- ============================================================================

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_pc_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_0 row rotation = air.cols.jump_pc 0 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_pc_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_1 row rotation = air.cols.jump_pc 1 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_pc_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_2 row rotation = air.cols.jump_pc 2 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_pc_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_3 row rotation = air.cols.jump_pc 3 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_next_pc_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_14 row rotation = air.cols.jump_next_pc 0 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_next_pc_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_15 row rotation = air.cols.jump_next_pc 1 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_next_pc_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_16 row rotation = air.cols.jump_next_pc 2 row rotation := rfl

@[cpu_jump_cols_simplification]
lemma CpuAir.jump_next_pc_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_17 row rotation = air.cols.jump_next_pc 3 row rotation := rfl

-- ============================================================================
-- AuipcCols interpretation
-- ============================================================================

@[cpu_auipc_cols_simplification]
lemma CpuAir.auipc_pc_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_0 row rotation = air.cols.auipc_pc 0 row rotation := rfl

@[cpu_auipc_cols_simplification]
lemma CpuAir.auipc_pc_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_1 row rotation = air.cols.auipc_pc 1 row rotation := rfl

@[cpu_auipc_cols_simplification]
lemma CpuAir.auipc_pc_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_2 row rotation = air.cols.auipc_pc 2 row rotation := rfl

@[cpu_auipc_cols_simplification]
lemma CpuAir.auipc_pc_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_3 row rotation = air.cols.auipc_pc 3 row rotation := rfl

-- ============================================================================
-- EcallCols interpretation
-- ============================================================================

-- IsZeroGadget inverse folding lemmas
@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_enter_unconstrained_inv_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_0 row rotation = air.cols.ecall_is_enter_unconstrained_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_enter_unconstrained_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_1 row rotation = air.cols.ecall_is_enter_unconstrained row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_hint_len_inv_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_2 row rotation = air.cols.ecall_is_hint_len_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_hint_len_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_3 row rotation = air.cols.ecall_is_hint_len row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_halt_inv_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_4 row rotation = air.cols.ecall_is_halt_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_halt_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_5 row rotation = air.cols.ecall_is_halt row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_commit_inv_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_6 row rotation = air.cols.ecall_is_commit_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_commit_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_7 row rotation = air.cols.ecall_is_commit row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_commit_deferred_proofs_inv_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_8 row rotation = air.cols.ecall_is_commit_deferred_proofs_inv row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_is_commit_deferred_proofs_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_9 row rotation = air.cols.ecall_is_commit_deferred_proofs row rotation := rfl

-- index_bitmap folding lemmas
@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_10 row rotation = air.cols.ecall_index_bitmap 0 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_11 row rotation = air.cols.ecall_index_bitmap 1 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_12 row rotation = air.cols.ecall_index_bitmap 2 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_13 row rotation = air.cols.ecall_index_bitmap 3 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_4_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_14 row rotation = air.cols.ecall_index_bitmap 4 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_5_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_15 row rotation = air.cols.ecall_index_bitmap 5 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_6_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_16 row rotation = air.cols.ecall_index_bitmap 6 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_index_bitmap_7_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_17 row rotation = air.cols.ecall_index_bitmap 7 row rotation := rfl

-- operand_to_check folding lemmas
@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_operand_to_check_0_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_28 row rotation = air.cols.ecall_operand_to_check 0 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_operand_to_check_1_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_29 row rotation = air.cols.ecall_operand_to_check 1 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_operand_to_check_2_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_30 row rotation = air.cols.ecall_operand_to_check 2 row rotation := rfl

@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_operand_to_check_3_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_31 row rotation = air.cols.ecall_operand_to_check 3 row rotation := rfl

-- bitmap_sum folding lemma
@[cpu_ecall_cols_simplification]
lemma CpuAir.ecall_bitmap_sum_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.opcode_specific.specific_10 row rotation +
  air.cols.opcode_specific.specific_11 row rotation +
  air.cols.opcode_specific.specific_12 row rotation +
  air.cols.opcode_specific.specific_13 row rotation +
  air.cols.opcode_specific.specific_14 row rotation +
  air.cols.opcode_specific.specific_15 row rotation +
  air.cols.opcode_specific.specific_16 row rotation +
  air.cols.opcode_specific.specific_17 row rotation =
  air.cols.ecall_bitmap_sum row rotation := rfl

-- ============================================================================
-- Syscall-derived computed values
-- ============================================================================

@[cpu_syscall_derived_simplification]
lemma CpuAir.syscall_id_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.op_a_access.prev_value_0 row rotation = air.cols.syscall_id row rotation := rfl

@[cpu_syscall_derived_simplification]
lemma CpuAir.send_to_table_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.op_a_access.prev_value_1 row rotation = air.cols.send_to_table row rotation := rfl

@[cpu_syscall_derived_simplification]
lemma CpuAir.num_extra_cycles_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.op_a_access.prev_value_2 row rotation *
  air.cols.opcode_selector.is_ecall row rotation =
  air.cols.num_extra_cycles row rotation := rfl

@[cpu_syscall_derived_simplification]
lemma CpuAir.is_halt_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.ecall_is_halt row rotation *
  air.cols.opcode_selector.is_ecall row rotation =
  air.cols.is_halt row rotation := rfl

@[cpu_syscall_derived_simplification]
lemma CpuAir.expected_next_clk_def [Field F] [Field ExtF] (air : Valid_CpuAir F ExtF) (row rotation : ℕ) :
  air.cols.clk row rotation + 4 + air.cols.num_extra_cycles row rotation =
  air.cols.expected_next_clk row rotation := rfl
