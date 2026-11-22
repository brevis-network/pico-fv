import Mathlib

import LeanZKCircuit_Plonky3.Plonky3.Circuit
import LeanZKCircuit_Plonky3.Plonky3.Command.Air.define_air

import PicoFV.RV64IM.Extraction.Attributes
import PicoFV.RV64IM.Airs.Attributes
import PicoFV.RV64IM.Airs.SubAirs
import PicoFV.RV64IM.Airs.U16ToU8GadgetSafe
import PicoFV.RV64IM.Airs.CodeRangeGadget

open Plonky3

set_option linter.unusedVariables false

/-!
# MemoryUnalignedChip (64-bit)

Lean formalisation of `MemoryUnalignedCols` from
`vm/src/chips/chips/riscv_memory/unaligned/columns.rs:21-68` at Pico v3.1.6
(`6aa644efeff9ddbec6beb538200f98f2a70f5d8e`).

This chip receives the same memory dispatch as `MemoryReadWriteChip` and proves the loads and
stores whose address is not a multiple of their width; it is correct for an aligned access too,
so which of the two takes an aligned one changes nothing (`riscv_memory/unaligned/mod.rs:1-6`).
It reads the dword holding the access's first byte at `clk + Memory`, and, when the access runs
past that dword, the next one at `clk + C` (`riscv_memory/unaligned/mod.rs:8-12`).

```rust
pub struct MemoryUnalignedCols<F> {
    pub chunk: F,
    pub clk: F,
    pub addr_word: [F; 2],
    pub addr_limb1_inv: F,
    pub offset: [F; DWORD_BYTES],                    // DWORD_BYTES = 8
    pub cross: F,
    pub next_carry: F,
    pub next_carry_inv: F,
    pub first: MemoryReadWriteLiteCols<F>,           // 10
    pub second: MemoryReadWriteLiteCols<F>,          // 10
    pub first_bytes: U16ToU8Gadget<F>,               //  4
    pub second_bytes: U16ToU8Gadget<F>,              //  4
    pub value_bytes: U16ToU8Gadget<F>,               //  4
    pub seen: Word<F>,                               //  4
    pub seen_byte: F,
    pub sign_src: F,
    pub msb: F,
    pub instruction: MemoryInstructionCols<F>,       // 24
    pub code_range: CodeRangeCols<F>,                //  8
}
```

Layout: 1 + 1 + 2 + 1 + 8 + 1 + 1 + 1 + 10 + 10 + 4 + 4 + 4 + 4 + 1 + 1 + 1 + 24 + 8 = 87
columns, the width `NUM_MEMORY_UNALIGNED_COLS` (`riscv_memory/unaligned/columns.rs:13`) gives and
the extraction at `Extraction/MemoryUnalignedChip.lean` uses. Unlike `MemoryReadWriteChip` there
is no `values` array: the columns are the row.

| columns | name | meaning |
|---------|------|---------|
| 0, 1    | `chunk`, `clk` | the row's chunk and clock, bound to the CPU row by the dispatch |
| 2, 3    | `addr_word_0`, `_1` | the address `b + c`, two 16-bit pieces |
| 4       | `addr_limb1_inv` | inverse of `addr_word_1`: the access is at or above `2^16` |
| 5..12   | `offset_0` … `offset_7` | the address's byte offset in its dword, one-hot |
| 13      | `cross` | the access runs past its dword into the next |
| 14      | `next_carry` | the next dword's address carries into limb 1 |
| 15      | `next_carry_inv` | inverse of the dword's low limb less `0xfff8`, where it does not carry |
| 16..25  | `first.*` | the access to the dword holding the first byte, at `clk + Memory` |
| 26..35  | `second.*` | the access to the next dword, at `clk + C`, on a row that crosses (see below) |
| 36..39  | `first_bytes.low_bytes_0..3` | the low byte of each limb of the first dword's previous value |
| 40..43  | `second_bytes.low_bytes_0..3` | the same for the second dword |
| 44..47  | `value_bytes.low_bytes_0..3` | the low byte of each limb of `op_a`, a store's value |
| 48..51  | `seen_0..3` | the eight bytes from the address on, across the two dwords |
| 52      | `seen_byte` | the first of those bytes, which a byte load reads |
| 53      | `sign_src` | the value whose bit 15 is a signed load's sign |
| 54      | `msb` | a signed load's sign bit; zero on the unsigned loads and on `LD` |
| 55..78  | `instruction.*` | `op_a_0`, the eleven instruction flags and the three operands |
| 79..86  | `code_range.*` | the `code_range` gadget (`Airs/CodeRangeGadget.lean`) |

On a row that does not cross, every message about `second` has multiplicity `cross` and is off,
and no constraint sets the `second` columns to zero: constraints 33 to 35, 48, 50, 52 and 54
relate them to other columns whatever `cross` is. Pico's trace generator leaves them zero: the
trace starts all zero (`riscv_memory/unaligned/traces.rs:54`), and only a row that crosses fills
`second` and `second_bytes` (`riscv_memory/unaligned/traces.rs:186-197`). The constraints do not
enforce it.

`MemoryInstructionCols` is in `Airs/SubAirs.lean`: both memory chips have one, and a chip's
files may not import another chip's.
-/

-- ============================================================================
-- MemoryUnalignedCols (87 columns)
-- ============================================================================

#define_subair "MemoryUnalignedCols" using "pico_encapsulation" where
  Column["chunk"]
  Column["clk"]
  Column["addr_word_0"]
  Column["addr_word_1"]
  Column["addr_limb1_inv"]
  Column["offset_0"]
  Column["offset_1"]
  Column["offset_2"]
  Column["offset_3"]
  Column["offset_4"]
  Column["offset_5"]
  Column["offset_6"]
  Column["offset_7"]
  Column["cross"]
  Column["next_carry"]
  Column["next_carry_inv"]
  SubAir["first": "MemoryReadWriteLiteCols" width := 10]
  SubAir["second": "MemoryReadWriteLiteCols" width := 10]
  SubAir["first_bytes": "U16ToU8Gadget" width := 4]
  SubAir["second_bytes": "U16ToU8Gadget" width := 4]
  SubAir["value_bytes": "U16ToU8Gadget" width := 4]
  Column["seen_0"]
  Column["seen_1"]
  Column["seen_2"]
  Column["seen_3"]
  Column["seen_byte"]
  Column["sign_src"]
  Column["msb"]
  SubAir["instruction": "MemoryInstructionCols" width := 24]
  SubAir["code_range": "CodeRangeGadget" width := 8]

#define_air "MemoryUnalignedChip" using "pico_encapsulation" where
  MainSubAir["cols": "MemoryUnalignedCols" width := 87]
