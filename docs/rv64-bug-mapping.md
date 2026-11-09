# RV64IM soundness gaps and the Pico 3.x constraints that close them

The formalisation of the 2.x series of Pico found 13 soundness gaps in its RV64IM chips
(described in `Report.pdf`, and for the memory chip in
`RV64_MemoryReadWriteChip_soundness_gaps.md`). This table records,
for each gap, the Pico constraint that closes it at the pinned commit
([`2acc7c18`](https://github.com/brevis-network/pico/tree/2acc7c1828fb4ec1bed5963511bb370870c5b608),
v3.1.1), and the extracted constraint and theorem that rely on it. A row is filled when its chip
is moved to the pinned commit (see [`migrating-a-chip.md`](migrating-a-chip.md)). If a gap turns
out not to be closed at the pinned commit, report it privately ([SECURITY.md](../SECURITY.md));
its row stays pending until the gap is fixed or disclosed.

| ID | Chip | Gap in 2.x | Closed by (Pico, pinned commit) | Lean evidence |
|----|------|------------|----------------------------------|---------------|
| LT-1 | `LtChip` | `a[0]` was not constrained to equal `lt_signed.result.bit`, so the SLT result was unwitnessed. | [`alu/lt/constraints.rs:81-82`](https://github.com/brevis-network/pico/blob/2acc7c1828fb4ec1bed5963511bb370870c5b608/vm/src/chips/chips/alu/lt/constraints.rs#L81-L82): `when(is_real).assert_eq(a[0], lt_signed.result.bit)` | `LtChip.Extraction.constraint_32`; used by `LtChip.Spec.spec_SLT` and `spec_SLTU` |
| SR-1 | `ShiftRightChip` | For SRLW/SRAW the output limbs `a[0]`/`a[1]` (the 32-bit result) were free witnesses. | [`alu/sr/constraints.rs:236-256`](https://github.com/brevis-network/pico/blob/2acc7c1828fb4ec1bed5963511bb370870c5b608/vm/src/chips/chips/alu/sr/constraints.rs#L236-L256): on word rows, `when(is_word).when(shift_u16[i])` sets `a[0]`/`a[1]`: for a shift below 16 to `limb_result[0]` and `higher_limb[1]` plus the sign correction, for a shift of 16 to 31 to `higher_limb[1]` plus the sign correction and the sign fill `b_msb * 0xFFFF` | `ShiftRightChip.Extraction.constraint_59` to `constraint_62`; used by `ShiftRightChip.Spec.spec_SRLW` and `spec_SRAW` |
| SR-2 | `ShiftRightChip` | The `lower_limb[i]` / `higher_limb[i]` decomposition was not tied back to `b[i]`. | [`alu/sr/constraints.rs:171-177`](https://github.com/brevis-network/pico/blob/2acc7c1828fb4ec1bed5963511bb370870c5b608/vm/src/chips/chips/alu/sr/constraints.rs#L171-L177): `assert_eq(b[i] * v_0123, higher_limb[i] * 2^16 + lower_limb[i] * v_0123)` for each limb | `ShiftRightChip.Extraction.constraint_26` to `constraint_29`; all four used by `ShiftRightChip.Spec.spec_SRL` and `spec_SRA`, and `constraint_26` and `constraint_27` (the low 32 bits of `b`) by `spec_SRLW` and `spec_SRAW` |
| SR-3 | `ShiftRightChip` | The shift amount `c` and the looked-up `c_for_lookup` were not tied together. | [`alu/sr/constraints.rs:75`](https://github.com/brevis-network/pico/blob/2acc7c1828fb4ec1bed5963511bb370870c5b608/vm/src/chips/chips/alu/sr/constraints.rs#L75): `assert_eq(c, c_for_lookup[0])` | `ShiftRightChip.Extraction.constraint_7`; used by `ShiftRightChip.Spec.spec_SRL`, `spec_SRA`, `spec_SRLW` and `spec_SRAW` |
| SLL-1 | `SLLChip` | `shift_u16` was neither boolean nor tied to `c_bits[4..6]`. | [`alu/sll/constraints.rs:71-77`](https://github.com/brevis-network/pico/blob/2acc7c1828fb4ec1bed5963511bb370870c5b608/vm/src/chips/chips/alu/sll/constraints.rs#L71-L77): `when(shift_u16[i]).assert_eq(c_bits[4] + c_bits[5] * 2 * not_sllw, i)` and `assert_bool(shift_u16[i])`, where `not_sllw = is_sll` | `SLLChip.Extraction.constraint_9` to `constraint_16`: the ties to `c_bits` (`constraint_9`, `_11`, `_13`, `_15`) are used by `SLLChip.Spec.spec_SLL` and `spec_SLLW`, which do not need the booleanity constraints (`_10`, `_12`, `_14`, `_16`) |
| JALR-1 | CPU (`JalrChip` in 2.x) | Bit 0 of the JALR target was not cleared. | pending: part of the CPU move | |
| DR-1 | `DivRemChip` | The `LtWordU16Gadget` call never asserted `bit = 1`, so `|r| < |c|` was absent. | pending | |
| DR-2 | `DivRemChip` | `quot_msb` was a free witness in word operations. | pending | |
| DR-3 | `DivRemChip` | The divisor's upper limbs were unconstrained in word operations. | pending | |
| DR-4 | `DivRemChip` | The dividend's upper limbs were unconstrained in word operations. | pending | |
| MRW-1 | `MemoryReadWriteChip` | No constraint tied the aligned address to `addr_word`. | pending: the chip is rewritten in 3.x | |
| MRW-2 | `MemoryReadWriteChip` | With `op_a_0 = 1` (load into `x0`) the loaded value was unbounded. | pending | |
| MRW-3 | `MemoryReadWriteChip` | For LB/LBU the high byte of the selected limb was not range-checked. | pending | |
