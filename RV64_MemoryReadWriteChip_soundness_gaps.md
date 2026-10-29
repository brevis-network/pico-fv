# RV64IM `MemoryReadWriteChip` — soundness gaps

> The RV32IM files cited below are no longer in this repository; read them at
> [NethermindEth/pico-fv@a7f9a09](https://github.com/NethermindEth/pico-fv/tree/a7f9a0976e245aeef89c3f02c51ae85023207b53).

**Context:** Formal verification of the Pico RV64IM `MemoryReadWriteChip` in Lean 4. This document summarizes three soundness gaps surfaced while proving (a) each opcode's spec (`spec_<OP>`) and (b) the State-bus ↔ Memory-bus equivalence (`bus_equiv`). Each is a missing chip-side constraint, **not** a Lean proof artifact. In every case, the analogous RV32IM chip is correct; RV64IM dropped or never added the constraint.

**Audience:** Pico / Brevis developers maintaining the chip.

**Date:** 2026-06-03 (original report); updated 2026-06-04.

---

## Status — ALL THREE RESOLVED upstream

All three gaps were addressed on 2026-06-04 by Pico PR #101 commits:

| # | Gap | Fix commit | Pico approach |
|---|-----|------------|---------------|
| 1 | `addr_aligned` not tied to `addr_word` | `db682d9c` | Removes the `addr_aligned` witness column entirely; aligned address now computed inline as `[addr_word[0] - offset_sum, addr_word[1], addr_word[2]]` in the State-bus and Memory-bus lookups |
| 2 | `op_a` payload unconstrained on rd = x0 | `7860af12` | Adds the exact 4 constraints proposed below: `op_a_0 · op_a_val[i] = 0` for i = 0..3 |
| 3 | LB/LBU high byte of `selected_limb` not bounded | `fc197c0b` | Replaces single-byte `slice_range_check_u8` with `looking_rangecheck(U8Range, ..., low_byte, high_byte, ...)`, both bytes range-checked — exactly the SB-mirror approach proposed below |

A column-layout refactor `0ecd943c` also landed on 2026-06-04 streamlining `op_b_access`/`op_c_access` from `MemoryReadCols` to plain `Word<T>` (removes 10 unused metadata cols). The remainder of this document is preserved as the original audit report — the analyses, RV32IM contrasts, and proposed fixes (which were the patches that landed).

---

## Original audit summary

| # | Gap | Affected ops | Lean impact | Fix scope |
|---|-----|--------------|-------------|-----------|
| 1 | `addr_aligned` not tied to `addr_word` | All 11 (loads + stores) | 11 `MISSING_<OP>_addr_aligned` on `bus_equiv_<OP>` | 1 new constraint (gated by `is_load_or_store`) |
| 2 | `op_a` payload unconstrained on rd = x0 | 7 loads (LB/LBU/LH/LHU/LW/LWU/LD) | 1 unprovable wf-assertion conjunct in each load spec | 4 new constraints (`op_a_0 · value_i = 0`) |
| 3 | LB/LBU high byte of `selected_limb` not bounded | LBU (directly), LB (`bus_equiv` only) | 3 MISSINGs across `spec_LBU` + `bus_equiv_LB/LBU` | 1 inline expression change to byte-bus entry 11 |

All three are RV64IM-only; the analogous RV32IM constraints are present and correct. None require new witness columns — only constraint additions or inline expression changes.

---

## Gap 1 — `addr_aligned` is not tied to `addr_word`

**Severity:** High. Any State-bus consumer trusting `addr_aligned` as "the aligned form of `addr_word`" can be spoofed.

### The chip's behavior

The chip emits `addr_aligned_0..2` on the State bus (the 6-byte aligned address used by the `.Double` ReadMem/WriteMem pair on the State bus). However, **no constraint in `c0..c84` references `addr_aligned_*` at all**. Verification:

```
grep -B1 "addr_aligned_" PicoFV/RV64IM/Constraints/MemoryReadWriteChip.lean \
  | grep "def constraint"
```

returns nothing.

A malicious prover can put arbitrary FKB elements into `addr_aligned_0..2`: the State bus will then act on a spoofed aligned address while the Memory bus operates at `addr_word`. The two buses no longer refer to the same 8-byte region.

### RV32IM comparison

`PicoFV/RV32IM/Constraints/MemoryReadWriteAir.lean` line 237 has the analogous constraint:

```
(is_lb + is_lbu + is_lh + is_lhu + is_lw + is_sb + is_sh + is_sw) *
  ((addr_aligned + addr_offset) -
   (1*aw0 + 256*aw1 + 65536*aw2 + 16777216*aw3)) = 0
```

(specialised to a single `addr_aligned` column since RV32IM packs the address in one u32 instead of three u16 limbs).

### Proposed fix (RV64IM)

Add the three-limb version with the alignment offset, gated by `is_load_or_store`:

```
(is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld +
 is_sb + is_sh + is_sw + is_sd) *
  ((addr_aligned_0 + 65536·addr_aligned_1 + 65536²·addr_aligned_2 +
    offset_bit_0 + 2·offset_bit_1 + 4·offset_bit_2) -
   (addr_word_0 + 65536·addr_word_1 + 65536²·addr_word_2 +
    65536³·addr_word_3)) = 0
```

(`c0`'s `addr_word_3 = 0` covers the top limb for `is_mem`.)

Per opcode the offset shape narrows: SD/LD ignore all three `offset_bit_*`, SW/LW/LWU ignore `ob_0` and `ob_1`, SH/LH/LHU ignore `ob_0`, SB/LB/LBU use all three. A single constraint with the full offset expression covers all 11 opcodes (the unused `ob_*` are zero per the per-opcode constraints `c9`, `c10`, etc.).

### Lean-side current workaround

`bus_equiv` in `PicoFV/RV64IM/Spec/MemoryReadWriteChip.lean` is dispatched per opcode. Each `bus_equiv_<OP>` takes a `MISSING_<OP>_addr_aligned` hypothesis with the appropriate per-opcode shape (11 in total). One chip-side fix discharges all of them.

---

## Gap 2 — `op_a` payload unconstrained when destination is `x0`

**Severity:** Medium-low in practice (RISC-V semantics make `x0` writes no-ops and the CpuChip pins `x0 = 0` via its own State-bus emission), but the chip cannot discharge its wf-assertion side of the Memory bus contract on paper.

### The chip's behavior

The chip writes the load payload into `op_a_access.access.value_0..3` via the constraint chain `c48..c63` (10 LB/LH/LW sign-extension fills + 4 positive-case fills). Every one of these constraints carries a `(1 - op_a_0)` factor via the two gate columns:

- `c46: mem_value_is_neg_not_x0 = (is_lb + is_lh + is_lw) · msb · (1 - op_a_0)`
- `c47: mem_value_is_pos_not_x0 = (is_lbu + is_lhu + is_lwu + is_ld + (is_lb + is_lh + is_lw)·(1 - msb)) · (1 - op_a_0)`

When `op_a_0 = 1` (`rd = x0`), **both** gates collapse to `0`, so `c48..c63` fire vacuously. The chip then permits any FKB value in `value_i` (up to `2,130,706,432`).

But the Memory bus (multiplicity `+is_real`) emitted by the chip carries those exact columns as the load result `a_0..a_3`, and `MemoryBus.Spec` (in `RV64IM/RVSail/Buses.lean`) requires unconditionally for every load opcode:

```
mem_opcode is a load → a_0..a_3 < 65536
```

So the chip cannot discharge its wf-assertion side of the Memory bus contract in the `op_a_0 = 1` case.

### Scope

- **Blocks** the per-load **spec lemmas** (`spec_LB`/`spec_LBU`/`spec_LH`/`spec_LHU`/`spec_LW`/`spec_LWU`/`spec_LD`), specifically the `value_i < 65536` conjunct.
- **Does NOT block** `bus_equiv_<LOAD>` — the x0 case of each `bus_equiv_<LOAD>` is closable from chip constraints alone (`c46 + c47 + c60-c63` force `a_i = 0`, and the byte-bus + `msb` case-split lets us derive `selected_word_*` / `selected_limb` / `selected_byte` are also `0` where needed).

### Why exploitable on paper but harmless in practice

RISC-V semantics: writes to `x0` are no-ops; CpuChip pins the post-write `x0` value to `0` via its own State-bus emission. So a malicious prover putting garbage into the Memory entry's `a_i` doesn't actually corrupt any register state in a well-formed Pico trace. But any downstream consumer that trusted the bus's u16 claim could be misled.

### RV32IM comparison

RV32IM has the same gate logic but only one limb to bound; the same shape of fix applies. (Note: the analogous patch upstream for the DivRem `bit = 1` gap has already landed as Pico PR #101 — same shape of fix.)

### Proposed fix (RV64IM)

Four extra algebraic constraints, no new witness columns:

```rust
for i in 0..4 {
    builder.assert_eq(
        local.instruction.op_a_0 * local.instruction.op_a_access.access.value[i],
        AB::Expr::ZERO,
    );
}
```

When `op_a_0 = 1`, this pins each `value_i = 0` (trivially u16-bounded). When `op_a_0 = 0`, the constraint is satisfied for any `value_i`, leaving `c48..c63` in charge.

---

## Gap 3 — LB/LBU high byte of `selected_limb` is never range-checked

**Severity:** Medium. Affects LBU directly; LB only via the byte-bus's MSB lookup which incidentally bounds the relevant byte (so `spec_LB` is provable but uses a non-obvious path; `bus_equiv_LB` is still blocked).

### The chip's behavior

The chip decomposes `selected_limb` (the active u16 limb of `prev_value_*`) into a low byte and a high byte using FKB arithmetic with `2122383361 = inv(256) mod FKB`:

```
selected_byte = offset_bit_0 · ((selected_limb - selected_limb_low_byte) · 2122383361)
              + (1 - offset_bit_0) · selected_limb_low_byte                            -- c21
```

For this byte split to be sound, **both** the low byte and the high byte `(selected_limb - selected_limb_low_byte) · 2122383361` need to be range-checked `< 256`. The chip's byte-bus entry for the LB+LBU pair (entry 11 in `bus_row`) is:

```
(-(is_lb + is_lbu), #v[7, 0, 0, selected_limb_low_byte, 0])
```

`ByteBus.Spec 7` range-checks `x_2` and `x_3`, but here `x_3 = 0` literally — so only `selected_limb_low_byte` is bounded. The high byte `(selected_limb - selected_limb_low_byte) · 2122383361` is **never** range-checked. A malicious prover can supply a fake `selected_limb_low_byte ∈ [0, 256)` that doesn't match the actual low byte of `selected_limb`, making the high byte an arbitrary FKB element (up to ~2.13 × 10⁹). Then:

- For **LBU `offset_bit_0 = 1`**: `selected_byte = high_byte` is unbounded → the u16 bound on `value_0` fails, AND the zero-extension equation `a = zeroExtend 64 (a.truncate 8)` is violated.
- For **LBU `offset_bit_0 = 0`**: `selected_byte = selected_limb_low_byte` is bounded directly, but the byte decomposition of `selected_limb` is still inconsistent → blocks `bus_equiv_LBU`'s byte-by-byte equivalence with the Memory bus.
- For **LB**: `selected_byte < 256` is enforced via byte-bus entry 12 (the `msb` lookup, opcode 6: `x_0 = if x_2 < 128 then 0 else 1 ∧ x_2 < 256`), so `spec_LB` passes. **But** `bus_equiv_LB` still needs the high-byte bound for the `offset_bit_0 = 0` case, where the same byte-split arithmetic is required.

### Scope: 3 Lean MISSINGs, 1 chip omission

The same chip omission surfaces in three Lean MISSINGs:

1. `spec_LBU` conjunct (a/d), `op_a_0 = 0, offset_bit_0 = 1` sub-case — `MISSING_LBU_selected_byte_in_range : selected_byte.val < 256`.
2. `bus_equiv_LBU` — `MISSING_LBU_selected_limb_high_byte_in_range : ((selected_limb - selected_limb_low_byte) · 2122383361).val < 256`.
3. `bus_equiv_LB` — `MISSING_LB_selected_limb_high_byte_in_range` (same form).

One Pico-side fix discharges all three.

### RV32IM comparison

RV32IM uses the same byte-split mechanism but is bug-free — its `prev_value` width matches the byte-bus structure differently; the high-byte slot is not silently dropped.

### Proposed fix (RV64IM)

Mirror the SB store pattern. SB emits its byte split with both bytes on the bus:

```
(-is_sb, #v[7, 0, 0, mem_limb_low_byte, (selected_limb - mem_limb_low_byte) · 2122383361])
```

Change byte-bus entry 11 (LB+LBU) from:

```
(-(is_lb + is_lbu), #v[7, 0, 0, selected_limb_low_byte, 0])
```

to:

```
(-(is_lb + is_lbu),
 #v[7, 0, 0, selected_limb_low_byte,
   (selected_limb - selected_limb_low_byte) * 2122383361])
```

No new columns; just a different inline expression in `x_3`. After the patch, `ByteBus.Spec 7` forces both bytes `< 256`, fixing all three Lean MISSINGs.

### Other loads are unaffected

- **LH** (opcode 11): byte-bus 13 (`-is_lh [4, 8, 2·selected_limb - msb·65536, 0, 0, 0]`) bounds `2·selected_limb - msb·65536 < 65536`, which (with `msb ∈ {0, 1}`) gives `selected_limb < 65536`.
- **LHU** (opcode 14): `c20` + state-bus u16 bounds on `memory_access.prev_value_i` + `limb_select` one-hot directly give `selected_limb < 65536`. The LHU spec is zero-extension (no `msb` involved), so the bound suffices.
- **LW** / **LWU** (opcodes 12 / 45): bound `selected_word_{0,1} < 65536` via `c30`/`c31` + state-bus bounds + offset-bit booleanness.
- **LD** (opcode 46): `unsigned_mem_val_i = memory_access.access.value_i` directly, bounded by state bus.

---

## How the Lean verification reflects each gap

The verification effort produced a per-opcode `bus_equiv_<OP>` lemma for each of the 11 memory opcodes, plus a top-level `bus_equiv` dispatcher. Each lemma's signature lists the MISSINGs it consumes:

```
bus_equiv_LB  ⟵ MISSING_LB_extends_correctly,
                MISSING_LB_selected_limb_high_byte_in_range,    -- Gap 3
                MISSING_LB_addr_aligned                          -- Gap 1
bus_equiv_LBU ⟵ MISSING_LBU_extends_correctly,
                MISSING_LBU_selected_limb_high_byte_in_range,   -- Gap 3
                MISSING_LBU_addr_aligned                         -- Gap 1
bus_equiv_LH  ⟵ MISSING_LH_extends_correctly,  MISSING_LH_addr_aligned       -- Gap 1
bus_equiv_LHU ⟵ MISSING_LHU_extends_correctly, MISSING_LHU_addr_aligned      -- Gap 1
bus_equiv_LW  ⟵ MISSING_LW_extends_correctly,  MISSING_LW_addr_aligned       -- Gap 1
bus_equiv_LWU ⟵ MISSING_LWU_extends_correctly, MISSING_LWU_addr_aligned      -- Gap 1
bus_equiv_LD  ⟵ MISSING_LD_extends_correctly,  MISSING_LD_addr_aligned       -- Gap 1
bus_equiv_SB  ⟵ MISSING_SB_addr_aligned                                       -- Gap 1
bus_equiv_SH  ⟵ MISSING_SH_addr_aligned                                       -- Gap 1
bus_equiv_SW  ⟵ MISSING_SW_addr_aligned                                       -- Gap 1
bus_equiv_SD  ⟵ MISSING_SD_addr_aligned                                       -- Gap 1
```

The `MISSING_<OP>_extends_correctly` hypotheses are not soundness gaps — they encode the chip's sign/zero-extension semantics for loads (a Pico-internal convention) and are derivable from the chip constraints in the `op_a_0 = 0` (normal `rd`) branch.

The per-load spec lemmas (`spec_<LOAD>`, proving correctness of the load) additionally carry `MISSING_<LOAD>_value_in_range` hypotheses for Gap 2 (`value_i < 65536` when `op_a_0 = 1`) and `MISSING_LBU_selected_byte_in_range` for Gap 3.

After all three chip-side patches:
- **Gap 1 fix** — discharges 11 `MISSING_<OP>_addr_aligned` and lets the `bus_equiv` dispatcher take no chip-side MISSINGs at all (only the convenience `MISSING_<OP>_extends_correctly`).
- **Gap 2 fix** — discharges 7 `MISSING_<LOAD>_value_in_range` (one per load opcode).
- **Gap 3 fix** — discharges 3 MISSINGs: `MISSING_LBU_selected_byte_in_range`, `MISSING_LBU_selected_limb_high_byte_in_range`, `MISSING_LB_selected_limb_high_byte_in_range`.

---

## File references

All in `PicoFV/RV64IM/`:

- `Constraints/MemoryReadWriteChip.lean` — extracted chip constraints (the 85 `c0..c84` definitions).
- `RVSail/Buses.lean` — `bus_row`, `BusEntry` definitions, `ByteBus.Spec` / `MemoryBus.Spec`.
- `Spec/MemoryReadWriteChip.lean` — the formal verification: 11 per-load/store spec lemmas + 11 `bus_equiv_<OP>` lemmas + top-level `bus_equiv` dispatcher.

For RV32IM comparison: `PicoFV/RV32IM/Constraints/MemoryReadWriteAir.lean` (Gap 1's analogous `constraint_12`).
