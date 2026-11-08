import PicoFV.RV64IM.RVSail.Operations
import PicoFV.RV64IM.Extraction.MulGadget
import PicoFV.RV64IM.Airs.MulGadget
import PicoFV.RV64IM.Constraints.U16MSBGadget
import PicoFV.RV64IM.Constraints.U16ToU8GadgetSafe

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# MulGadget — abstract constraints & buses

`MulGadget`'s Pico Rust source is `vm/src/chips/gadgets/mul.rs` at
commit `22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`. The gadget computes
`a = b * c` as 16 u8-limbs of the unsigned 128-bit product via
schoolbook polynomial multiplication with carry propagation, then
selects which window of the 128-bit product is placed back into `a`
depending on the operation selector:

| Selector    | What's placed into `a` (low → high)                        |
|-------------|------------------------------------------------------------|
| `is_mul`    | low 64 bits of `b · c` — bytes 0..7                        |
| `is_mulh`   | high 64 bits of (signed `b`) · (signed `c`) — bytes 8..15  |
| `is_mulhu`  | high 64 bits of (unsigned `b`) · (unsigned `c`) — bytes 8..15 |
| `is_mulhsu` | high 64 bits of (signed `b`) · (unsigned `c`) — bytes 8..15  |
| `is_mulw`   | sign-extension of low 32 bits of `b · c` (bytes 0..3, then sext fill) |

Signed handling is done via per-operand sign-extension flags
(`b_sign_extend`, `c_sign_extend`), which when set fill the upper 8
bytes of each operand with `0xff` before the polynomial multiplication.

## Standalone layout (63 columns total in the extraction)

| Cols    | Role                                              |
|---------|---------------------------------------------------|
| 0..3    | `a_0..a_3` (output, u16 limbs supplied by parent) |
| 4..7    | `b_0..b_3` (input 1)                              |
| 8..11   | `c_0..c_3` (input 2)                              |
| 12..27  | `carry_0..carry_15` (u16-range-checked carry per byte position) |
| 28..43  | `product_0..product_15` (u8-range-checked product bytes) |
| 44..47  | `b_lower_byte_0..b_lower_byte_3` (low byte of each `b` limb) |
| 48..51  | `c_lower_byte_0..c_lower_byte_3` (low byte of each `c` limb) |
| 52      | `b_msb` — top bit of byte 7 of `b`                |
| 53      | `c_msb` — top bit of byte 7 of `c`                |
| 54      | `product_msb` — top bit of `a_1` (used by MULW)   |
| 55      | `b_sign_extend` — `is_signed_b · b_msb`           |
| 56      | `c_sign_extend` — `is_signed_c · c_msb`           |
| 57      | `is_real` (parent's activation flag)              |
| 58..62  | `is_mul`, `is_mulh`, `is_mulw`, `is_mulhu`, `is_mulhsu` |

## Per-byte values

The polynomial multiplication operates on 16-byte vectors derived from
the 4-limb `b` and `c` Words. For `b`:
```
b_byte[0]      = b_lower_byte_0
b_byte[1]      = (b_0 - b_lower_byte_0) · 2122383361   -- · 256⁻¹
b_byte[2]      = b_lower_byte_1
b_byte[3]      = (b_1 - b_lower_byte_1) · 2122383361
b_byte[4]      = b_lower_byte_2
b_byte[5]      = (b_2 - b_lower_byte_2) · 2122383361
b_byte[6]      = b_lower_byte_3
b_byte[7]      = (b_3 - b_lower_byte_3) · 2122383361
b_byte[8..15]  = b_sign_extend · 255    -- 0x00 / 0xff fill
```
(Identical pattern for `c_byte` with `c_lower_byte_*` and
`c_sign_extend`.) `2122383361` is `256⁻¹ mod FKB`.

## Algebraic constraints (45 total)

- **c0**: `is_mulw · (is_mulw - 1) = 0` — `is_mulw` bool (from
  `U16MSBGadget::eval`'s own `assert_bool(is_real)` on
  `product_msb`, where the embedded `is_real` is `is_mulw`).
- **c1**: `product_msb · (product_msb - 1) = 0` — `product_msb` bool
  (from `U16MSBGadget::eval`'s own `assert_bool(msb)`).
- **c2**: `b_sign_extend = (is_mulh + is_mulhsu) · b_msb`.
- **c3**: `c_sign_extend = is_mulh · c_msb`.
- **c4..c19**: 16 polynomial-multiplication carry constraints. For
  byte position `i`:
  `is_real · (product[i] - (m[i] + carry_in[i] - carry[i] · 256)) = 0`
  where `m[i] = Σ_{j+k=i, j,k∈[0,15]} b_byte[j] · c_byte[k]` and
  `carry_in[i] = if i = 0 then 0 else carry[i-1]`.
- **c20..c31**: 12 result-selection constraints (3 per output limb × 4
  limbs). For `i ∈ [0,3]`:
  - `is_mulw · ((product[2i] + product[2i+1] · 256) - a[i]) = 0` for
    `i ∈ {0, 1}` (low 32 bits = low half of `b · c`); for `i ∈ {2, 3}`,
    `is_mulw · (product_msb · 65535 - a[i]) = 0` (sign-extension fill).
  - `is_mul · ((product[2i] + product[2i+1] · 256) - a[i]) = 0` — low
    64 bits.
  - `(is_mulh + is_mulhu + is_mulhsu) ·
    ((product[2i + 8] + product[2i + 9] · 256) - a[i]) = 0` — high 64
    bits.
- **c32..c40**: bool checks on `b_msb`, `c_msb`, `b_sign_extend`,
  `c_sign_extend`, `is_mul`, `is_mulh`, `is_mulhu`, `is_mulhsu`,
  `is_mulw` (the last is a duplicate of c0).
- **c41**: at-most-one selector — `(is_mul + is_mulh + is_mulhu +
  is_mulhsu + is_mulw) · ((sum) - 1) = 0`.
- **c42**: `is_real · (is_real - 1) = 0`.
- **c43**: `b_sign_extend · (b_msb - 1) = 0` — if sign-extending `b`,
  the prover must have set `b_msb = 1`.
- **c44**: same for `c`.

## Bus interactions (35 entries, all `ByteBus`)

- 4 `(opcode 5, sub-op 7) = U8Pair` entries gated by `+is_real` for
  `(b_lower_byte_i, (b_i - b_lower_byte_i) · 256⁻¹)` — the
  `U16ToU8GadgetSafe(b)` range-check (low byte / high byte).
- 4 similar entries for `c`.
- 2 `(5, 6) = MSB` entries gated by `+is_real`: `MSB(b_msb, byte 7 of
  b)` and `MSB(c_msb, byte 7 of c)`. These tie `b_msb`/`c_msb` to the
  top bit of the top byte of `b`/`c`.
- 1 `(5, 8) = U16Range` entry gated by `+is_mulw`: `2 · a_1 -
  product_msb · 65536` — the `U16MSBGadget` consistency check on
  `a_1`.
- 16 `(5, 8) = U16Range` entries gated by `+is_real`: u16-range-check
  on each `carry_0..carry_15`.
- 8 `(5, 7) = U8Pair` entries gated by `+is_real`: u8-range-check on
  `(product[2i], product[2i+1])` for `i ∈ [0, 7]` — the
  `slice_range_check_u8` pair form.

This file therefore provides only the parametric `AbsConstraints` and
`AbsBuses` predicates. The semantic spec lives in
`Spec/MulGadget.lean`.
-/

namespace MulGadget

  open RV64IM_Interactions

  /-- The conjunction of algebraic facts the Pico `MulGadget` asserts
      on a row, expressed parametrically in the 45 owned column values
      plus the parent-supplied `a`, `b`, `c`, `is_real`, and the five
      operation-selector flags.

      The polynomial-multiplication carry constraints (c4..c19) are
      written by literal degree-expanded form rather than via a
      `Finset.sum`, to keep `AbsConstraints` definitionally close to
      the extraction. Sub-expressions used repeatedly:

      ```
      b_byte_0 = b_lower_byte_0
      b_byte_1 = (b_0 - b_lower_byte_0) · 2122383361
      … etc … with b_byte_{8..15} = b_sign_extend · 255
      ```

      (analogous for `c_byte`). -/
  def AbsConstraints
    {F : Type} [Field F]
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
     b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
     c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
     b_msb c_msb product_msb
     b_sign_extend c_sign_extend : F)
  : Prop :=
    -- Per-byte values for `b` and `c`. We bind them as `let` so the
    -- 16 carry-propagation constraints below stay readable.
    let bb0 := b_lower_byte_0
    let bb1 := (b_0 - b_lower_byte_0) * 2122383361
    let bb2 := b_lower_byte_1
    let bb3 := (b_1 - b_lower_byte_1) * 2122383361
    let bb4 := b_lower_byte_2
    let bb5 := (b_2 - b_lower_byte_2) * 2122383361
    let bb6 := b_lower_byte_3
    let bb7 := (b_3 - b_lower_byte_3) * 2122383361
    let bbS := b_sign_extend * 255
    let cb0 := c_lower_byte_0
    let cb1 := (c_0 - c_lower_byte_0) * 2122383361
    let cb2 := c_lower_byte_1
    let cb3 := (c_1 - c_lower_byte_1) * 2122383361
    let cb4 := c_lower_byte_2
    let cb5 := (c_2 - c_lower_byte_2) * 2122383361
    let cb6 := c_lower_byte_3
    let cb7 := (c_3 - c_lower_byte_3) * 2122383361
    let cbS := c_sign_extend * 255
    -- ====================================================================
    -- c0: U16MSBGadget(product_msb)'s own `assert_bool(is_real)`,
    -- where this gadget's local `is_real` is the parent's `is_mulw`.
    -- ====================================================================
    (is_mulw * (is_mulw - 1) = 0) ∧
    -- ====================================================================
    -- c1: U16MSBGadget(product_msb)'s own `assert_bool(msb)`.
    -- ====================================================================
    (product_msb * (product_msb - 1) = 0) ∧
    -- ====================================================================
    -- c2..c3: sign-extension flags.
    -- ====================================================================
    (b_sign_extend - (is_mulh + is_mulhsu) * b_msb = 0) ∧
    (c_sign_extend - is_mulh * c_msb = 0) ∧
    -- ====================================================================
    -- c4..c19: 16 polynomial-mult carry constraints.
    -- product[i] = m[i] + (carry[i-1] if i > 0 else 0) - carry[i] * 256.
    -- ====================================================================
    -- i = 0
    (is_real *
      (product_0 - (bb0 * cb0 - carry_0 * 256)) = 0) ∧
    -- i = 1
    (is_real *
      (product_1 - ((bb0 * cb1 + bb1 * cb0) + carry_0 - carry_1 * 256)) = 0) ∧
    -- i = 2
    (is_real *
      (product_2 - ((bb0 * cb2 + bb1 * cb1 + bb2 * cb0) + carry_1 - carry_2 * 256)) = 0) ∧
    -- i = 3
    (is_real *
      (product_3 -
        ((bb0 * cb3 + bb1 * cb2 + bb2 * cb1 + bb3 * cb0) + carry_2 - carry_3 * 256)) = 0) ∧
    -- i = 4
    (is_real *
      (product_4 -
        ((bb0 * cb4 + bb1 * cb3 + bb2 * cb2 + bb3 * cb1 + bb4 * cb0)
          + carry_3 - carry_4 * 256)) = 0) ∧
    -- i = 5
    (is_real *
      (product_5 -
        ((bb0 * cb5 + bb1 * cb4 + bb2 * cb3 + bb3 * cb2 + bb4 * cb1 + bb5 * cb0)
          + carry_4 - carry_5 * 256)) = 0) ∧
    -- i = 6
    (is_real *
      (product_6 -
        ((bb0 * cb6 + bb1 * cb5 + bb2 * cb4 + bb3 * cb3 + bb4 * cb2 + bb5 * cb1 + bb6 * cb0)
          + carry_5 - carry_6 * 256)) = 0) ∧
    -- i = 7
    (is_real *
      (product_7 -
        ((bb0 * cb7 + bb1 * cb6 + bb2 * cb5 + bb3 * cb4 + bb4 * cb3 + bb5 * cb2 + bb6 * cb1
          + bb7 * cb0) + carry_6 - carry_7 * 256)) = 0) ∧
    -- i = 8 .. i = 15 use the sign-extension fill `bbS` / `cbS` for any
    -- index ≥ 8. The summation indexing follows
    -- `m[i] = Σ_{j+k=i, j,k∈[0,15]} b_byte[j] · c_byte[k]`.
    -- i = 8
    (is_real *
      (product_8 -
        ((bb0 * cbS + bb1 * cb7 + bb2 * cb6 + bb3 * cb5 + bb4 * cb4 + bb5 * cb3 + bb6 * cb2
          + bb7 * cb1 + bbS * cb0) + carry_7 - carry_8 * 256)) = 0) ∧
    -- i = 9
    (is_real *
      (product_9 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cb7 + bb3 * cb6 + bb4 * cb5 + bb5 * cb4 + bb6 * cb3
          + bb7 * cb2 + bbS * cb1 + bbS * cb0) + carry_8 - carry_9 * 256)) = 0) ∧
    -- i = 10
    (is_real *
      (product_10 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cb7 + bb4 * cb6 + bb5 * cb5 + bb6 * cb4
          + bb7 * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0) + carry_9 - carry_10 * 256)) = 0) ∧
    -- i = 11
    (is_real *
      (product_11 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cb7 + bb5 * cb6 + bb6 * cb5
          + bb7 * cb4 + bbS * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0)
          + carry_10 - carry_11 * 256)) = 0) ∧
    -- i = 12
    (is_real *
      (product_12 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cb7 + bb6 * cb6
          + bb7 * cb5 + bbS * cb4 + bbS * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0)
          + carry_11 - carry_12 * 256)) = 0) ∧
    -- i = 13
    (is_real *
      (product_13 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cbS + bb6 * cb7
          + bb7 * cb6 + bbS * cb5 + bbS * cb4 + bbS * cb3 + bbS * cb2 + bbS * cb1 + bbS * cb0)
          + carry_12 - carry_13 * 256)) = 0) ∧
    -- i = 14
    (is_real *
      (product_14 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cbS + bb6 * cbS
          + bb7 * cb7 + bbS * cb6 + bbS * cb5 + bbS * cb4 + bbS * cb3 + bbS * cb2 + bbS * cb1
          + bbS * cb0) + carry_13 - carry_14 * 256)) = 0) ∧
    -- i = 15
    (is_real *
      (product_15 -
        ((bb0 * cbS + bb1 * cbS + bb2 * cbS + bb3 * cbS + bb4 * cbS + bb5 * cbS + bb6 * cbS
          + bb7 * cbS + bbS * cb7 + bbS * cb6 + bbS * cb5 + bbS * cb4 + bbS * cb3 + bbS * cb2
          + bbS * cb1 + bbS * cb0) + carry_14 - carry_15 * 256)) = 0) ∧
    -- ====================================================================
    -- c20..c31: result-selection (12 constraints).
    -- ====================================================================
    -- a_0
    (is_mulw * ((product_0 + product_1 * 256) - a_0) = 0) ∧
    (is_mul * ((product_0 + product_1 * 256) - a_0) = 0) ∧
    ((is_mulh + is_mulhu + is_mulhsu) * ((product_8 + product_9 * 256) - a_0) = 0) ∧
    -- a_1
    (is_mulw * ((product_2 + product_3 * 256) - a_1) = 0) ∧
    (is_mul * ((product_2 + product_3 * 256) - a_1) = 0) ∧
    ((is_mulh + is_mulhu + is_mulhsu) * ((product_10 + product_11 * 256) - a_1) = 0) ∧
    -- a_2
    (is_mulw * (product_msb * 65535 - a_2) = 0) ∧
    (is_mul * ((product_4 + product_5 * 256) - a_2) = 0) ∧
    ((is_mulh + is_mulhu + is_mulhsu) * ((product_12 + product_13 * 256) - a_2) = 0) ∧
    -- a_3
    (is_mulw * (product_msb * 65535 - a_3) = 0) ∧
    (is_mul * ((product_6 + product_7 * 256) - a_3) = 0) ∧
    ((is_mulh + is_mulhu + is_mulhsu) * ((product_14 + product_15 * 256) - a_3) = 0) ∧
    -- ====================================================================
    -- c32..c44: bool checks + at-most-one selector + sign-extend → msb.
    -- ====================================================================
    (b_msb * (b_msb - 1) = 0) ∧
    (c_msb * (c_msb - 1) = 0) ∧
    (b_sign_extend * (b_sign_extend - 1) = 0) ∧
    (c_sign_extend * (c_sign_extend - 1) = 0) ∧
    (is_mul * (is_mul - 1) = 0) ∧
    (is_mulh * (is_mulh - 1) = 0) ∧
    (is_mulhu * (is_mulhu - 1) = 0) ∧
    (is_mulhsu * (is_mulhsu - 1) = 0) ∧
    (is_mulw * (is_mulw - 1) = 0) ∧
    ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw) *
       ((is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw) - 1) = 0) ∧
    (is_real * (is_real - 1) = 0) ∧
    (b_sign_extend * (b_msb - 1) = 0) ∧
    (c_sign_extend * (c_msb - 1) = 0)

  /-- The 35 byte-bus entries the Pico `MulGadget` contributes per row.
      All entries are gated by `+is_real`, except the
      `U16MSBGadget(product_msb)` consistency check on `a_1` which is
      gated by `+is_mulw`. -/
  def AbsBuses
    (is_real is_mulw
     a_1
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
     b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
     c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
     b_msb c_msb product_msb : FKB)
  : BusRow :=
    -- U16ToU8GadgetSafe on b (4 byte-bus entries)
    U16ToU8GadgetSafe.AbsBuses is_real b_0 b_1 b_2 b_3
      b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
    ++
    -- U16ToU8GadgetSafe on c (4 byte-bus entries)
    U16ToU8GadgetSafe.AbsBuses is_real c_0 c_1 c_2 c_3
      c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
    ++
    -- Remaining MulGadget-own bus entries: 2 × MSB byte lookups, 1 ×
    -- U16MSBGadget consistency on `a_1`, 16 × U16Range on carry,
    -- 8 × U8Pair on the product bytes.
    ({
      Program := [],
      ALU := [],
      Byte := List.map ByteBusEntry.deserialise [
        -- 2 × MSB lookup (sub-op 6) for b_msb, c_msb on top byte
        ((is_real), #v[6, b_msb, 0, (b_3 - b_lower_byte_3) * 2122383361, 0]),
        ((is_real), #v[6, c_msb, 0, (c_3 - c_lower_byte_3) * 2122383361, 0]),
        -- 1 × U16MSBGadget(product_msb) byte-bus consistency on a_1
        ((is_mulw), #v[8, 2 * a_1 - product_msb * 65536, 0, 0, 0]),
        -- 16 × U16Range on carry (sub-op 8)
        ((is_real), #v[8, carry_0, 0, 0, 0]),
        ((is_real), #v[8, carry_1, 0, 0, 0]),
        ((is_real), #v[8, carry_2, 0, 0, 0]),
        ((is_real), #v[8, carry_3, 0, 0, 0]),
        ((is_real), #v[8, carry_4, 0, 0, 0]),
        ((is_real), #v[8, carry_5, 0, 0, 0]),
        ((is_real), #v[8, carry_6, 0, 0, 0]),
        ((is_real), #v[8, carry_7, 0, 0, 0]),
        ((is_real), #v[8, carry_8, 0, 0, 0]),
        ((is_real), #v[8, carry_9, 0, 0, 0]),
        ((is_real), #v[8, carry_10, 0, 0, 0]),
        ((is_real), #v[8, carry_11, 0, 0, 0]),
        ((is_real), #v[8, carry_12, 0, 0, 0]),
        ((is_real), #v[8, carry_13, 0, 0, 0]),
        ((is_real), #v[8, carry_14, 0, 0, 0]),
        ((is_real), #v[8, carry_15, 0, 0, 0]),
        -- 8 × U8Pair on product[2i], product[2i+1]
        ((is_real), #v[7, 0, 0, product_0, product_1]),
        ((is_real), #v[7, 0, 0, product_2, product_3]),
        ((is_real), #v[7, 0, 0, product_4, product_5]),
        ((is_real), #v[7, 0, 0, product_6, product_7]),
        ((is_real), #v[7, 0, 0, product_8, product_9]),
        ((is_real), #v[7, 0, 0, product_10, product_11]),
        ((is_real), #v[7, 0, 0, product_12, product_13]),
        ((is_real), #v[7, 0, 0, product_14, product_15])
      ],
      State := [],
      Memory := []
    } : BusRow)

end MulGadget

namespace MulGadget.Interpretations

  /-- Gadget-level analogue of `MulChip.Interpretations.selector_breakdown`.
      Each of the five operation selectors is binary (∈ `{0, 1}`), and
      their sum is `0` or `1` (from the at-most-one constraint
      `(sum) · ((sum) - 1) = 0` baked into `MulGadget.AbsConstraints`).
      This lemma is purely about the `AbsConstraints` bool checks — it
      does **not** require `is_real = 1` or the parent invariant. -/
  lemma selector_breakdown
    {F : Type} [Field F]
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
     b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
     c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
     b_msb c_msb product_msb
     b_sign_extend c_sign_extend : F)
    (h_constraints :
      MulGadget.AbsConstraints
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
        a_0 a_1 a_2 a_3
        b_0 b_1 b_2 b_3
        c_0 c_1 c_2 c_3
        carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
        carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
        product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
        product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
        b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
        c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
        b_msb c_msb product_msb
        b_sign_extend c_sign_extend)
  :
    (is_mul = 0 ∨ is_mul = 1) ∧
    (is_mulh = 0 ∨ is_mulh = 1) ∧
    (is_mulhu = 0 ∨ is_mulhu = 1) ∧
    (is_mulhsu = 0 ∨ is_mulhsu = 1) ∧
    (is_mulw = 0 ∨ is_mulw = 1) ∧
    (is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 0 ∨
     is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 1)
  := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
            _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
            is_mul_b, is_mulh_b, is_mulhu_b, is_mulhsu_b, is_mulw_b,
            sum_b, _, _, _⟩ := h_constraints
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    . exact (mul_eq_zero.mp is_mul_b).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp is_mulh_b).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp is_mulhu_b).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp is_mulhsu_b).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp is_mulw_b).imp id sub_eq_zero.mp
    . exact (mul_eq_zero.mp sum_b).imp id sub_eq_zero.mp

  /-- Gadget-level analogue of `MulChip.Interpretations.selector_exclusivity`.
      Given the parent invariants `is_real = 1` and
      `is_real = sum_of_selectors`, exactly one selector is `1` and the
      others are `0`. The sum-equals-`1` fact pins the case down (vs.
      just `selector_breakdown` which allows sum = 0). -/
  lemma selector_exclusivity
    (is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
     a_0 a_1 a_2 a_3
     b_0 b_1 b_2 b_3
     c_0 c_1 c_2 c_3
     carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
     carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
     product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
     product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
     b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
     c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
     b_msb c_msb product_msb
     b_sign_extend c_sign_extend : FKB)
    (h_constraints :
      MulGadget.AbsConstraints
        is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
        a_0 a_1 a_2 a_3
        b_0 b_1 b_2 b_3
        c_0 c_1 c_2 c_3
        carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
        carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
        product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
        product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
        b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
        c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
        b_msb c_msb product_msb
        b_sign_extend c_sign_extend)
    (h_is_real : is_real = 1)
    (h_real_eq_sum :
      is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw)
  :
    (is_mul = 1 →
      is_mulh = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0 ∧ is_mulw = 0) ∧
    (is_mulh = 1 →
      is_mul = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0 ∧ is_mulw = 0) ∧
    (is_mulhu = 1 →
      is_mul = 0 ∧ is_mulh = 0 ∧ is_mulhsu = 0 ∧ is_mulw = 0) ∧
    (is_mulhsu = 1 →
      is_mul = 0 ∧ is_mulh = 0 ∧ is_mulhu = 0 ∧ is_mulw = 0) ∧
    (is_mulw = 1 →
      is_mul = 0 ∧ is_mulh = 0 ∧ is_mulhu = 0 ∧ is_mulhsu = 0)
  := by
    have h_breakdown :=
      selector_breakdown is_real is_mul is_mulh is_mulw is_mulhu is_mulhsu
        a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
        carry_0 carry_1 carry_2 carry_3 carry_4 carry_5 carry_6 carry_7
        carry_8 carry_9 carry_10 carry_11 carry_12 carry_13 carry_14 carry_15
        product_0 product_1 product_2 product_3 product_4 product_5 product_6 product_7
        product_8 product_9 product_10 product_11 product_12 product_13 product_14 product_15
        b_lower_byte_0 b_lower_byte_1 b_lower_byte_2 b_lower_byte_3
        c_lower_byte_0 c_lower_byte_1 c_lower_byte_2 c_lower_byte_3
        b_msb c_msb product_msb b_sign_extend c_sign_extend
        h_constraints
    have h_sum_one : is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw = 1 := by
      rw [← h_real_eq_sum]; exact h_is_real
    clear h_constraints h_is_real h_real_eq_sum
    grind (splits := 22)

end MulGadget.Interpretations
