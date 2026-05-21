import PicoFV.RV64IM.Constraints.BitwiseChip

open Plonky3

set_option maxHeartbeats 1_000_000_000

/-!
# BitwiseChip — semantic specification

The `BitwiseChip.Spec` namespace below states the semantic content of
the chip's three operations (XOR, OR, AND) on full 64-bit words.

Layout (mirroring RV32 `BitwiseAir.Spec` but adapted for u16 limbs):

- `selector_breakdown` — the three selectors are binary and their sum
  is 0 or 1 (in `Interpretations`; we just consume it here).
- `ext_asrt` — externality assertions on the chip's bus row (vacuous:
  byte bus has no externals; ALU entry's externals don't fire on
  emitted side).
- `spec_XOR`, `spec_OR`, `spec_AND` — each discharges `ALUBus.Spec
  <opcode>` from the gadget's byte-bus assumptions, by composing 8
  byte-level bitwise facts (one per byte of the 64-bit result) into 4
  limb-level facts via the `low_byte + (high_byte) * 256` decomposition,
  and then into the full `BitVec 64` equation via `xor_append` /
  `or_append` / `and_append`.
- `wf_asrt` — well-formedness, dispatching to whichever of XOR/OR/AND
  is currently active.

The byte/limb plumbing — specifically the inline high-byte expression
`(limb - low_byte) * inv(256)` — is what makes this longer than the
RV32 version; the high byte is *not* a column but a derived expression
pinned to `< 256` by the byte bus.
-/

namespace BitwiseChip.Spec

  open RV64IM_Interactions
  open BitwiseChip.ConstraintsAndBuses
  open BitwiseChip.Interactions
  open BitwiseChip.Interpretations

  set_option maxHeartbeats 1_000_000_000

  --
  -- Byte-level FKB↔BitVec bitwise conversion (re-imported from the
  -- RV32 BitwiseAir spec — these are private there)
  --

  private lemma FKB.ofNat_xor_eq (a b : FKB) (ha : a.val < 256) (hb : b.val < 256) :
      BitVec.ofNat 8 (a ^^^ b).val = BitVec.ofNat 8 a.val ^^^ BitVec.ofNat 8 b.val := by
    simp only [Fin.xor_val]
    have : a.val ^^^ b.val < 2130706433 := by
      have h1 : a.val < 2 ^ 8 := by omega
      have h2 : b.val < 2 ^ 8 := by omega
      have := Nat.xor_lt_two_pow h1 h2; omega
    simp only [Nat.mod_eq_of_lt this, BitVec.ofNat_xor]

  private lemma FKB.ofNat_or_eq (a b : FKB) (ha : a.val < 256) (hb : b.val < 256) :
      BitVec.ofNat 8 (a ||| b).val = BitVec.ofNat 8 a.val ||| BitVec.ofNat 8 b.val := by
    simp only [Fin.or_val]
    have : a.val ||| b.val < 2130706433 := by
      have h1 : a.val < 2 ^ 8 := by omega
      have h2 : b.val < 2 ^ 8 := by omega
      have := Nat.or_lt_two_pow h1 h2; omega
    simp only [Nat.mod_eq_of_lt this, BitVec.ofNat_or]

  private lemma FKB.ofNat_and_eq (a b : FKB) (hb : b.val < 256) :
      BitVec.ofNat 8 (a &&& b).val = BitVec.ofNat 8 a.val &&& BitVec.ofNat 8 b.val := by
    simp only [Fin.and_val]
    have : a.val &&& b.val < 2130706433 := by
      have := Nat.and_lt_two_pow a.val (n := 8) (by omega); omega
    simp only [BitVec.ofNat_and]

  --
  -- u16 limb decomposition: given a low byte bL and a high byte
  -- expression bH := (b - bL) * inv(256), both u8-ranged, recover the
  -- BitVec representation of the limb as (high8 ++ low8).
  --

  /-- Given `bL.val < 256` and `((b - bL) * inv(256)).val < 256`, the
      limb `b` decomposes as `bL.val + bH.val * 256` with both bytes
      `< 256`, hence its `BitVec 16` is `bH ++ bL`. -/
  private lemma limb_decomp (b bL : FKB)
      (h_bL : bL.val < 256)
      (h_bH : ((b - bL) * 2122383361 : FKB).val < 256) :
      b.val < 65536 ∧
      BitVec.ofNat 16 b.val =
        BitVec.ofNat 8 ((b - bL) * 2122383361 : FKB).val ++ BitVec.ofNat 8 bL.val := by
    -- Step 1: convert to a Nat equation. With bL.val < 256 and bH.val < 256,
    -- the sum bL.val + bH.val * 256 < 65536 < KB_prime, so no F-wraparound.
    set bH : FKB := (b - bL) * 2122383361 with h_bH_def
    have h_b_val : b.val = bL.val + bH.val * 256 := by grind
    refine ⟨ by omega, ?_ ⟩
    -- Step 2: BitVec equality via toNat. Convert `<<<` / `|||` to
    -- plain `*` / `+` via the `shiftLeft_add_eq_or_of_lt` idiom from
    -- `U32b.toBV_toNat`, then close with omega using `h_b_val`.
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]; simp
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
    omega

  /-- Compose two u8-ranged field elements into a `BitVec 16` via
      `low + high * 256`. Simpler sibling of `limb_decomp` — no
      `inv(256)` algebra, used for the chip's result limbs where both
      bytes are explicit. -/
  private lemma bv16_from_bytes (low high : FKB)
      (h_low : low.val < 256) (h_high : high.val < 256) :
      BitVec.ofNat 16 (low + high * 256 : FKB).val =
        BitVec.ofNat 8 high.val ++ BitVec.ofNat 8 low.val := by
    have h_high256 : (high * 256 : FKB).val = high.val * 256 := by grind
    have h_sum : (low + high * 256 : FKB).val = low.val + high.val * 256 := by grind
    rw [h_sum]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]; simp
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
    omega

  /-- Bridge `U64w.toBV` to `U64b.toBV` via per-limb byte splits. Each
      u16 limb `b_i` factors as `bH_i ++ bL_i` (BitVec 8 ++ BitVec 8),
      and the resulting `U64b` byte view has the same `BitVec 64`. -/
  private lemma U64w_toBV_eq_U64b_toBV
    (b_0 b_1 b_2 b_3 : BitVec 16)
    (bL_0 bH_0 bL_1 bH_1 bL_2 bH_2 bL_3 bH_3 : BitVec 8)
    (h_0 : b_0 = bH_0 ++ bL_0)
    (h_1 : b_1 = bH_1 ++ bL_1)
    (h_2 : b_2 = bH_2 ++ bL_2)
    (h_3 : b_3 = bH_3 ++ bL_3)
  :
    U64w.toBV #v[b_0, b_1, b_2, b_3]
    = U64b.toBV #v[bL_0, bH_0, bL_1, bH_1, bL_2, bH_2, bL_3, bH_3]
  := by
    subst h_0; subst h_1; subst h_2; subst h_3
    simp [U64w.toBV, U64b.toBV]
    bv_decide

  --
  -- spec_XOR — opcode 2 (XOR)
  --

  lemma spec_XOR
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseChip.Extraction.allHold air row)
    (h_xor : air.cols.values.is_xor row 0 = 1)
  :
    ALUBus.Spec 2
      ((air.cols.values.bitwise.bitwise.result_0 row 0) + (air.cols.values.bitwise.bitwise.result_1 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_2 row 0) + (air.cols.values.bitwise.bitwise.result_3 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_4 row 0) + (air.cols.values.bitwise.bitwise.result_5 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_6 row 0) + (air.cols.values.bitwise.bitwise.result_7 row 0) * 256)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    -- Establish that is_or = is_and = 0, hence is_real = 1
    obtain ⟨ h_xor_excl, _, _ ⟩ := selector_exclusivity air row h_constraints
    obtain ⟨ h_or, h_and ⟩ := h_xor_excl h_xor
    have h_real : air.cols.values.is_real row 0 = 1 := by
      show air.cols.values.is_xor row 0 + air.cols.values.is_or row 0 + air.cols.values.is_and row 0 = 1
      rw [h_xor, h_or, h_and]; ring
    -- Extract the 8 byte-bus assumptions (XOR opcode 2 at byte level)
    simp [bus_row_wf_asm, bus_row, h_xor, h_or, h_and, h_real, ByteBus.Spec] at h_wf
    obtain ⟨⟨h_x0, h_r0, h_bL0, h_cL0⟩,
            ⟨h_x1, h_r1, h_bH0, h_cH0⟩,
            ⟨h_x2, h_r2, h_bL1, h_cL1⟩,
            ⟨h_x3, h_r3, h_bH1, h_cH1⟩,
            ⟨h_x4, h_r4, h_bL2, h_cL2⟩,
            ⟨h_x5, h_r5, h_bH2, h_cH2⟩,
            ⟨h_x6, h_r6, h_bL3, h_cL3⟩,
            ⟨h_x7, h_r7, h_bH3, h_cH3⟩⟩ := h_wf
    -- Limb decompositions for b and c (4 each), and result composition (4)
    obtain ⟨h_b0_range, h_b0_split⟩ := limb_decomp _ _ h_bL0 h_bH0
    obtain ⟨h_b1_range, h_b1_split⟩ := limb_decomp _ _ h_bL1 h_bH1
    obtain ⟨h_b2_range, h_b2_split⟩ := limb_decomp _ _ h_bL2 h_bH2
    obtain ⟨h_b3_range, h_b3_split⟩ := limb_decomp _ _ h_bL3 h_bH3
    obtain ⟨h_c0_range, h_c0_split⟩ := limb_decomp _ _ h_cL0 h_cH0
    obtain ⟨h_c1_range, h_c1_split⟩ := limb_decomp _ _ h_cL1 h_cH1
    obtain ⟨h_c2_range, h_c2_split⟩ := limb_decomp _ _ h_cL2 h_cH2
    obtain ⟨h_c3_range, h_c3_split⟩ := limb_decomp _ _ h_cL3 h_cH3
    have h_a0_split := bv16_from_bytes _ _ h_r0 h_r1
    have h_a1_split := bv16_from_bytes _ _ h_r2 h_r3
    have h_a2_split := bv16_from_bytes _ _ h_r4 h_r5
    have h_a3_split := bv16_from_bytes _ _ h_r6 h_r7
    -- Byte-level XOR facts at BitVec level (from FKB byte XOR + ofNat_xor_eq)
    have h_byte_0 := FKB.ofNat_xor_eq _ _ h_bL0 h_cL0
    have h_byte_1 := FKB.ofNat_xor_eq _ _ h_bH0 h_cH0
    have h_byte_2 := FKB.ofNat_xor_eq _ _ h_bL1 h_cL1
    have h_byte_3 := FKB.ofNat_xor_eq _ _ h_bH1 h_cH1
    have h_byte_4 := FKB.ofNat_xor_eq _ _ h_bL2 h_cL2
    have h_byte_5 := FKB.ofNat_xor_eq _ _ h_bH2 h_cH2
    have h_byte_6 := FKB.ofNat_xor_eq _ _ h_bL3 h_cL3
    have h_byte_7 := FKB.ofNat_xor_eq _ _ h_bH3 h_cH3
    rw [← h_x0] at h_byte_0; rw [← h_x1] at h_byte_1
    rw [← h_x2] at h_byte_2; rw [← h_x3] at h_byte_3
    rw [← h_x4] at h_byte_4; rw [← h_x5] at h_byte_5
    rw [← h_x6] at h_byte_6; rw [← h_x7] at h_byte_7
    -- Discharge ALUBus.Spec 2: result_range ∧ operand_range ∧ XOR equation
    refine ⟨ ⟨by grind, by grind, by grind, by grind⟩,
             ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption⟩,
             ?_ ⟩
    -- Move to U64b and solve
    iterate 4 rw [bv16_from_bytes _ _ (by omega) (by omega)]
    rw [← U64w.toU64b_toBV, U64w.toU64b_from_split]
    simp [h_b0_split, h_b1_split, h_b2_split, h_b3_split,
          h_c0_split, h_c1_split, h_c2_split, h_c3_split]
    iterate 2 rw [← U64w.toU64b_toBV, U64w.toU64b_from_split]
    simp [RV64IM.execute_RTYPE_pure, U64b.toBV]
    repeat rw [BitVec.xor_append]
    simp [h_byte_0, h_byte_1, h_byte_2, h_byte_3, h_byte_4, h_byte_5, h_byte_6, h_byte_7]

  --
  -- spec_OR — opcode 3
  --

  lemma spec_OR
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseChip.Extraction.allHold air row)
    (h_or : air.cols.values.is_or row 0 = 1)
  :
    ALUBus.Spec 3
      ((air.cols.values.bitwise.bitwise.result_0 row 0) + (air.cols.values.bitwise.bitwise.result_1 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_2 row 0) + (air.cols.values.bitwise.bitwise.result_3 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_4 row 0) + (air.cols.values.bitwise.bitwise.result_5 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_6 row 0) + (air.cols.values.bitwise.bitwise.result_7 row 0) * 256)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    -- Establish that is_xor = is_and = 0, hence is_real = 1
    obtain ⟨ _, h_or_excl, _ ⟩ := selector_exclusivity air row h_constraints
    obtain ⟨ h_xor, h_and ⟩ := h_or_excl h_or
    have h_real : air.cols.values.is_real row 0 = 1 := by
      show air.cols.values.is_xor row 0 + air.cols.values.is_or row 0 + air.cols.values.is_and row 0 = 1
      rw [h_xor, h_or, h_and]; ring
    -- Extract the 8 byte-bus assumptions (OR opcode 1 at byte level)
    simp [bus_row_wf_asm, bus_row, h_xor, h_or, h_and, h_real, ByteBus.Spec] at h_wf
    obtain ⟨⟨h_x0, h_r0, h_bL0, h_cL0⟩,
            ⟨h_x1, h_r1, h_bH0, h_cH0⟩,
            ⟨h_x2, h_r2, h_bL1, h_cL1⟩,
            ⟨h_x3, h_r3, h_bH1, h_cH1⟩,
            ⟨h_x4, h_r4, h_bL2, h_cL2⟩,
            ⟨h_x5, h_r5, h_bH2, h_cH2⟩,
            ⟨h_x6, h_r6, h_bL3, h_cL3⟩,
            ⟨h_x7, h_r7, h_bH3, h_cH3⟩⟩ := h_wf
    obtain ⟨h_b0_range, h_b0_split⟩ := limb_decomp _ _ h_bL0 h_bH0
    obtain ⟨h_b1_range, h_b1_split⟩ := limb_decomp _ _ h_bL1 h_bH1
    obtain ⟨h_b2_range, h_b2_split⟩ := limb_decomp _ _ h_bL2 h_bH2
    obtain ⟨h_b3_range, h_b3_split⟩ := limb_decomp _ _ h_bL3 h_bH3
    obtain ⟨h_c0_range, h_c0_split⟩ := limb_decomp _ _ h_cL0 h_cH0
    obtain ⟨h_c1_range, h_c1_split⟩ := limb_decomp _ _ h_cL1 h_cH1
    obtain ⟨h_c2_range, h_c2_split⟩ := limb_decomp _ _ h_cL2 h_cH2
    obtain ⟨h_c3_range, h_c3_split⟩ := limb_decomp _ _ h_cL3 h_cH3
    have h_a0_split := bv16_from_bytes _ _ h_r0 h_r1
    have h_a1_split := bv16_from_bytes _ _ h_r2 h_r3
    have h_a2_split := bv16_from_bytes _ _ h_r4 h_r5
    have h_a3_split := bv16_from_bytes _ _ h_r6 h_r7
    have h_byte_0 := FKB.ofNat_or_eq _ _ h_bL0 h_cL0
    have h_byte_1 := FKB.ofNat_or_eq _ _ h_bH0 h_cH0
    have h_byte_2 := FKB.ofNat_or_eq _ _ h_bL1 h_cL1
    have h_byte_3 := FKB.ofNat_or_eq _ _ h_bH1 h_cH1
    have h_byte_4 := FKB.ofNat_or_eq _ _ h_bL2 h_cL2
    have h_byte_5 := FKB.ofNat_or_eq _ _ h_bH2 h_cH2
    have h_byte_6 := FKB.ofNat_or_eq _ _ h_bL3 h_cL3
    have h_byte_7 := FKB.ofNat_or_eq _ _ h_bH3 h_cH3
    rw [← h_x0] at h_byte_0; rw [← h_x1] at h_byte_1
    rw [← h_x2] at h_byte_2; rw [← h_x3] at h_byte_3
    rw [← h_x4] at h_byte_4; rw [← h_x5] at h_byte_5
    rw [← h_x6] at h_byte_6; rw [← h_x7] at h_byte_7
    refine ⟨ ⟨by grind, by grind, by grind, by grind⟩,
             ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption⟩,
             ?_ ⟩
    -- Move to U64b and solve
    iterate 4 rw [bv16_from_bytes _ _ (by omega) (by omega)]
    rw [← U64w.toU64b_toBV, U64w.toU64b_from_split]
    simp [h_b0_split, h_b1_split, h_b2_split, h_b3_split,
          h_c0_split, h_c1_split, h_c2_split, h_c3_split]
    iterate 2 rw [← U64w.toU64b_toBV, U64w.toU64b_from_split]
    simp [RV64IM.execute_RTYPE_pure, U64b.toBV]
    repeat rw [BitVec.or_append]
    simp [h_byte_0, h_byte_1, h_byte_2, h_byte_3, h_byte_4, h_byte_5, h_byte_6, h_byte_7]

  --
  -- spec_AND — opcode 4
  --

  lemma spec_AND
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseChip.Extraction.allHold air row)
    (h_and : air.cols.values.is_and row 0 = 1)
  :
    ALUBus.Spec 4
      ((air.cols.values.bitwise.bitwise.result_0 row 0) + (air.cols.values.bitwise.bitwise.result_1 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_2 row 0) + (air.cols.values.bitwise.bitwise.result_3 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_4 row 0) + (air.cols.values.bitwise.bitwise.result_5 row 0) * 256)
      ((air.cols.values.bitwise.bitwise.result_6 row 0) + (air.cols.values.bitwise.bitwise.result_7 row 0) * 256)
      (air.cols.values.b_0 row 0) (air.cols.values.b_1 row 0)
      (air.cols.values.b_2 row 0) (air.cols.values.b_3 row 0)
      (air.cols.values.c_0 row 0) (air.cols.values.c_1 row 0)
      (air.cols.values.c_2 row 0) (air.cols.values.c_3 row 0)
  := by
    -- Establish that is_xor = is_or = 0, hence is_real = 1
    obtain ⟨ _, _, h_and_excl ⟩ := selector_exclusivity air row h_constraints
    obtain ⟨ h_xor, h_or ⟩ := h_and_excl h_and
    have h_real : air.cols.values.is_real row 0 = 1 := by
      show air.cols.values.is_xor row 0 + air.cols.values.is_or row 0 + air.cols.values.is_and row 0 = 1
      rw [h_xor, h_or, h_and]; ring
    -- Extract the 8 byte-bus assumptions (AND opcode 0 at byte level)
    simp [bus_row_wf_asm, bus_row, h_xor, h_or, h_and, h_real, ByteBus.Spec] at h_wf
    obtain ⟨⟨h_x0, h_r0, h_bL0, h_cL0⟩,
            ⟨h_x1, h_r1, h_bH0, h_cH0⟩,
            ⟨h_x2, h_r2, h_bL1, h_cL1⟩,
            ⟨h_x3, h_r3, h_bH1, h_cH1⟩,
            ⟨h_x4, h_r4, h_bL2, h_cL2⟩,
            ⟨h_x5, h_r5, h_bH2, h_cH2⟩,
            ⟨h_x6, h_r6, h_bL3, h_cL3⟩,
            ⟨h_x7, h_r7, h_bH3, h_cH3⟩⟩ := h_wf
    obtain ⟨h_b0_range, h_b0_split⟩ := limb_decomp _ _ h_bL0 h_bH0
    obtain ⟨h_b1_range, h_b1_split⟩ := limb_decomp _ _ h_bL1 h_bH1
    obtain ⟨h_b2_range, h_b2_split⟩ := limb_decomp _ _ h_bL2 h_bH2
    obtain ⟨h_b3_range, h_b3_split⟩ := limb_decomp _ _ h_bL3 h_bH3
    obtain ⟨h_c0_range, h_c0_split⟩ := limb_decomp _ _ h_cL0 h_cH0
    obtain ⟨h_c1_range, h_c1_split⟩ := limb_decomp _ _ h_cL1 h_cH1
    obtain ⟨h_c2_range, h_c2_split⟩ := limb_decomp _ _ h_cL2 h_cH2
    obtain ⟨h_c3_range, h_c3_split⟩ := limb_decomp _ _ h_cL3 h_cH3
    have h_a0_split := bv16_from_bytes _ _ h_r0 h_r1
    have h_a1_split := bv16_from_bytes _ _ h_r2 h_r3
    have h_a2_split := bv16_from_bytes _ _ h_r4 h_r5
    have h_a3_split := bv16_from_bytes _ _ h_r6 h_r7
    have h_byte_0 := FKB.ofNat_and_eq
      (air.cols.values.bitwise.b_low_bytes.low_bytes_0 row 0) _ h_cL0
    have h_byte_1 := FKB.ofNat_and_eq
      ((air.cols.values.b_0 row 0 - air.cols.values.bitwise.b_low_bytes.low_bytes_0 row 0) * 2122383361) _ h_cH0
    have h_byte_2 := FKB.ofNat_and_eq
      (air.cols.values.bitwise.b_low_bytes.low_bytes_1 row 0) _ h_cL1
    have h_byte_3 := FKB.ofNat_and_eq
      ((air.cols.values.b_1 row 0 - air.cols.values.bitwise.b_low_bytes.low_bytes_1 row 0) * 2122383361) _ h_cH1
    have h_byte_4 := FKB.ofNat_and_eq
      (air.cols.values.bitwise.b_low_bytes.low_bytes_2 row 0) _ h_cL2
    have h_byte_5 := FKB.ofNat_and_eq
      ((air.cols.values.b_2 row 0 - air.cols.values.bitwise.b_low_bytes.low_bytes_2 row 0) * 2122383361) _ h_cH2
    have h_byte_6 := FKB.ofNat_and_eq
      (air.cols.values.bitwise.b_low_bytes.low_bytes_3 row 0) _ h_cL3
    have h_byte_7 := FKB.ofNat_and_eq
      ((air.cols.values.b_3 row 0 - air.cols.values.bitwise.b_low_bytes.low_bytes_3 row 0) * 2122383361) _ h_cH3
    rw [← h_x0] at h_byte_0; rw [← h_x1] at h_byte_1
    rw [← h_x2] at h_byte_2; rw [← h_x3] at h_byte_3
    rw [← h_x4] at h_byte_4; rw [← h_x5] at h_byte_5
    rw [← h_x6] at h_byte_6; rw [← h_x7] at h_byte_7
    refine ⟨ ⟨by grind, by grind, by grind, by grind⟩,
             ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption⟩,
             ?_ ⟩
    -- Move to U64b and solve
    iterate 4 rw [bv16_from_bytes _ _ (by omega) (by omega)]
    rw [← U64w.toU64b_toBV, U64w.toU64b_from_split]
    simp [h_b0_split, h_b1_split, h_b2_split, h_b3_split,
          h_c0_split, h_c1_split, h_c2_split, h_c3_split]
    iterate 2 rw [← U64w.toU64b_toBV, U64w.toU64b_from_split]
    simp [RV64IM.execute_RTYPE_pure, U64b.toBV]
    repeat rw [BitVec.and_append]
    simp [h_byte_0, h_byte_1, h_byte_2, h_byte_3, h_byte_4, h_byte_5, h_byte_6, h_byte_7]

  --
  -- Externals (vacuous for byte; ALU entry's externals only fire when
  -- the chip *consumes* an entry — chip emits, so no assertion needed)
  --

  lemma ext_asrt
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (_h_ext_asm : bus_row_ext_asm (bus_row air row))
    (_h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseChip.Extraction.allHold air row)
  :
    bus_row_ext_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_ext_asrt, bus_row, Valid_BitwiseValueCols.is_real]
    intro h; exfalso; grind

  --
  -- wf_asrt — dispatches to spec_XOR/OR/AND
  --

  lemma wf_asrt
    [Field ExtF]
    (air : Valid_BitwiseChip FKB ExtF)
    (row : ℕ)
    (h_wf : bus_row_wf_asm (bus_row air row))
    (h_constraints : BitwiseChip.Extraction.allHold air row)
  :
    bus_row_wf_asrt (bus_row air row)
  := by
    have selectors := selector_breakdown air row h_constraints
    simp [bus_row_wf_asrt, bus_row, Valid_BitwiseValueCols.is_real]
    refine ⟨?_, ?_⟩
    -- ALU entry: dispatch to spec_XOR / spec_OR / spec_AND based on which
    -- selector is active (exactly one, since is_real = sum = 1).
    . intro h_real
      obtain ⟨h_xor_disj, h_or_disj, _, _⟩ := selectors
      rcases h_xor_disj with h_xor | h_xor
      · rcases h_or_disj with h_or | h_or
        · have h_and : air.cols.values.is_and row 0 = 1 := by grind
          simp [h_xor, h_or, h_and]
          exact spec_AND air row h_wf h_constraints h_and
        · have h_and : air.cols.values.is_and row 0 = 0 := by grind
          simp [h_xor, h_or, h_and]
          exact spec_OR air row h_wf h_constraints h_or
      · have h_or : air.cols.values.is_or row 0 = 0 := by grind
        have h_and : air.cols.values.is_and row 0 = 0 := by grind
        simp [h_xor, h_or, h_and]
        exact spec_XOR air row h_wf h_constraints h_xor
    -- Byte entries: vacuous (multiplicity = -is_real ∈ {0, -1}, never 1).
    . split_ands <;> intro h <;> exfalso <;> grind

end BitwiseChip.Spec
