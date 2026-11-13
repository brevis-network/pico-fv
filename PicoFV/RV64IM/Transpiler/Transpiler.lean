import LeanRV64D
import Mathlib

import PicoFV.Fundamentals.KoalaBear
import PicoFV.RV64IM.RVSail.Auxiliaries

namespace Transpiler

  open RV64IM

  /-! ## Register helpers -/

  /-- Convert a 5-bit register index to an `FKB` value. Registers fit trivially
      in the field since `0 ≤ idx < 32 < KB_prime`. -/
  def reg_to_KB (rd : regidx) : FKB :=
    ⟨(regidx_to_fin rd).val, by omega⟩

  /-- An `FKB` element represents a valid register index iff it lies in
      `[0, 32)`. -/
  def is_register (reg : FKB) : Prop :=
    reg < 32

  /-! ## Immediate decomposition

      In RV64 Pico, a `Word<T>` is `[T; 4]` with each `T` holding a u16 limb
      (the four 16-bit limbs together encode a 64-bit value). The transpiler
      therefore sign-extends (or zero-extends) the Sail immediate to 64 bits
      and decomposes it into 4 × 16-bit limbs that are then lifted into the
      field.

      The corresponding RV32 helper produced 4 × 8-bit byte limbs of a
      sign/zero-extended 32-bit value. The shape (4 limbs) is the same; the
      per-limb width is the only structural difference.                       -/

  /-- Decompose a `BitVec w` extended to 64 bits into 4 × u16 limbs, each
      lifted into `FKB`. The element ordering is little-endian
      (`limb[0]` = bits 15..0, `limb[3]` = bits 63..48).

      Mirrors the RV32 helper `Vector.map (·.toNat) ∘ U32b.fromNat` pattern:
      we first build the 64-bit value's 4-u16-limb decomposition as a
      `U64w` (`Vector (BitVec 16) 4`) via `U64w.fromNat`, then lift each
      `BitVec 16` limb into `FKB` (sound because `2^16 - 1 < KB_prime`). -/
  def imm_to_KB {w : ℕ} (imm : BitVec w) (sgn : Bool) : Vector FKB 4 :=
    let imm_u64w := U64w.fromNat (BitVec.extend imm 64 sgn).toNat
    Vector.map (fun x => ⟨ x.toNat, by omega ⟩) imm_u64w

  /-- Each limb produced by `imm_to_KB` is a valid u16 value. -/
  lemma imm_to_KB_limbs {w : ℕ} (imm : BitVec w) (sgn : Bool) :
    (imm_to_KB imm sgn)[0] < 65536 ∧ (imm_to_KB imm sgn)[1] < 65536 ∧
    (imm_to_KB imm sgn)[2] < 65536 ∧ (imm_to_KB imm sgn)[3] < 65536
  := by
    simp [imm_to_KB, U64w.fromNat, Fin.lt_def]; omega

  /-! ### Signed-extension lemmas (sgn = true)

      Lemma statements use `U64w.toBV` / `U64w.toNat` / `U64w.toInt` from
      `Word.lean` (`Vector (BitVec 16) 4`), with the implicit
      `FKB → BitVec 16` coercion from `KoalaBear.lean` lifting each
      `imm_KB[i] : FKB` into a `BitVec 16` limb.
                                                                          -/

  lemma imm_to_KB_BV_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U64w.toBV #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    BitVec.signExtend 64 imm
  := by
    simp [← BitVec.toNat_inj]
    simp [
      U64w.toNat,
      imm_to_KB,
      U64w.fromNat,
      BitVec.extend,
    ]
    omega

  lemma imm_to_KB_Nat_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U64w.toNat #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.signExtend 64 imm).toNat
  := by
    simp [← imm_to_KB_BV_sgn]

  lemma imm_to_KB_Int_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U64w.toInt #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.signExtend 64 imm).toInt
  := by
    simp [← imm_to_KB_BV_sgn]

  /-! ### Zero-extension lemmas (sgn = false) -/

  lemma imm_to_KB_BV_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U64w.toBV #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    BitVec.zeroExtend 64 imm
  := by
    simp [← BitVec.toNat_inj]
    simp [
      U64w.toNat,
      imm_to_KB,
      U64w.fromNat,
      BitVec.extend,
    ]
    omega

  lemma imm_to_KB_Nat_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U64w.toNat #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.zeroExtend 64 imm).toNat
  := by
    simp [← imm_to_KB_BV_usgn]

  lemma imm_to_KB_Int_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U64w.toInt #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.zeroExtend 64 imm).toInt
  := by
    simp [← imm_to_KB_BV_usgn]

  /-! ### Signed-extension lemmas for W-imms (sgn = true) -/

  set_option maxHeartbeats 1_000_000 in
  lemma immw_to_KB_BV_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U32w.toBV #v[imm_KB[0], imm_KB[1]] =
    BitVec.signExtend 32 imm
  := by
    simp [
      imm_to_KB,
      U64w.fromNat,
      BitVec.extend,
    ]
    by_cases h_w_32 : w ≤ 32
    . simp [← BitVec.toNat_inj, BitVec.toNat_signExtend, U32w.toNat, BitVec.msb_eq_decide]
      have ub_pow_32 : 2 ^ w ≤ 4294967296 := by interval_cases w <;> simp
      have ub_pow_64 : 2 ^ w ≤ 18446744073709551616 := by interval_cases w <;> simp
      rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
      repeat rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)]
      split_ifs <;> interval_cases w <;> simp at * <;> omega
    . simp [← BitVec.toNat_inj, U32w.toNat, BitVec.toNat_signExtend]
      split_ifs with h_if
      . by_cases h_w_64 : w ≤ 64
        . interval_cases w <;> simp at * <;> omega
        . suffices h_zero : 2 ^ 64 < 2 ^ w
          . omega
          . exact Nat.pow_lt_pow_right (by simp) (by omega)
      . omega

  lemma immw_to_KB_Nat_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U32w.toNat #v[imm_KB[0], imm_KB[1]] =
    (BitVec.signExtend 32 imm).toNat
  := by
    simp [← immw_to_KB_BV_sgn]

  lemma immw_to_KB_Int_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U32w.toInt #v[imm_KB[0], imm_KB[1]] =
    (BitVec.signExtend 32 imm).toInt
  := by
    simp [← immw_to_KB_BV_sgn]

  /-! ### Zero-extension lemmas for W-imms (sgn = false) -/

  lemma immw_to_KB_BV_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U32w.toBV #v[imm_KB[0], imm_KB[1]] =
    BitVec.setWidth 32 imm
  := by
    simp [← BitVec.toNat_inj]
    simp [
      U32w.toNat,
      imm_to_KB,
      U64w.fromNat,
      BitVec.extend,
    ]
    omega

  lemma immw_to_KB_Nat_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U32w.toNat #v[imm_KB[0], imm_KB[1]] =
    (BitVec.setWidth 32 imm).toNat
  := by
    simp [← immw_to_KB_BV_usgn]

  lemma immw_to_KB_Int_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U32w.toInt #v[imm_KB[0], imm_KB[1]] =
    (BitVec.setWidth 32 imm).toInt
  := by
    simp [← immw_to_KB_BV_usgn]


  /-! ## Opcode encodings

      These mirror the Pico `Opcode` enum at
      `vm/src/compiler/riscv/opcode.rs` (commit
      `22b0aae6321c1f63c72aafd0b506b5f45b91ffb1`). The RV32 codes for
      common-base ALU/branch/jump/memory ops are unchanged; RV64 adds the
      W-variants (40..44, 48..52) and the new `LWU/LD/SD` memory ops
      (45..47).                                                                -/

  def opcode_of_rop (op : rop) : FKB :=
    match op with
    | .ADD  => 0
    | .SUB  => 1
    | .XOR  => 2
    | .OR   => 3
    | .AND  => 4
    | .SLL  => 5
    | .SRL  => 6
    | .SRA  => 7
    | .SLT  => 8
    | .SLTU => 9

  def opcode_of_iop (op : iop) : FKB :=
    match op with
    | .ADDI  => 0
    | .XORI  => 2
    | .ORI   => 3
    | .ANDI  => 4
    | .SLTI  => 8
    | .SLTIU => 9

  def opcode_of_sop (op : sop) : FKB :=
    match op with
    | .SLLI => 5
    | .SRLI => 6
    | .SRAI => 7

  def opcode_of_bop (op : bop) : FKB :=
    match op with
    | .BEQ  => 18
    | .BNE  => 19
    | .BLT  => 20
    | .BGE  => 21
    | .BLTU => 22
    | .BGEU => 23

  def opcode_of_uop (op : uop) : FKB :=
    match op with
    | .LUI   => 0      -- LUI is encoded as `ADD rd, x0, imm` (see rrs.rs)
    | .AUIPC => 27

  /-- RV64-only: word-size R-type opcodes (ADDW/SUBW/SLLW/SRLW/SRAW). -/
  def opcode_of_ropw (op : ropw) : FKB :=
    match op with
    | .ADDW => 40
    | .SUBW => 41
    | .SLLW => 42
    | .SRLW => 43
    | .SRAW => 44

  /-- RV64-only: word-size shift-immediate opcodes (SLLIW/SRLIW/SRAIW). -/
  def opcode_of_sopw (op : sopw) : FKB :=
    match op with
    | .SLLIW => 42
    | .SRLIW => 43
    | .SRAIW => 44

  /-! ## Transpilation

      Maps a Sail `instruction` to the program-bus payload row carried on the
      `Program` lookup bus, expressed as a `Vector FKB 43`. The 43-element
      layout follows the RV64 `CpuChip` program-bus call extracted from
      `Extraction/CpuChip.lean:453` at the tag `pico-v3-before-cpu` (2.x):

      ```
      [ pc[0], pc[1], pc[2],
        opcode,                                            -- emitted once
        opcode, op_a[0..3], op_b[0..3], op_c[0..3], op_a_0, -- InstructionCols (14)
        imm_b, imm_c, is_alu, is_ecall,                    -- OpcodeSelectorCols (25)
        is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld,
        is_sb, is_sh, is_sw, is_sd,
        is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
        is_jalr, is_jal,
        is_auipc, is_unimpl ]
      ```

      Total payload size after the bus tag: `3 + 1 + 14 + 25 = 43`.

      Compared to RV32's 38-element payload:
      - `pc` widens from `1` field to `3` field limbs (`Addr<T> = [T; 3]`).
      - `OpcodeSelectorCols` grows by 3 (`is_lwu`, `is_ld`, `is_sd`).
      - Operand slots (`op_a/b/c`) still hold 4 field limbs each; only the
        *interpretation* of each limb changes (u16 instead of u8).
                                                                                -/

  /-- Transpile a single Sail instruction at PC `pc` to a (multiplicity,
      bus-payload, precondition) triple. The PC is supplied as three u16
      limbs since RV64 stores it as `Addr<T> = [T; 3]` (covering a 48-bit
      address space). Returns `none` for unsupported instructions. -/
  def transpile_op
    (inst : instruction)
    (multiplicity : FKB)
    (pc : Vector FKB 3)
  : Option ((FKB × Vector FKB 43) × Prop) :=
    match inst with
    -- ====================================================================
    -- RTYPE : 10 opcodes — register-register ALU ops
    -- ====================================================================
    | .RTYPE (rs2, rs1, rd, op) =>
      let opcode := opcode_of_rop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,            -- imm_b, imm_c
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,  -- is_lb..is_ld
            0, 0, 0, 0,      -- is_sb..is_sd
            0, 0, 0, 0, 0, 0,  -- is_beq..is_bgeu
            0, 0,            -- is_jalr, is_jal
            0, 0             -- is_auipc, is_unimpl
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- RTYPEW : 5 opcodes — register-register W-variant ALU ops (RV64-only)
    -- ====================================================================
    | .RTYPEW (rs2, rs1, rd, op) =>
      let opcode := opcode_of_ropw op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,            -- imm_b, imm_c
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- ITYPE : 6 opcodes — register-immediate ALU ops
    -- ====================================================================
    | .ITYPE (imm, rs1, rd, op) =>
      let opcode := opcode_of_iop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,            -- imm_b = 0, imm_c = 1
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- ====================================================================
    -- ADDIW : ADD-immediate-word (RV64-only single-constructor opcode)
    -- ====================================================================
    | .ADDIW (imm, rs1, rd) =>
      let opcode : FKB := 40        -- ADDW
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,            -- imm_b = 0, imm_c = 1
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- ====================================================================
    -- SHIFTIOP : 3 opcodes — shift-immediate (SLLI/SRLI/SRAI)
    -- 6-bit shift amount on RV64 (vs 5-bit on RV32); zero-extended.
    -- ====================================================================
    | .SHIFTIOP (imm, rs1, rd, op) =>
      let opcode := opcode_of_sop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm false
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,            -- imm_b = 0, imm_c = 1
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- ====================================================================
    -- SHIFTIWOP : 3 opcodes — W-variant shift-immediate (RV64-only)
    -- 5-bit shift amount; zero-extended.
    -- ====================================================================
    | .SHIFTIWOP (imm, rs1, rd, op) =>
      let opcode := opcode_of_sopw op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm false
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,            -- imm_b = 0, imm_c = 1
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- ====================================================================
    -- LOAD : 7 opcodes — LB/LBU/LH/LHU/LW/LWU/LD
    -- Sail encoding: `(imm, rs1, rd, is_unsigned, width)`.
    -- Note: in RV64, `LW` is *signed* (sign-extended to 64 bits), so it is
    -- emitted by Sail as `(false, 4)`; `LWU` is `(true, 4)`. This differs
    -- from RV32 where `LW` was `(true, 4)`.
    -- ====================================================================
    | .LOAD (imm, rs1, rd, is_unsigned, width) =>
      let opcode : FKB :=
        match is_unsigned, width with
        | false, 1 => 10   -- LB
        | true,  1 => 13   -- LBU
        | false, 2 => 11   -- LH
        | true,  2 => 14   -- LHU
        | false, 4 => 12   -- LW   (signed, RV64-style)
        | true,  4 => 45   -- LWU  (new for RV64)
        | false, 8 => 46   -- LD   (new for RV64)
        | _, _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
        let imm_KB := imm_to_KB imm true
        .some (
          (
            multiplicity,
            #v[
              pc[0], pc[1], pc[2], opcode, opcode,
              reg_to_KB rd, 0, 0, 0,
              reg_to_KB rs1, 0, 0, 0,
              imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
              a_is_0,
              0, 1,            -- imm_b = 0, imm_c = 1
              0, 0,            -- is_alu = 0, is_ecall = 0
              (if opcode = 10 then 1 else 0),   -- is_lb
              (if opcode = 13 then 1 else 0),   -- is_lbu
              (if opcode = 11 then 1 else 0),   -- is_lh
              (if opcode = 14 then 1 else 0),   -- is_lhu
              (if opcode = 12 then 1 else 0),   -- is_lw
              (if opcode = 45 then 1 else 0),   -- is_lwu (new)
              (if opcode = 46 then 1 else 0),   -- is_ld  (new)
              0, 0, 0, 0,      -- is_sb..is_sd
              0, 0, 0, 0, 0, 0,
              0, 0,
              0, 0
            ]
          ),
          is_register (reg_to_KB rd) ∧
          is_register (reg_to_KB rs1)
        )
    -- ====================================================================
    -- STORE : 4 opcodes — SB/SH/SW/SD
    -- Sail encoding: `(imm, rs2, rs1, width)`. SD is new for RV64.
    -- ====================================================================
    | .STORE (imm, rs2, rs1, width) =>
      let opcode : FKB :=
        match width with
        | 1 => 15   -- SB
        | 2 => 16   -- SH
        | 4 => 17   -- SW
        | 8 => 47   -- SD (new for RV64)
        | _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 : FKB := 0
        let imm_KB := imm_to_KB imm true
        .some (
          (
            multiplicity,
            #v[
              pc[0], pc[1], pc[2], opcode, opcode,
              reg_to_KB rs2, 0, 0, 0,
              reg_to_KB rs1, 0, 0, 0,
              imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
              a_is_0,
              0, 1,            -- imm_b = 0, imm_c = 1
              0, 0,            -- is_alu = 0, is_ecall = 0
              0, 0, 0, 0, 0, 0, 0,   -- is_lb..is_ld
              (if opcode = 15 then 1 else 0),   -- is_sb
              (if opcode = 16 then 1 else 0),   -- is_sh
              (if opcode = 17 then 1 else 0),   -- is_sw
              (if opcode = 47 then 1 else 0),   -- is_sd (new)
              0, 0, 0, 0, 0, 0,
              0, 0,
              0, 0
            ]
          ),
          is_register (reg_to_KB rs1) ∧
          is_register (reg_to_KB rs2)
        )
    -- ====================================================================
    -- BTYPE : 6 opcodes — conditional branches
    -- Branch offset must be 2-byte-aligned.
    -- ====================================================================
    | .BTYPE (imm, rs2, rs1, op) =>
      let opcode := opcode_of_bop op
      let a_is_0 : FKB := 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,            -- imm_b = 0, imm_c = 1
            0, 0,            -- is_alu = 0, is_ecall = 0
            0, 0, 0, 0, 0, 0, 0,   -- is_lb..is_ld
            0, 0, 0, 0,      -- is_sb..is_sd
            (if op == .BEQ  then 1 else 0),
            (if op == .BNE  then 1 else 0),
            (if op == .BLT  then 1 else 0),
            (if op == .BGE  then 1 else 0),
            (if op == .BLTU then 1 else 0),
            (if op == .BGEU then 1 else 0),
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2) ∧
        imm % 2 = 0
      )
    -- ====================================================================
    -- JALR : indirect jump
    -- Offset must be 2-byte-aligned.
    -- ====================================================================
    | .JALR (imm, rs1, rd) =>
      let opcode : FKB := 25
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,            -- imm_b = 0, imm_c = 1
            0, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            1, 0,            -- is_jalr = 1
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        imm % 2 = 0
      )
    -- ====================================================================
    -- JAL : direct jump
    -- ====================================================================
    | .JAL (imm, rd) =>
      let opcode : FKB := 24
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            0, 0, 0, 0,
            a_is_0,
            1, 1,            -- imm_b = 1, imm_c = 1
            0, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 1,            -- is_jal = 1
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        imm % 2 = 0
      )
    -- ====================================================================
    -- UTYPE : 2 opcodes (LUI → ADD with imm; AUIPC)
    -- Sail's `imm` is the upper-20-bit field; we shift it left by 12 to get
    -- the actual immediate value, then sign-extend to 64 bits. The
    -- precondition `imm % 4096 = 0` is automatic from `(imm ++ 0#12)`.
    -- ====================================================================
    | .UTYPE (imm, rd, op) =>
      let opcode := opcode_of_uop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB (imm ++ 0#12) true
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            (if op == .AUIPC then imm_KB[0] else 0),
            (if op == .AUIPC then imm_KB[1] else 0),
            (if op == .AUIPC then imm_KB[2] else 0),
            (if op == .AUIPC then imm_KB[3] else 0),
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            1, 1,            -- imm_b = 1, imm_c = 1
            (if op == .LUI then 1 else 0), 0,   -- is_alu (LUI), is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            (if op == .AUIPC then 1 else 0), 0  -- is_auipc, is_unimpl
          ]
        ),
        is_register (reg_to_KB rd) ∧
        imm % 4096 = 0
      )
    -- ====================================================================
    -- MUL : 4 opcodes (MUL/MULH/MULHU/MULHSU)
    -- Same constructor shape as RV32; MULW is a separate constructor.
    -- ====================================================================
    | .MUL (rs2, rs1, rd, op) =>
      let opcode : FKB :=
        match op with
        | { result_part := .Low,  signed_rs1 := _,         signed_rs2 := _ }         => 30  -- MUL
        | { result_part := .High, signed_rs1 := .Signed,   signed_rs2 := .Signed }   => 31  -- MULH
        | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => 32  -- MULHU
        | { result_part := .High, signed_rs1 := .Signed,   signed_rs2 := .Unsigned } => 33  -- MULHSU
        | _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
        .some (
          (
            multiplicity,
            #v[
              pc[0], pc[1], pc[2], opcode, opcode,
              reg_to_KB rd, 0, 0, 0,
              reg_to_KB rs1, 0, 0, 0,
              reg_to_KB rs2, 0, 0, 0,
              a_is_0,
              0, 0,            -- imm_b, imm_c
              1, 0,            -- is_alu, is_ecall
              0, 0, 0, 0, 0, 0, 0,
              0, 0, 0, 0,
              0, 0, 0, 0, 0, 0,
              0, 0,
              0, 0
            ]
          ),
          is_register (reg_to_KB rd) ∧
          is_register (reg_to_KB rs1) ∧
          is_register (reg_to_KB rs2)
        )
    -- ====================================================================
    -- MULW : 1 opcode (RV64-only)
    -- Sail constructor: `MULW (rs2, rs1, rd)`.
    -- ====================================================================
    | .MULW (rs2, rs1, rd) =>
      let opcode : FKB := 48
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,            -- imm_b, imm_c
            1, 0,            -- is_alu, is_ecall
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- DIV : 2 opcodes (DIV/DIVU)
    -- ====================================================================
    | .DIV (rs2, rs1, rd, sgn) =>
      -- `sgn` here is Sail's `is_unsigned` field: `true` = DIVU, `false` = DIV.
      -- Chip opcode 34 = DIV (signed, `.DRS` arm), opcode 35 = DIVU (unsigned, `.DRU` arm).
      let opcode : FKB := match sgn with | true => 35 | false => 34   -- DIVU / DIV
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0,
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- DIVW : 2 opcodes (DIVW/DIVUW) — RV64-only
    -- ====================================================================
    | .DIVW (rs2, rs1, rd, sgn) =>
      -- `sgn` = Sail's `is_unsigned`: `true` = DIVUW, `false` = DIVW.
      -- Chip opcode 49 = DIVW (signed), opcode 50 = DIVUW (unsigned).
      let opcode : FKB := match sgn with | true => 50 | false => 49   -- DIVUW / DIVW
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0,
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- REM : 2 opcodes (REM/REMU)
    -- ====================================================================
    | .REM (rs2, rs1, rd, sgn) =>
      -- `sgn` = Sail's `is_unsigned`: `true` = REMU, `false` = REM.
      -- Chip opcode 36 = REM (signed), opcode 37 = REMU (unsigned).
      let opcode : FKB := match sgn with | true => 37 | false => 36   -- REMU / REM
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0,
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- REMW : 2 opcodes (REMW/REMUW) — RV64-only
    -- ====================================================================
    | .REMW (rs2, rs1, rd, sgn) =>
      -- `sgn` = Sail's `is_unsigned`: `true` = REMUW, `false` = REMW.
      -- Chip opcode 51 = REMW (signed), opcode 52 = REMUW (unsigned).
      let opcode : FKB := match sgn with | true => 52 | false => 51   -- REMUW / REMW
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc[0], pc[1], pc[2], opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0,
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0,
            0, 0, 0, 0, 0, 0,
            0, 0,
            0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ====================================================================
    -- Unimplemented Sail constructor → no bus row.
    -- (ECALL/EBREAK, FENCE-class etc.; add here if/when needed.)
    -- ====================================================================
    | _ => .none

end Transpiler
