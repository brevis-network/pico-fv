import LeanRV32D
import Mathlib

import PicoFV.Fundamentals.KoalaBear
import PicoFV.RVSail.RV32IM.Auxiliaries

namespace Transpiler

  open RV32IM

  def reg_to_KB (rd : regidx) : FKB :=
    ⟨(regidx_to_fin rd).val, by omega⟩

  def is_register (reg : FKB) : Prop :=
    reg < 32

  def imm_to_KB {w : ℕ} (imm : BitVec w) (sgn : Bool) : Vector FKB 4 :=
    let imm_u32 := U32.fromNat (BitVec.extend imm 32 sgn).toNat
    Vector.map (fun x => ⟨ x.toNat, by omega ⟩) imm_u32

  lemma imm_to_KB_BV_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U32.toBV #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    BitVec.signExtend 32 imm
  := by
    simp [← BitVec.toNat_inj]
    simp [
      U32.toNat,
      imm_to_KB,
      U32.fromNat,
      BitVec.extend,
    ]
    omega

  lemma imm_to_KB_Nat_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U32.toNat #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.signExtend 32 imm).toNat
  := by
    simp [← imm_to_KB_BV_sgn]

  lemma imm_to_KB_Int_sgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm true
    U32.toInt #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.signExtend 32 imm).toInt
  := by
    simp [← imm_to_KB_BV_sgn]

  lemma imm_to_KB_BV_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U32.toBV #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    BitVec.zeroExtend 32 imm
  := by
    simp [← BitVec.toNat_inj]
    simp [
      U32.toNat,
      imm_to_KB,
      U32.fromNat,
      BitVec.extend,
    ]
    omega

  lemma imm_to_KB_Nat_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U32.toNat #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.zeroExtend 32 imm).toNat
  := by
    simp [← imm_to_KB_BV_usgn]

  lemma imm_to_KB_Int_usgn {w : ℕ} (imm : BitVec w) :
    let imm_KB := imm_to_KB imm false
    U32.toInt #v[imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3]] =
    (BitVec.zeroExtend 32 imm).toInt
  := by
    simp [← imm_to_KB_BV_usgn]

  lemma imm_mod_2_to_KB {w : ℕ} (imm : BitVec w) (sgn : Bool)
    (h_imm : imm % 2 = 0)
  :
    let imm_KB := imm_to_KB imm sgn
    imm_KB[0] % 2 = 0
  := by
    simp_all [← BitVec.toNat_inj]
    by_cases h_w : 1 < w
    . rw [Nat.mod_eq_of_lt (a := 2)] at h_imm
      . simp_all [imm_to_KB, U32.fromNat, BitVec.extend]
        split_ifs <;> simp [Fin.ext_iff] <;> [ skip; omega ]
        simp [BitVec.toNat_signExtend]
        repeat rw [Nat.add_mod_eq_sub]
        split_ifs <;> simp_all <;> try omega
        by_cases h_w' : 32 < w
        . have h_pow_w : 4294967296 < 2 ^ w
          := by
            apply lt_of_le_of_lt (b := 2 ^ 32) <;> [ simp; skip ]
            exact Nat.pow_lt_pow_right (by simp) h_w'
          omega
        . simp at h_w'
          interval_cases w <;> simp_all
      . apply lt_of_le_of_lt (b := 2 ^ 1) <;> [ simp; skip ]
        exact Nat.pow_lt_pow_right (by simp) h_w
    . have h_eq : 2 % 2 ^ w = 0
        := by simp at h_w; interval_cases w <;> simp
      rw [h_eq] at h_imm; clear h_eq; simp at h_imm
      have h_eq : imm = 0 := by grind
      simp_all [imm_to_KB, U32.fromNat, BitVec.extend]
      split_ifs <;> simp [BitVec.signExtend]

  lemma imm_mod_4096_to_KB {w : ℕ} (imm : BitVec w) (sgn : Bool)
    (h_imm : imm % 4096 = 0)
  :
    let imm_KB := imm_to_KB imm sgn
    imm_KB[0] = 0 ∧ imm_KB[1] % 4 = 0
  := by
    simp_all [← BitVec.toNat_inj]
    by_cases h_w : 12 < w
    . rw [Nat.mod_eq_of_lt (a := 4096)] at h_imm
      . have h_mod : imm.toNat % 256 = 0 := by omega
        simp_all [imm_to_KB, U32.fromNat, BitVec.extend]
        split_ifs <;> simp [Fin.ext_iff] <;> [ skip; omega ]
        simp [BitVec.toNat_signExtend]
        repeat rw [Nat.add_mod_eq_sub]
        split_ifs <;> simp_all <;> try omega
        by_cases h_w' : 32 < w
        . have h_pow_w : 4294967296 < 2 ^ w
          := by
            apply lt_of_le_of_lt (b := 2 ^ 32) <;> [ simp; skip ]
            exact Nat.pow_lt_pow_right (by simp) h_w'
          omega
        . simp at h_w'
          interval_cases w <;> simp_all <;> omega
      . apply lt_of_le_of_lt (b := 2 ^ 12) <;> [ simp; skip ]
        exact Nat.pow_lt_pow_right (by simp) h_w
    . have h_eq : 4096 % 2 ^ w = 0
        := by simp at h_w; interval_cases w <;> simp
      rw [h_eq] at h_imm; clear h_eq; simp at h_imm
      have h_eq : imm = 0 := by grind
      simp_all [imm_to_KB, U32.fromNat, BitVec.extend]
      split_ifs <;> simp [BitVec.signExtend]

  def opcode_of_rop (op : rop) : FKB :=
    match op with
    | .ADD => 0
    | .SUB => 1
    | .XOR => 2
    | .OR => 3
    | .AND => 4
    | .SLL => 5
    | .SRL => 6
    | .SRA => 7
    | .SLT => 8
    | .SLTU => 9

  def opcode_of_iop (op : iop) : FKB :=
    match op with
    | .ADDI => 0
    | .XORI => 2
    | .ORI => 3
    | .ANDI => 4
    | .SLTI => 8
    | .SLTIU => 9

  def opcode_of_sop (op : sop) : FKB :=
    match op with
    | .SLLI => 5
    | .SRLI => 6
    | .SRAI => 7

  def opcode_of_bop (op : bop) : FKB :=
    match op with
    | .BEQ => 18
    | .BNE => 19
    | .BLT => 20
    | .BGE => 21
    | .BLTU => 22
    | .BGEU => 23

  def opcode_of_uop (op : uop) : FKB :=
    match op with
    | .LUI => 0
    | .AUIPC => 27

  def transpile_op
    (inst : instruction)
    (multiplicity : FKB)
    (pc : FKB)
  : Option ((FKB × Vector FKB 38) × Prop) :=
    match inst with
    -- RTYPE : 10 opcodes
    | .RTYPE (rs2, rs1, rd, op) =>
      let opcode := opcode_of_rop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- ITYPE : 6 opcodes
    | .ITYPE (imm, rs1, rd, op) =>
      let opcode := opcode_of_iop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_12_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_12_KB[0], imm_12_KB[1], imm_12_KB[2], imm_12_KB[3],
            a_is_0,
            0, 1,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- SHIFTIOP : 3 opcodes
    | .SHIFTIOP (imm, rs1, rd, op) =>
      let opcode := opcode_of_sop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm false
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- LOAD : 5 opcodes
    | .LOAD (imm, rs1, rd, is_unsigned, width) =>
      let opcode :=
        match is_unsigned, width with
        | false, 1 => 10 -- LB
        | false, 2 => 11 -- LH
        | true, 4 => 12  -- LW
        | true, 1 => 13  -- LBU
        | true, 2 => 14  -- LHU
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
              pc, opcode, opcode,
              reg_to_KB rd, 0, 0, 0,
              reg_to_KB rs1, 0, 0, 0,
              imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
              a_is_0,
              0, 1,
              0, 0,
              (if opcode = 10 then 1 else 0),
              (if opcode = 13 then 1 else 0),
              (if opcode = 11 then 1 else 0),
              (if opcode = 14 then 1 else 0),
              (if opcode = 12 then 1 else 0),
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
          ),
          is_register (reg_to_KB rd) ∧
          is_register (reg_to_KB rs1)
      )
    -- STORE : 5 opcodes
    | .STORE (imm, rs2, rs1, width) =>
      let opcode :=
        match width with
        | 1 => 15 -- SB
        | 2 => 16 -- SH
        | 4 => 17 -- SW
        | _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 := 0
        let imm_KB := imm_to_KB imm true
        .some (
          (
            multiplicity,
            #v[
              pc, opcode, opcode,
              reg_to_KB rs2, 0, 0, 0,
              reg_to_KB rs1, 0, 0, 0,
              imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
              a_is_0,
              0, 1,
              0, 0, 0, 0, 0, 0, 0,
              (if opcode = 15 then 1 else 0),
              (if opcode = 16 then 1 else 0),
              (if opcode = 17 then 1 else 0),
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
          ),
          is_register (reg_to_KB rs1) ∧
          is_register (reg_to_KB rs2)
      )
    -- BTYPE : 6 opcodes
    | .BTYPE (imm, rs2, rs1, op) =>
      let opcode := opcode_of_bop op
      let a_is_0 := 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            (if op == .BEQ then 1 else 0),
            (if op == .BNE then 1 else 0),
            (if op == .BLT then 1 else 0),
            (if op == .BGE then 1 else 0),
            (if op == .BLTU then 1 else 0),
            (if op == .BGEU then 1 else 0),
            0, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2) ∧
        imm % 2 = 0
      )
    -- JALR
    | .JALR (imm, rs1, rd) =>
      let opcode := 25
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            0, 1,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        imm % 2 = 0
      )
    -- JAL
    | .JAL (imm, rd) =>
      let opcode := 24
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            0, 0, 0, 0,
            a_is_0,
            1, 1,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        imm % 2 = 0
      )
    -- UTYPE : 2 opcodes (LUI encoded as SLL)
    | .UTYPE (imm, rd, op) =>
      let opcode := opcode_of_uop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      let imm_KB := imm_to_KB (imm ++ 0#12) true
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            (if op == .AUIPC then imm_KB[0] else 0),
            (if op == .AUIPC then imm_KB[1] else 0),
            (if op == .AUIPC then imm_KB[2] else 0),
            (if op == .AUIPC then imm_KB[3] else 0),
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            1, 1,
            (if op == .LUI then 1 else 0),
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            (if op == .AUIPC then 1 else 0), 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        imm % 4096 = 0
      )
    -- External call : 1 opcode
    | .ECALL () =>
      let opcode := 28
      let a_is_0 := 0
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            5, 0, 0, 0,
            10, 0, 0, 0,
            11, 0, 0, 0,
            a_is_0,
            0, 0,
            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
        ),
        True
      )
    -- MUL : 4 opcodes
    | .MUL (rs2, rs1, rd, op) =>
      let opcode :=
        match op with
        | { result_part := .Low, signed_rs1 := _, signed_rs2 := _ } => 30                  -- MUL
        | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => 31     -- MULH
        | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => 32 -- MULHU
        | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => 33   -- MULHSU
        | _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
        .some (
          (
            multiplicity,
            #v[
              pc, opcode, opcode,
              reg_to_KB rd, 0, 0, 0,
              reg_to_KB rs1, 0, 0, 0,
              reg_to_KB rs2, 0, 0, 0,
              a_is_0,
              0, 0,
              1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
          ),
          is_register (reg_to_KB rd) ∧
          is_register (reg_to_KB rs1) ∧
          is_register (reg_to_KB rs2)
        )
    -- DIV : 2 opcodes
    | .DIV (rs2, rs1, rd, sgn) =>
      let opcode :=
        match sgn with
        | true => 35
        | false => 34
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- REM : 2 opcodes
    | .REM (rs2, rs1, rd, sgn) =>
      let opcode :=
        match sgn with
        | true => 37
        | false => 36
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            reg_to_KB rs1, 0, 0, 0,
            reg_to_KB rs2, 0, 0, 0,
            a_is_0,
            0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
        ),
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1) ∧
        is_register (reg_to_KB rs2)
      )
    -- Unimplemented
    | _ => .none

end Transpiler
