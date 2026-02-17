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
    | .LUI => 5
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
        let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
    | .BTYPE (imm, rs1, rd, op) =>
      let opcode := opcode_of_bop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
        is_register (reg_to_KB rd) ∧
        is_register (reg_to_KB rs1)
      )
    -- JALR
    | .JALR (imm, rd, rs1) =>
      let opcode := 25
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
        is_register (reg_to_KB rs1)
      )
    -- JAL
    | .JAL (imm, rd) =>
      let opcode := 24
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
        is_register (reg_to_KB rd)
      )
    -- UTYPE : 2 opcodes (LUI encoded as SLL)
    | .UTYPE (imm, rd, op) =>
      let opcode := opcode_of_uop op
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
      let imm_KB := imm_to_KB imm true
      .some (
        (
          multiplicity,
          #v[
            pc, opcode, opcode,
            reg_to_KB rd, 0, 0, 0,
            0, 0, 0, 0,
            imm_KB[0], imm_KB[1], imm_KB[2], imm_KB[3],
            a_is_0,
            1, 1,
            (if op == .LUI then 1 else 0),
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            (if op == .AUIPC then 1 else 0), 0
          ]
        ),
        is_register (reg_to_KB rd)
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
        let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 0 else 1
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
    | _ => .none

end Transpiler
