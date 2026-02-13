import LeanRV64D
import PicoFV.Fundamentals.Core

open PreSail
open LeanRV64D.Functions

attribute [simp]
  bool_to_bit
  mult_to_bits_half
  shift_bits_right_arith
  shift_right_arith
  sign_extend
  zero_extend
  zopz0zI_s
  zopz0zI_u
  Sail.BitVec.extractLsb
  Sail.BitVec.signExtend
  Sail.BitVec.zeroExtend
  Sail.BitVec.toNatInt
  Sail.shift_bits_left
  Sail.shift_bits_right

attribute [local simp]
  BitVec.extractLsb
  BitVec.extractLsb'

namespace RV64IM

  section RTYPE

    /-- Pure part of 64-bit `execute_RTYPE` -/
    def execute_RTYPE_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : rop) :=
      match op with
      | .ADD => op1 + op2
      | .SLT => zero_extend (m := 64) (bool_to_bit (zopz0zI_s op1 op2))
      | .SLTU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u op1 op2))
      | .AND => op1 &&& op2
      | .OR => op1 ||| op2
      | .XOR => op1 ^^^ op2
      | .SLL => Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 5 0)
      | .SRL => Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 5 0)
      | .SUB => op1 - op2
      | .SRA => BitVec.sshiftRight op1 (Sail.BitVec.extractLsb op2 5 0).toNat

    /-- `execute_RTYPE` with isolated pure part -/
    def execute_RTYPE' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      (wX_bits rd (execute_RTYPE_pure rs1_bits rs2_bits op))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_RTYPE`s -/
    @[simp]
    lemma execute_RTYPE_eq_execute_RTYPE' :
      execute_RTYPE rs2 rs1 rd op = execute_RTYPE' rs2 rs1 rd op
      := by
        cases op <;> simp_all [execute_RTYPE', execute_RTYPE, execute_RTYPE_pure]
        . congr
        . congr
        . refine bind_congr ?_; intro r1
          refine bind_congr ?_; intro r2
          ext s; simp_all; congr 3
          simp [LeanRV64D.Functions.log2_xlen]
          have : (63 + ((BitVec.ofNat 6 r2.toNat).toNat) : ℤ).toNat - (BitVec.ofNat 6 r2.toNat).toNat + 1 = 64 := by omega
          rw [this]; clear this; simp
          rw [BitVec.sshiftright_eq]
          simp; congr

  end RTYPE

  section ITYPE

    @[simp]
    def rop_of_iop (op : iop) : rop :=
      match op with
      | .ADDI => .ADD
      | .SLTI => .SLT
      | .SLTIU => .SLTU
      | .XORI => .XOR
      | .ORI => .OR
      | .ANDI => .AND

    /-- Pure part of 64-bit `execute_ITYPE` -/
    def execute_ITYPE_pure (imm : BitVec 12) (op1 : BitVec 64) (op : iop) :=
      let immext := sign_extend (m := 64) imm
      execute_RTYPE_pure op1 immext (rop_of_iop op)

    /-- `execute_ITYPE` with isolated pure part -/
    def execute_ITYPE' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      (wX_bits rd (execute_ITYPE_pure imm rs1_bits op))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_ITYPE`s -/
    @[simp]
    lemma execute_ITYPE_eq_execute_ITYPE' :
      execute_ITYPE imm rs1 rd op = execute_ITYPE' imm rs1 rd op
      := by cases op <;> simp_all [execute_ITYPE', execute_ITYPE, execute_ITYPE_pure, execute_RTYPE_pure]

  end ITYPE

  section SHIFTIOP

    @[simp]
    def rop_of_sop (op : sop) : rop :=
      match op with
      | .SLLI => .SLL
      | .SRLI => .SRL
      | .SRAI => .SRA

    /-- Pure part of a 64-bit `execute_SHIFTIOP` -/
    def execute_SHIFTIOP_pure (op1 : BitVec 64) (shamt : BitVec 6) (op : sop) :=
      let shamt64 : BitVec 64 := shamt
      execute_RTYPE_pure op1 shamt64 (rop_of_sop op)

    /-- `execute_SHIFTIOP` with isolated pure part -/
    def execute_SHIFTIOP' (shamt : BitVec 6) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      (wX_bits rd (execute_SHIFTIOP_pure rs1_bits shamt op))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_SHIFTIOP`s -/
    @[simp]
    lemma execute_SHIFTIOP_eq_execute_SHIFTIOP' :
      execute_SHIFTIOP shamt rs1 rd op = execute_SHIFTIOP' shamt rs1 rd op
      := by
        have h_eq_shamt : BitVec.ofNat 6 (shamt.toNat % 18446744073709551616) = shamt := by
          rw [Nat.mod_eq_of_lt (by omega)]; simp
        simp [execute_SHIFTIOP, execute_SHIFTIOP', execute_SHIFTIOP_pure, execute_RTYPE_pure]
        cases op <;> simp
        . aesop
        . aesop
        . refine bind_congr ?_; intro r1
          ext s; simp_all; congr 3
          simp [LeanRV64D.Functions.log2_xlen]
          have : (63 + ((BitVec.ofNat 6 shamt.toNat).toNat) : ℤ).toNat - (BitVec.ofNat 6 shamt.toNat).toNat + 1 = 64 := by omega
          rw [this]; clear this; simp
          rw [BitVec.sshiftright_eq]
          simp; congr

  end SHIFTIOP

  section RTYPEW

    /-- Pure part of 32-bit-word `execute_RTYPEW` (RV64-only) -/
    def execute_RTYPEW_pure (op1 : BitVec 32) (op2 : BitVec 32) (op : ropw) : BitVec 64 :=
      let result : BitVec 32 :=
        match op with
        | .ADDW => op1 + op2
        | .SUBW => op1 - op2
        | .SLLW => Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 4 0)
        | .SRLW => Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 4 0)
        | .SRAW => BitVec.sshiftRight op1 (Sail.BitVec.extractLsb op2 4 0).toNat
      sign_extend (m := 64) result

    /-- `execute_RTYPEW` with isolated pure part -/
    def execute_RTYPEW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      let rs1_val := Sail.BitVec.extractLsb rs1_bits 31 0
      let rs2_val := Sail.BitVec.extractLsb rs2_bits 31 0
      (wX_bits rd (execute_RTYPEW_pure rs1_val rs2_val op))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_RTYPEW`s -/
    @[simp]
    lemma execute_RTYPEW_eq_execute_RTYPEW' :
      execute_RTYPEW rs2 rs1 rd op = execute_RTYPEW' rs2 rs1 rd op
      := by
        cases op
        case ADDW | SUBW | SLLW | SRLW =>
          simp_all [execute_RTYPEW', execute_RTYPEW, execute_RTYPEW_pure]
        case SRAW =>
          simp [execute_RTYPEW', execute_RTYPEW, execute_RTYPEW_pure]
          refine bind_congr ?_; intro r1
          refine bind_congr ?_; intro r2
          ext s; simp; congr 3
          have h_shamt : (BitVec.ofNat 5 (BitVec.setWidth 32 r2).toNat).toNat = r2.toNat % 32 := by
            simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]
          have h_w1 : (31 + ((BitVec.ofNat 5 (BitVec.setWidth 32 r2).toNat).toNat : ℤ)).toNat -
            (BitVec.ofNat 5 (BitVec.setWidth 32 r2).toNat).toNat + 1 = 32 := by omega
          have h_w2 : (32 + ((BitVec.ofNat 5 (BitVec.setWidth 32 r2).toNat).toNat : ℤ)).toNat =
            32 + (BitVec.ofNat 5 (BitVec.setWidth 32 r2).toNat).toNat := by omega
          have h_shift : ((r2.toNat : ℤ) % 32).toNat = r2.toNat % 32 := by omega
          rw [h_w1, h_w2, h_shamt, h_shift]; congr 1
          rw [BitVec.sshiftright_eq]; simp

  end RTYPEW

  section ADDIW

    /-- Pure part of `execute_ADDIW` (RV64-only) -/
    def execute_ADDIW_pure (imm : BitVec 12) (op1 : BitVec 64) : BitVec 64 :=
      let result := op1 + sign_extend (m := 64) imm
      sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)

    /-- `execute_ADDIW` with isolated pure part -/
    def execute_ADDIW' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      (wX_bits rd (execute_ADDIW_pure imm rs1_bits))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_ADDIW`s -/
    @[simp]
    lemma execute_ADDIW_eq_execute_ADDIW' :
      execute_ADDIW imm rs1 rd = execute_ADDIW' imm rs1 rd
      := by
        simp [execute_ADDIW', execute_ADDIW, execute_ADDIW_pure]
        refine bind_congr ?_; intro r1
        simp [BitVec.setWidth]

  end ADDIW

  section SHIFTIWOP

    /-- Conversion from `sopw` to `rop` -/
    @[simp]
    def rop_of_sopw (op : sopw) : rop :=
      match op with
      | .SLLIW => .SLL
      | .SRLIW => .SRL
      | .SRAIW => .SRA

    /-- Pure part of `execute_SHIFTIWOP` (RV64-only) -/
    def execute_SHIFTIWOP_pure (op1 : BitVec 32) (shamt : BitVec 5) (op : sopw) : BitVec 64 :=
      let result : BitVec 32 :=
        match op with
        | .SLLIW => Sail.shift_bits_left op1 shamt
        | .SRLIW => Sail.shift_bits_right op1 shamt
        | .SRAIW => BitVec.sshiftRight op1 shamt.toNat
      sign_extend (m := 64) result

    /-- `execute_SHIFTIWOP` with isolated pure part -/
    def execute_SHIFTIWOP' (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs1_val := Sail.BitVec.extractLsb rs1_bits 31 0
      (wX_bits rd (execute_SHIFTIWOP_pure rs1_val shamt op))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_SHIFTIWOP`s -/
    @[simp]
    lemma execute_SHIFTIWOP_eq_execute_SHIFTIWOP' :
      execute_SHIFTIWOP shamt rs1 rd op = execute_SHIFTIWOP' shamt rs1 rd op
      := by
        simp [execute_SHIFTIWOP, execute_SHIFTIWOP', execute_SHIFTIWOP_pure]
        cases op <;> simp
        -- SRAIW: shift_bits_right_arith vs sshiftRight
        . refine bind_congr ?_; intro r1
          ext s; simp; congr 3
          have : (31 + (shamt.toNat : ℤ)).toNat - shamt.toNat + 1 = 32 := by omega
          rw [this]; clear this; simp
          rw [BitVec.sshiftright_eq]
          simp; congr

  end SHIFTIWOP

  section MUL

    /-- Multiplication opcodes -/
    inductive mop where | MUL | MULH | MULHU | MULHUS | MULHSU
      deriving BEq, DecidableEq, Inhabited, Repr

    /-- Conversion from RISC-V spec representation to `mop` -/
    def mop_of_mul_op (m : mul_op) : mop :=
      match m with
      | { result_part := .Low, signed_rs1 := _, signed_rs2 := _ } => .MUL
      | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => .MULHU
      | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Signed } => .MULHUS
      | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => .MULHSU
      | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => .MULH

    /-- Pure part of 64-bit `execute_MUL` -/
    def execute_MUL_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : mop) : BitVec 64 :=
      let rs1_ext : BitVec 128 := op1.extend 128 (op = .MULH ∨ op = .MULHSU)
      let rs2_ext : BitVec 128 := op2.extend 128 (op = .MULH ∨ op = .MULHUS)
      let result_wide := rs1_ext * rs2_ext
      (if (op = .MUL)
        then (Sail.BitVec.extractLsb result_wide 63 0)
        else (Sail.BitVec.extractLsb result_wide 127 64))

    def execute_MUL' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (m : mop) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      (wX_bits rd (execute_MUL_pure rs1_bits rs2_bits m))
      (pure RETIRE_SUCCESS)

    @[simp]
    lemma execute_MUL_eq_execute_MUL' :
      execute_MUL rs2 rs1 rd op = execute_MUL' rs2 rs1 rd (mop_of_mul_op op)
        := by sorry

  end MUL

  section MULW

    /-- Pure part of `execute_MULW` (RV64-only) -/
    def execute_MULW_pure (op1 : BitVec 32) (op2 : BitVec 32) : BitVec 64 :=
      let rs1_int := BitVec.toInt op1
      let rs2_int := BitVec.toInt op2
      let result32 : BitVec 32 := to_bits_truncate (l := 32) (rs1_int * rs2_int)
      sign_extend (m := 64) result32

    /-- `execute_MULW` with isolated pure part -/
    def execute_MULW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      let rs1_val := Sail.BitVec.extractLsb rs1_bits 31 0
      let rs2_val := Sail.BitVec.extractLsb rs2_bits 31 0
      (wX_bits rd (execute_MULW_pure rs1_val rs2_val))
      (pure RETIRE_SUCCESS)

    /-- Equivalence of `execute_MULW`s -/
    @[simp]
    lemma execute_MULW_eq_execute_MULW' :
      execute_MULW rs2 rs1 rd = execute_MULW' rs2 rs1 rd
        := by sorry

  end MULW

  section DIV_REM

    /-- Div/Rem opcodes -/
    inductive drop where | DRS | DRU
      deriving BEq, DecidableEq, Inhabited, Repr

    def execute_DIV_REM_pure_int (op1 : BitVec 64) (op2 : BitVec 64) (op : drop) : ℤ × ℤ :=
      match op with
      | .DRS =>
          let nop1 := BitVec.toInt op1
          let nop2 := BitVec.toInt op2
          let q := if nop2 = 0 then -1 else
                    if nop1 = -2^63 && nop2 = -1 then -2^63 else
                      Int.tdiv nop1 nop2
          let r := Int.tmod nop1 nop2
          ⟨ q, r ⟩
      | .DRU =>
          let nop1 : ℤ := BitVec.toNat op1
          let nop2 : ℤ := BitVec.toNat op2
          let q := if nop2 = 0 then 2^64 - 1 else Int.tdiv nop1 nop2
          let r := Int.tmod nop1 nop2
          ⟨ q, r ⟩

    def execute_DIV_REM_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : drop) : BitVec 64 × BitVec 64 :=
      let ⟨ q, r ⟩ := execute_DIV_REM_pure_int op1 op2 op
      match op with
      | .DRS => ⟨ BitVec.ofInt 64 q, BitVec.ofInt 64 r ⟩
      | .DRU => ⟨ BitVec.ofNat 64 q, BitVec.ofNat 64 r ⟩

    def execute_DIV' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      let ⟨ result, _ ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
      (wX_bits rd result)
      (pure RETIRE_SUCCESS)

    def execute_REM' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      let ⟨ _, result ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
      (wX_bits rd result)
      (pure RETIRE_SUCCESS)

    @[simp]
    lemma execute_DIV_eq_execute_DIV' :
      execute_DIV rs2 rs1 rd usgn = execute_DIV' rs2 rs1 rd usgn := by sorry

    @[simp]
    lemma execute_REM_eq_execute_REM' :
      execute_REM rs2 rs1 rd usgn = execute_REM' rs2 rs1 rd usgn := by sorry

  end DIV_REM

  section DIVW_REMW

    def execute_DIVW_REMW_pure_int (op1 : BitVec 32) (op2 : BitVec 32) (op : drop) : ℤ × ℤ :=
      match op with
      | .DRS =>
          let nop1 := BitVec.toInt op1
          let nop2 := BitVec.toInt op2
          let q := if nop2 = 0 then -1 else
                    if nop1 = -2^31 && nop2 = -1 then -2^31 else
                      Int.tdiv nop1 nop2
          let r := Int.tmod nop1 nop2
          ⟨ q, r ⟩
      | .DRU =>
          let nop1 : ℤ := BitVec.toNat op1
          let nop2 : ℤ := BitVec.toNat op2
          let q := if nop2 = 0 then 2^32 - 1 else Int.tdiv nop1 nop2
          let r := Int.tmod nop1 nop2
          ⟨ q, r ⟩

    def execute_DIVW_REMW_pure (op1 : BitVec 32) (op2 : BitVec 32) (op : drop) : BitVec 64 × BitVec 64 :=
      let ⟨ q, r ⟩ := execute_DIVW_REMW_pure_int op1 op2 op
      match op with
      | .DRS => ⟨ sign_extend (m := 64) (BitVec.ofInt 32 q), sign_extend (m := 64) (BitVec.ofInt 32 r) ⟩
      | .DRU => ⟨ sign_extend (m := 64) (BitVec.ofNat 32 q), sign_extend (m := 64) (BitVec.ofNat 32 r) ⟩

    def execute_DIVW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      let rs1_val := Sail.BitVec.extractLsb rs1_bits 31 0
      let rs2_val := Sail.BitVec.extractLsb rs2_bits 31 0
      let ⟨ result, _ ⟩ := execute_DIVW_REMW_pure rs1_val rs2_val (if is_unsigned then .DRU else .DRS)
      (wX_bits rd result)
      (pure RETIRE_SUCCESS)

    def execute_REMW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
      let rs1_bits ← do (rX_bits rs1)
      let rs2_bits ← do (rX_bits rs2)
      let rs1_val := Sail.BitVec.extractLsb rs1_bits 31 0
      let rs2_val := Sail.BitVec.extractLsb rs2_bits 31 0
      let ⟨ _, result ⟩ := execute_DIVW_REMW_pure rs1_val rs2_val (if is_unsigned then .DRU else .DRS)
      (wX_bits rd result)
      (pure RETIRE_SUCCESS)

    @[simp]
    lemma execute_DIVW_eq_execute_DIVW' :
      execute_DIVW rs2 rs1 rd usgn = execute_DIVW' rs2 rs1 rd usgn := by sorry

    @[simp]
    lemma execute_REMW_eq_execute_REMW' :
      execute_REMW rs2 rs1 rd usgn = execute_REMW' rs2 rs1 rd usgn := by sorry

  end DIVW_REMW

end RV64IM