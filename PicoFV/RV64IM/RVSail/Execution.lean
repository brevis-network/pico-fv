import LeanRV64D
import PicoFV.Fundamentals.Core
import PicoFV.Fundamentals.Word

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

set_option maxHeartbeats 1_000_000_000

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
    := by
      have bounds_toInt_64 : forall (bv : BitVec 64), -2^63 ≤ bv.toInt ∧ bv.toInt < 2^63 := by simp [BitVec.toInt]; intros; split_ifs <;> omega
      have bounds_toNat_64 : forall (bv : BitVec 64), 0 ≤ bv.toNat ∧ bv.toNat < 2^64 := by omega

      rcases op with ⟨ high, sgn1, sgn2 ⟩
      rcases sgn2 with sgn2 | sgn2 <;> rcases sgn1 with sgn1 | sgn1 <;> rcases high with high | high

      all_goals
        simp_all [execute_MUL', execute_MUL, execute_MUL_pure, BitVec.extend, mop_of_mul_op, LeanRV64D.Functions.xlen, to_bits_truncate, Sail.get_slice_int]
        refine bind_congr ?_; intro r1
        refine bind_congr ?_; intro r2
        ext s; simp_all; congr 3
        have mod_129_to_128 : forall (a : ℤ), (a % 680564733841876926926749214863536422912).toNat % 340282366920938463463374607431768211456 = (a % 340282366920938463463374607431768211456).toNat := by omega

      . congr 2
        rw [mod_129_to_128]
        . rw [← BitVec.toNat_mul]
          apply toInt_toInt_as_toNat_128

      . unfold BitVec.toInt
        split_ifs <;> simp_all
        . rw [Int.toNat_emod (by nlinarith) (by simp)]
          simp; congr
        . simp [← BitVec.toNat_inj]
          trans (- ((r1.toNat : ℤ) * ((18446744073709551616 : ℤ) - r2.toNat)) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
          . congr 3
            ring_nf
          . rw [Int.neg_emod_eq_sub_emod]
            have := bounds_toNat_64 r1
            have := bounds_toNat_64 r2
            rw [Int.toNat_emod (by nlinarith) (by simp)]
            rw [Int.toNat_sub'' (by simp) (by nlinarith)]
            simp only [Int.reduceToNat]
            rw [Int.toNat_mul (by omega) (by omega)]
            simp
            rw [Nat.mul_sub_left_distrib ]
            rw [Nat.sub_sub_right _ (by nlinarith)]
            omega
        . simp [← BitVec.toNat_inj]
          trans (- (((18446744073709551616 : ℤ) - r1.toNat) * r2.toNat) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
          . congr 3
            ring_nf
          . rw [Int.neg_emod_eq_sub_emod]
            have := bounds_toNat_64 r1
            have := bounds_toNat_64 r2
            rw [Int.toNat_emod (by nlinarith) (by simp)]
            rw [Int.toNat_sub'' (by simp) (by nlinarith)]
            simp only [Int.reduceToNat]
            rw [Int.toNat_mul (by omega) (by omega)]
            simp
            rw [Nat.mul_sub_right_distrib]
            rw [Nat.sub_sub_right _ (by nlinarith)]
            omega
        . simp [← BitVec.toNat_inj]
          trans (((18446744073709551616 : ℤ) - r1.toNat) * (18446744073709551616 - r2.toNat) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
          . congr 3
            ring_nf
          . have := bounds_toNat_64 r1
            have := bounds_toNat_64 r2
            rw [Int.toNat_emod (by nlinarith) (by simp)]
            simp only [Int.reduceToNat]
            rw [Int.toNat_mul (by omega) (by omega)]
            simp [Nat.mul_sub_right_distrib]
            repeat rw [Nat.mul_sub_left_distrib]
            rw [Nat.sub_sub_right _ (by nlinarith)]
            ring_nf
            suffices : (r1.toNat * 18446744073709551616) % 18446744073709551616 = 0
            . have : forall x y, y * 18446744073709551616 ≤ x → (x - y * 18446744073709551616) % 18446744073709551616 = x % 18446744073709551616 := by intro; omega
              rw [this]
              . omega
              . suffices : r1.toNat * 18446744073709551616 + r2.toNat * 18446744073709551616 ≤ r2.toNat * r1.toNat + 340282366920938463463374607431768211456
                . rw [← Nat.add_sub_assoc (by omega)]
                  rw [Nat.le_sub_iff_add_le (by nlinarith)]
                  assumption
                . nlinarith
            . omega

      . congr 2
        rw [mod_129_to_128]
        apply toNat_toInt_as_toNat_128

      . unfold BitVec.toInt
        split_ifs <;> simp_all
        . rw [Int.toNat_emod (by nlinarith) (by simp)]
          simp; congr
        . simp [← BitVec.toNat_inj]
          trans (- ((r1.toNat : ℤ) * ((18446744073709551616 : ℤ) - r2.toNat)) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
          . congr 3
            ring_nf
          . rw [Int.neg_emod_eq_sub_emod]
            have := bounds_toNat_64 r1
            have := bounds_toNat_64 r2
            rw [Int.toNat_emod (by nlinarith) (by simp)]
            rw [Int.toNat_sub'' (by simp) (by nlinarith)]
            simp only [Int.reduceToNat]
            rw [Int.toNat_mul (by omega) (by omega)]
            simp
            rw [Nat.mul_sub_left_distrib]
            rw [Nat.sub_sub_right _ (by nlinarith)]
            omega

      . congr 2
        rw [mod_129_to_128]
        apply toInt_toNat_as_toNat_128

      . unfold BitVec.toInt
        split_ifs <;> simp_all
        . rw [Int.toNat_emod (by nlinarith) (by simp)]
          simp; congr
        . simp [← BitVec.toNat_inj]
          trans (- (((18446744073709551616 : ℤ) - r1.toNat) * r2.toNat) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
          . congr 3
            ring_nf
          . rw [Int.neg_emod_eq_sub_emod]
            have := bounds_toNat_64 r1
            have := bounds_toNat_64 r2
            rw [Int.toNat_emod (by nlinarith) (by simp)]
            rw [Int.toNat_sub'' (by simp) (by nlinarith)]
            simp only [Int.reduceToNat]
            rw [Int.toNat_mul (by omega) (by omega)]
            simp
            rw [Nat.mul_sub_right_distrib]
            rw [Nat.sub_sub_right _ (by nlinarith)]
            omega

      . rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_mul (by simp) (by simp)]
        simp

      . rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_mul (by simp) (by simp)]
        simp

  lemma combine_MUL_MULH {pl ph op1 op2 : U64w}
  :
    pl.toBV = execute_MUL_pure op1.toBV op2.toBV .MUL →
    ph.toBV = execute_MUL_pure op1.toBV op2.toBV .MULH →
      U128w.toBV #v[pl[0], pl[1], pl[2], pl[3], ph[0], ph[1], ph[2], ph[3]] = (op1.extend true).toBV * (op2.extend true).toBV
  := by
    simp [U64w.extend_BitVec_extend, BitVec.extend]
    simp [execute_MUL_pure, -BitVec.extractLsb]
    intro lo hi
    have : BitVec.extractLsb 63 0 (op1.toBV.extend 128 false * op2.toBV.extend 128 false) = BitVec.extractLsb 63 0 (op1.toBV.extend 128 true * op2.toBV.extend 128 true) := by simp [BitVec.extend, -BitVec.extractLsb]; bv_decide
    rw [this] at lo; clear this
    simp [BitVec.extend, -BitVec.extractLsb] at *
    set x := BitVec.signExtend 128 op1.toBV * BitVec.signExtend 128 op2.toBV
    trans BitVec.extractLsb 63 0 x + (BitVec.setWidth 128 (BitVec.extractLsb 127 64 x) <<< 64)
    . rw [← lo, ← hi]
      simp [← BitVec.toNat_inj]
      simp [U128w.toNat, U64w.toNat]
      simp [Nat.shiftLeft_eq]
      iterate 2 rw [Nat.mod_eq_of_lt (b := 340282366920938463463374607431768211456) (by omega)]
      ring_nf
    . bv_decide

  lemma combine_MUL_MULHU {pl ph op1 op2 : U64w}
  :
    pl.toBV = execute_MUL_pure op1.toBV op2.toBV .MUL →
    ph.toBV = execute_MUL_pure op1.toBV op2.toBV .MULHU →
      U128w.toBV #v[pl[0], pl[1], pl[2], pl[3], ph[0], ph[1], ph[2], ph[3]] = (op1.extend false).toBV * (op2.extend false).toBV
  := by
    simp [U64w.extend_BitVec_extend, BitVec.extend]
    simp [execute_MUL_pure, -BitVec.extractLsb]
    intro lo hi
    simp [BitVec.extend, -BitVec.extractLsb] at *
    set x := BitVec.setWidth 128 op1.toBV * BitVec.setWidth 128 op2.toBV
    trans BitVec.extractLsb 63 0 x + (BitVec.setWidth 128 (BitVec.extractLsb 127 64 x) <<< 64)
    . rw [← lo, ← hi]
      simp [← BitVec.toNat_inj]
      simp [U128w.toNat, U64w.toNat]
      simp [Nat.shiftLeft_eq]
      iterate 2 rw [Nat.mod_eq_of_lt (b := 340282366920938463463374607431768211456) (by omega)]
      ring_nf
    . bv_decide

  end MUL

  section MULW

    /-- Pure part of `execute_MULW` (RV64-only) -/
    def execute_MULW_pure (op1 : BitVec 32) (op2 : BitVec 32) : BitVec 64 :=
      (op1 * op2).signExtend 64

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
    := by
      simp [execute_MULW, execute_MULW']
      refine bind_congr ?_; intro r1
      refine bind_congr ?_; intro r2
      simp [execute_MULW_pure]
      suffices :
        BitVec.signExtend 64 (to_bits_truncate ((r1.toNat : ℤ).bmod 4294967296 * (r2.toNat : ℤ).bmod 4294967296)) =
        BitVec.signExtend 64 (BitVec.setWidth 32 r1 * BitVec.setWidth 32 r2)
      . congr 1
      . simp [← BitVec.toInt_inj, to_bits_truncate, Sail.get_slice_int]
        simp [BitVec.toInt_signExtend_of_le]
        simp [Int.bmod_def]
        have eq_prod :
          (r1.toNat : ℤ) * (r2.toNat : ℤ) % 4294967296 =
            (((r1.toNat : ℤ) % 4294967296) * ((r2.toNat : ℤ) % 4294967296)) % 4294967296
          := by apply Int.mul_emod
        simp [eq_prod]
        obtain ⟨ x, y, eq_x, eq_y ⟩ :
          ∃ x y, (r1.toNat : ℤ) % 4294967296 = x ∧ (r2.toNat : ℤ) % 4294967296 = y
          := by simp
        simp [eq_x, eq_y]
        by_cases hxz : x = 0
        . simp_all
        . by_cases hyz : y = 0
          . simp_all
          . obtain ⟨ lb_x, ub_x, lb_y, ub_y ⟩ :
              0 < x ∧ x < 4294967296 ∧ 0 < y ∧ y < 4294967296
              := by grind
            clear eq_x eq_y eq_prod r1 r2 rs2 rs1 rd
            simp [BitVec.ofNat]; rw [max_eq_left (by omega)]; simp [Int.bmod_def]
            split_ifs <;> ring_nf at * <;> omega

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
      execute_DIV rs2 rs1 rd usgn = execute_DIV' rs2 rs1 rd usgn
    := by
      simp_all [execute_DIV, execute_DIV']
      refine bind_congr ?_; intro r1
      refine bind_congr ?_; intro r2
      ext s; simp; congr
      have range_int_r1 : -9223372036854775808 ≤ r1.toInt ∧ r1.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
      have range_int_r2 : -9223372036854775808 ≤ r2.toInt ∧ r2.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
      have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 18446744073709551616 := by omega
      have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 18446744073709551616 := by omega
      by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int, LeanRV64D.Functions.not, LeanRV64D.Functions.xlen] <;>
      by_cases r2z : r2 = 0 <;> simp_all
      . simp [to_bits_truncate, Sail.get_slice_int]
      . repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
        rw [← BitVec.toNat_inj]
        simp [to_bits_truncate, Sail.get_slice_int]
        congr; rw [Int.emod_eq_of_lt]
        . apply Int.zero_le_ofNat
        . have := @Int.ediv_le_self r1.toNat r2.toNat (by omega)
          omega
      . simp [to_bits_truncate, Sail.get_slice_int]
        aesop
      . rw [if_neg (c := r2.toInt = 0) (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
        by_cases of : 9223372036854775808 ≤ r1.toInt.tdiv r2.toInt <;>
        have of' := div_overflow_64 range_int_r1 range_int_r2 <;>
        simp_all [to_bits_truncate, Sail.get_slice_int]
        . rw [if_pos (by omega)]
          decide
        . rw [if_neg (by omega)]
          rw [if_neg (c := r2.toInt = 0) (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
          simp [BitVec.ofNat, BitVec.ofInt]
          congr; simp [Fin.ext_iff]
          omega

    @[simp]
    lemma execute_REM_eq_execute_REM' :
      execute_REM rs2 rs1 rd usgn = execute_REM' rs2 rs1 rd usgn
    := by
      simp_all [execute_REM, execute_REM']
      refine bind_congr ?_; intro r1
      refine bind_congr ?_; intro r2
      ext s; simp_all; congr
      have range_int_r1 : -9223372036854775808 ≤ r1.toInt ∧ r1.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
      have range_int_r2 : -9223372036854775808 ≤ r2.toInt ∧ r2.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
      have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 18446744073709551616 := by omega
      have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 18446744073709551616 := by omega
      by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int] <;>
      by_cases r2z : r2 = 0 <;> simp_all
      . simp [to_bits_truncate, Sail.get_slice_int]
        rw [Nat.mod_eq_of_lt (by omega)]; simp
      . repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
        rw [← BitVec.toNat_inj]
        simp [to_bits_truncate, Sail.get_slice_int]
        congr; rw [Int.emod_eq_of_lt]
        . apply Int.zero_le_ofNat
        . rw [Int.tmod_eq_emod_of_nonneg (by omega)]
          trans (r2.toNat : ℤ)
          . simp [← BitVec.toNat_inj] at r2z
            apply Int.emod_lt_of_pos r1.toNat (by omega)
          . omega
      . simp [to_bits_truncate, Sail.get_slice_int]
        simp [← BitVec.toNat_inj]
        have mod_65_to_64 : forall (a : ℤ), (a % 36893488147419103232).toNat % 18446744073709551616 = (a % 18446744073709551616).toNat := by omega
        simp [mod_65_to_64, BitVec.toInt]
        split_ifs with hneg <;> [ skip; simp ] <;> rw [Int.emod_eq_of_lt (by omega)] <;> simp <;> omega
      . repeat rw [ if_neg (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
        simp_all [to_bits_truncate, Sail.get_slice_int]
        simp [BitVec.ofNat, BitVec.ofInt]
        congr; simp [Fin.ext_iff]
        omega

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

    attribute [-simp]
      EuclideanDomain.mod_eq_zero

    @[simp]
    lemma execute_DIVW_eq_execute_DIVW' :
      execute_DIVW rs2 rs1 rd usgn = execute_DIVW' rs2 rs1 rd usgn
    := by
      simp_all [execute_DIVW, execute_DIVW']
      refine bind_congr ?_; intro r1
      refine bind_congr ?_; intro r2
      ext s; simp; congr
      by_cases h_usgn : usgn <;> simp_all [execute_DIVW_REMW_pure, execute_DIVW_REMW_pure_int, LeanRV64D.Functions.not]
      . obtain ⟨ r1', eq_r1' ⟩ : ∃ r1', (r1.toNat : ℤ) % 4294967296 = r1' := by simp
        obtain ⟨ r2', eq_r2' ⟩ : ∃ r2', (r2.toNat : ℤ) % 4294967296 = r2' := by simp
        have lb_r1' : 0 ≤ r1' := by omega
        have ub_r1' : r1' < 4294967296 := by omega
        have ub_r2' : r2' < 4294967296 := by omega
        simp_all
        clear eq_r1' r1
        split_ifs
        . decide
        . have lb_r2' : 0 < r2' := by omega
          rw [Int.tdiv_eq_ediv, if_pos (by omega)]
          simp [to_bits_truncate, Sail.get_slice_int]
          congr; rw [Int.emod_eq_of_lt]
          . rw [Int.le_ediv_iff_mul_le (by omega)]
            simp [lb_r1']
          . have := @Int.ediv_le_self r1' r2' lb_r1'
            omega
      . obtain ⟨ r1', eq_r1' ⟩ : ∃ r1', (r1.toNat : ℤ).bmod 4294967296 = r1' := by simp
        obtain ⟨ r2', eq_r2' ⟩ : ∃ r2', (r2.toNat : ℤ).bmod 4294967296 = r2' := by simp
        have range_int_r1' : -2147483648 ≤ r1' ∧ r1' < 2147483648 := by grind
        have range_int_r2' : -2147483648 ≤ r2' ∧ r2' < 2147483648 := by grind
        simp_all [to_bits_truncate, Sail.get_slice_int]
        clear eq_r1' r1 eq_r2' r2
        by_cases z_r2' : r2' = 0 <;> simp [z_r2']
        . decide
        . by_cases of : 2147483648 ≤ r1'.tdiv r2' <;>
          have of' := div_overflow_32 range_int_r1' range_int_r2' <;>
          simp_all
          . rw [if_pos (by omega)]
            decide
          . rw [if_neg (by omega)]
            simp [BitVec.ofNat, BitVec.ofInt]
            congr; simp [Fin.ext_iff]
            omega

    @[simp]
    lemma execute_REMW_eq_execute_REMW' :
      execute_REMW rs2 rs1 rd usgn = execute_REMW' rs2 rs1 rd usgn
    := by
      simp_all [execute_REMW, execute_REMW']
      refine bind_congr ?_; intro r1
      refine bind_congr ?_; intro r2
      ext s; simp; congr
      by_cases h_usgn : usgn <;> simp_all [execute_DIVW_REMW_pure, execute_DIVW_REMW_pure_int]
      . obtain ⟨ r1', eq_r1' ⟩ : ∃ r1', (r1.toNat : ℤ) % 4294967296 = r1' := by simp
        obtain ⟨ r2', eq_r2' ⟩ : ∃ r2', (r2.toNat : ℤ) % 4294967296 = r2' := by simp
        have lb_r1' : 0 ≤ r1' := by omega
        have ub_r1' : r1' < 4294967296 := by omega
        have ub_r2' : r2' < 4294967296 := by omega
        simp_all
        clear eq_r1' r1
        split_ifs with h_r2'
        . simp_all [to_bits_truncate, Sail.get_slice_int]
          grind
        . replace h_r2' : 0 < r2' := by omega
          rw [Int.tmod_eq_emod, if_pos (by omega)]
          simp [to_bits_truncate, Sail.get_slice_int]
          congr 2; rw [Int.emod_eq_of_lt (b := 8589934592)]
          . apply Int.emod_nonneg
            omega
          . have := @Int.emod_lt_of_pos r1' r2' h_r2'
            omega
      . obtain ⟨ r1', eq_r1' ⟩ : ∃ r1', (r1.toNat : ℤ).bmod 4294967296 = r1' := by simp
        obtain ⟨ r2', eq_r2' ⟩ : ∃ r2', (r2.toNat : ℤ).bmod 4294967296 = r2' := by simp
        have range_int_r1' : -2147483648 ≤ r1' ∧ r1' < 2147483648 := by grind
        have range_int_r2' : -2147483648 ≤ r2' ∧ r2' < 2147483648 := by grind
        simp_all [to_bits_truncate, Sail.get_slice_int]
        clear eq_r1' r1 eq_r2' r2
        by_cases z_r2' : r2' = 0 <;> simp [z_r2']
        . congr
          simp [← BitVec.toInt_inj]
          have mod_33_to_32 : forall (a : ℤ), (a % 8589934592).toNat % 4294967296 = (a % 4294967296).toNat := by omega
          simp [BitVec.toInt, mod_33_to_32]
          rw [max_eq_left (by omega)]
          rw [Int.bmod_eq_of_le (by omega) (by omega)]
          omega
        . simp [BitVec.ofNat, BitVec.ofInt]
          congr; simp [Fin.ext_iff]
          omega

  end DIVW_REMW

end RV64IM
