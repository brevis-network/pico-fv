import PicoFV.RV64IM.Transpiler.Transpiler

/-! # Instruction decoder for the Pico v3.1.1 Program table

    The Pico v3.1.1 `CpuChip` fetches its instruction with one 26-field message on the
    Program bus (tag 2). This file maps a Sail `instruction` at address `pc` to that message,
    following Pico's decoder `vm/src/compiler/riscv/disassembler/rrs.rs` and the table builder
    `vm/src/chips/chips/riscv_program/traces.rs` at the commit pinned in `extractor/Cargo.toml`
    (`2acc7c1828fb`).

    Layout, as sent by `riscv_cpu/constraints.rs:452-481` (`looking_program`) and received by
    `riscv_program/constraints.rs:53-83` (`looked_program`):

    ```
    [ pc[0], pc[1],                                   -- Pc (2)
      opcode,                                         -- emitted once on its own
      opcode, op_a, op_b (limb0, limb1, sign),        -- InstructionCols (9)
             op_c (limb0, limb1, sign), op_a_0,
      imm_b, imm_c, is_ecall, is_memory, is_store,    -- OpcodeSelectorCols (13)
      is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
      is_jalr, is_jal,
      pc_carry ]                                      -- [pc[0] >= 0xFFFC]
    ```

    Differences from the 2.x decoder in `Transpiler.lean`, which stays unchanged because the
    2.x bus contracts (still used by the memory chip) refer to it:

    * the pc is a natural number with two 16-bit pieces, not three field limbs;
    * register `a` is one field (`instruction/columns.rs:19`);
    * `b` and `c` are two 16-bit pieces plus one sign bit (`SignExtImm`,
      `instruction/columns.rs:43-48`);
    * 13 selectors; there is no `is_alu`, `is_auipc`, `is_unimpl` and no per-width memory flag;
    * `op_a_0` is `[op_a = x0]` for every instruction, stores and branches included
      (`instruction/columns.rs:92`);
    * `AUIPC rd, imm` is `ADD rd, imm, pc` with both immediate flags (`rrs.rs:357-366`);
    * `ECALL` has a row: `op_a = x5`, `b = x10`, `c = x11`, `is_ecall = 1` (`rrs.rs:368-377`);
    * trap instructions (`EBREAK` and `UNIMP`; Pico decodes CSR, `MRET` and `WFI` as `UNIMP`,
      `rrs.rs:485-507, 519-525`) have no row: the Program table gives them no pc of their own
      (`riscv_program/traces.rs:111-120`), so the decoder returns `none` for them, as for
      every constructor it does not list;
    * no evenness side condition on the `JALR` offset: RISC-V allows an odd one, and the chip
      clears the low bit itself (`riscv_cpu/jump/constraints.rs:79-126`).

    `FENCE` has no case of its own. Pico decodes every `FENCE` word (`fence.tso` and `pause`
    included) as the no-op `ADD x0, x0, 0` with `imm_c` set (`rrs.rs:95-100, 509-517`), which
    is exactly the row this decoder gives `ADDI x0, x0, 0`. The Program promise in
    `BusesV3.lean` therefore holds for a `FENCE` row as written, and an instruction theorem,
    which rebuilds the instruction from the row's columns, reads that row as
    `ADDI x0, x0, 0`. That the no-op row does what Sail's `FENCE` and `FENCE_TSO` do is not
    proved here.

    The lemmas below relate the decoder's pc pieces and operands to natural numbers and
    64-bit values; the lemmas that go from a Program-bus message back to its instruction are
    in `BusesV3.lean`.                                                                     -/

namespace Transpiler.V3

  open RV64IM
  open Transpiler

  /-! ## Program counter -/

  /-- Low 16-bit piece of a pc (`Pc<T>` limb 0, `compiler/addr.rs`). -/
  def pc_lo (pc : ℕ) : FKB := ⟨pc % 65536, by omega⟩

  /-- High 16-bit piece of a pc (`Pc<T>` limb 1). Pico's pc has no third piece. -/
  def pc_hi (pc : ℕ) : FKB := ⟨pc / 65536 % 65536, by omega⟩

  /-- The Program table's `pc_carry` column: the carry out of limb 0 in `pc + 4`, i.e.
      `[pc[0] >= 0xFFFC]` (`riscv_program/traces.rs:126`). -/
  def pc_carry (pc : ℕ) : FKB := if 0xFFFC ≤ pc % 65536 then 1 else 0

  /-- Guest addresses stay below this bound; the Program table asserts it for every row it
      builds (`riscv_program/traces.rs:107-110`). -/
  def code_address_bound : ℕ := 0x7800_0000

  @[simp] lemma val_pc_lo (pc : ℕ) : (pc_lo pc).val = pc % 65536 := rfl

  @[simp] lemma val_pc_hi (pc : ℕ) : (pc_hi pc).val = pc / 65536 % 65536 := rfl

  /-- A guest address is its two 16-bit pieces, and its high piece is at most `0x77FF`. -/
  lemma pc_pieces {pc : ℕ} (h_lt : pc < code_address_bound) :
      (pc_lo pc).val < 65536 ∧ (pc_hi pc).val ≤ 0x77FF ∧
      (pc_lo pc).val + 65536 * (pc_hi pc).val = pc := by
    simp only [val_pc_lo, val_pc_hi, code_address_bound] at *
    omega

  /-- The low piece of a 4-aligned pc is 4-aligned. -/
  lemma pc_lo_mod_four {pc : ℕ} (h_al : pc % 4 = 0) : (pc_lo pc).val % 4 = 0 := by
    simp only [val_pc_lo]; omega

  /-- `pc_carry` is 1 exactly when the low piece is at least `0xFFFC`. -/
  lemma pc_carry_eq (pc : ℕ) :
      pc_carry pc = if 0xFFFC ≤ (pc_lo pc).val then 1 else 0 := rfl

  /-! ## Operands

      An operand in the Program message is `SignExtImm`: bits 0..16, bits 16..32 and one sign
      bit standing for bits 32..64 (all zero or all one). Register indices, shift amounts and
      the pc have sign 0.                                                                  -/

  /-- `SignExtImm` of an immediate, extended to 64 bits with sign `sgn`
      (`SignExtImm::from_u64`, `instruction/columns.rs:57-70`). For the immediates the
      decoder meets (at most 32 bits wide) bits 32..64 are a sign fill, so the sign bit is
      the extended value's bit 63. -/
  def imm_operand {w : ℕ} (imm : BitVec w) (sgn : Bool) : Vector FKB 3 :=
    let limbs := imm_to_KB imm sgn
    #v[limbs[0], limbs[1], if (BitVec.extend imm 64 sgn).msb then 1 else 0]

  /-- The two low pieces of an operand are those of `imm_to_KB`. -/
  lemma imm_operand_low {w : ℕ} (imm : BitVec w) (sgn : Bool) :
      (imm_operand imm sgn)[0] = (imm_to_KB imm sgn)[0] ∧
      (imm_operand imm sgn)[1] = (imm_to_KB imm sgn)[1] := by
    simp [imm_operand]

  /-- An operand's two pieces are 16-bit and its sign is 0 or 1. -/
  lemma imm_operand_limbs {w : ℕ} (imm : BitVec w) (sgn : Bool) :
      (imm_operand imm sgn)[0].val < 65536 ∧ (imm_operand imm sgn)[1].val < 65536 ∧
      ((imm_operand imm sgn)[2] = 0 ∨ (imm_operand imm sgn)[2] = 1) := by
    have h := imm_to_KB_limbs imm sgn
    simp only [Fin.lt_def] at h
    refine ⟨ h.1, h.2.1, ?_ ⟩
    simp only [imm_operand]
    split <;> simp

  /-- The split form: the two low pieces of the sign-extended value, and a sign that is 0 for
      a value below `2^31` and 1 for a value in the top `2^31` of the 64-bit range. -/
  lemma imm_operand_sext {w : ℕ} (imm : BitVec w) (hw0 : 0 < w) (hw : w ≤ 32) :
      let o := imm_operand imm true
      let sx := (BitVec.signExtend 64 imm).toNat
      o[0].val = sx % 65536 ∧ o[1].val = sx / 65536 % 65536 ∧
      ((o[2] = 0 ∧ sx < 2^31) ∨ (o[2] = 1 ∧ 2^64 - 2^31 ≤ sx ∧ sx < 2^64)) := by
    intro o sx
    have h_w : 2^w ≤ 2^32 := Nat.pow_le_pow_right (by norm_num) hw
    have h_lt : imm.toNat < 2^w := imm.isLt
    have h_half : 2^w = 2 * 2^(w-1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have h_sx : sx = imm.toNat + if imm.msb then 2^64 - 2^w else 0 := by
      simp only [sx, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (by omega)]
    have h_msb : imm.msb = decide (2^(w-1) ≤ imm.toNat) := BitVec.msb_eq_decide imm
    have h_sx_lt : sx < 2^64 := (BitVec.signExtend 64 imm).isLt
    have h_msb64 : (BitVec.signExtend 64 imm).msb = decide (2^63 ≤ sx) := BitVec.msb_eq_decide _
    simp only [o, imm_operand, imm_to_KB, BitVec.extend, U64w.fromNat]
    simp only [ite_true, h_msb64]
    simp
    refine ⟨ rfl, rfl, ?_ ⟩
    by_cases hm : imm.msb
    · simp [hm] at h_sx h_msb
      right
      refine ⟨ ?_, by omega, h_sx_lt ⟩
      omega
    · simp [hm] at h_sx h_msb
      left
      refine ⟨ ?_, by omega ⟩
      omega

  /-- For a signed immediate of at most 32 bits, pieces 2 and 3 of the 64-bit value are the
      sign fill `sign * 65535`: both 0 for a non-negative value, both `0xFFFF` for a negative
      one. -/
  lemma imm_operand_fill {w : ℕ} (imm : BitVec w) (hw0 : 0 < w) (hw : w ≤ 32) :
      (imm_to_KB imm true)[2] = (imm_operand imm true)[2] * 65535 ∧
      (imm_to_KB imm true)[3] = (imm_operand imm true)[2] * 65535 := by
    have h := imm_operand_sext imm hw0 hw
    simp only at h
    obtain ⟨ -, -, h_s ⟩ := h
    have h2 : ((imm_to_KB imm true)[2]).val =
        (BitVec.signExtend 64 imm).toNat / 4294967296 % 65536 := by
      simp [imm_to_KB, BitVec.extend, U64w.fromNat]
    have h3 : ((imm_to_KB imm true)[3]).val =
        (BitVec.signExtend 64 imm).toNat / 281474976710656 % 65536 := by
      simp [imm_to_KB, BitVec.extend, U64w.fromNat]
    rcases h_s with ⟨ hs, h_lt ⟩ | ⟨ hs, h_ge, h_lt ⟩ <;> rw [hs] <;>
      simp only [Fin.ext_iff, h2, h3] <;> norm_num <;> omega

  /-! ### Signed immediates (sgn = true)

      The 64-bit operand is `[o[0], o[1], o[2] * 65535, o[2] * 65535]`, the form the CPU
      chip's immediate constraints give its operand value (`value_2 = sign * 65535`,
      `value_3 = sign * 65535`). The product is taken in the field. -/

  lemma imm_operand_toBV_sgn {w : ℕ} (imm : BitVec w) (hw0 : 0 < w) (hw : w ≤ 32) :
      let o := imm_operand imm true
      U64w.toBV #v[o[0], o[1], (o[2] * 65535 : FKB), (o[2] * 65535 : FKB)] =
      BitVec.signExtend 64 imm := by
    intro o
    obtain ⟨ h2, h3 ⟩ := imm_operand_fill imm hw0 hw
    obtain ⟨ h0, h1 ⟩ := imm_operand_low imm true
    have h := imm_to_KB_BV_sgn imm
    simp only at h
    simp only [o, h0, h1]
    rw [← h2]
    nth_rewrite 2 [show (imm_to_KB imm true)[2] = (imm_to_KB imm true)[3] from h2.trans h3.symm]
    exact h

  lemma imm_operand_toNat_sgn {w : ℕ} (imm : BitVec w) (hw0 : 0 < w) (hw : w ≤ 32) :
      let o := imm_operand imm true
      U64w.toNat #v[o[0], o[1], (o[2] * 65535 : FKB), (o[2] * 65535 : FKB)] =
      (BitVec.signExtend 64 imm).toNat := by
    simp [← imm_operand_toBV_sgn imm hw0 hw]

  lemma imm_operand_toInt_sgn {w : ℕ} (imm : BitVec w) (hw0 : 0 < w) (hw : w ≤ 32) :
      let o := imm_operand imm true
      U64w.toInt #v[o[0], o[1], (o[2] * 65535 : FKB), (o[2] * 65535 : FKB)] =
      (BitVec.signExtend 64 imm).toInt := by
    simp [← imm_operand_toBV_sgn imm hw0 hw]

  /-! ### Unsigned immediates (sgn = false): shift amounts -/

  lemma imm_operand_usgn {w : ℕ} (imm : BitVec w) (hw : w ≤ 32) :
      (imm_operand imm false)[2] = 0 ∧
      (imm_to_KB imm false)[2] = 0 ∧ (imm_to_KB imm false)[3] = 0 := by
    have h_w : 2^w ≤ 2^32 := Nat.pow_le_pow_right (by norm_num) hw
    have h_lt : imm.toNat < 2^w := imm.isLt
    simp only [imm_operand, imm_to_KB, BitVec.extend, U64w.fromNat]
    simp [Fin.ext_iff, BitVec.msb_eq_decide]
    omega

  lemma imm_operand_toBV_usgn {w : ℕ} (imm : BitVec w) (hw : w ≤ 32) :
      let o := imm_operand imm false
      o[2] = 0 ∧ U64w.toBV #v[o[0], o[1], 0, 0] = BitVec.zeroExtend 64 imm := by
    intro o
    obtain ⟨ h_s, h2, h3 ⟩ := imm_operand_usgn imm hw
    refine ⟨ h_s, ?_ ⟩
    obtain ⟨ h0, h1 ⟩ := imm_operand_low imm false
    have h := imm_to_KB_BV_usgn imm
    simp only at h
    rw [h2, h3] at h
    simp only [o, h0, h1]
    exact h

  lemma imm_operand_toNat_usgn {w : ℕ} (imm : BitVec w) (hw : w ≤ 32) :
      let o := imm_operand imm false
      o[2] = 0 ∧ U64w.toNat #v[o[0], o[1], 0, 0] = (BitVec.zeroExtend 64 imm).toNat := by
    obtain ⟨ h_s, h ⟩ := imm_operand_toBV_usgn imm hw
    exact ⟨ h_s, by simp [← h] ⟩

  lemma imm_operand_toInt_usgn {w : ℕ} (imm : BitVec w) (hw : w ≤ 32) :
      let o := imm_operand imm false
      o[2] = 0 ∧ U64w.toInt #v[o[0], o[1], 0, 0] = (BitVec.zeroExtend 64 imm).toInt := by
    obtain ⟨ h_s, h ⟩ := imm_operand_toBV_usgn imm hw
    exact ⟨ h_s, by simp [← h] ⟩

  /-! ### 32-bit (W) values: the two low pieces alone -/

  lemma immw_operand_toBV_sgn {w : ℕ} (imm : BitVec w) :
      let o := imm_operand imm true
      U32w.toBV #v[o[0], o[1]] = BitVec.signExtend 32 imm :=
    immw_to_KB_BV_sgn imm

  lemma immw_operand_toNat_sgn {w : ℕ} (imm : BitVec w) :
      let o := imm_operand imm true
      U32w.toNat #v[o[0], o[1]] = (BitVec.signExtend 32 imm).toNat :=
    immw_to_KB_Nat_sgn imm

  lemma immw_operand_toInt_sgn {w : ℕ} (imm : BitVec w) :
      let o := imm_operand imm true
      U32w.toInt #v[o[0], o[1]] = (BitVec.signExtend 32 imm).toInt :=
    immw_to_KB_Int_sgn imm

  lemma immw_operand_toBV_usgn {w : ℕ} (imm : BitVec w) :
      let o := imm_operand imm false
      U32w.toBV #v[o[0], o[1]] = BitVec.setWidth 32 imm :=
    immw_to_KB_BV_usgn imm

  lemma immw_operand_toNat_usgn {w : ℕ} (imm : BitVec w) :
      let o := imm_operand imm false
      U32w.toNat #v[o[0], o[1]] = (BitVec.setWidth 32 imm).toNat :=
    immw_to_KB_Nat_usgn imm

  lemma immw_operand_toInt_usgn {w : ℕ} (imm : BitVec w) :
      let o := imm_operand imm false
      U32w.toInt #v[o[0], o[1]] = (BitVec.setWidth 32 imm).toInt :=
    immw_to_KB_Int_usgn imm

  /-! ### Register operands -/

  /-- `op_a_0` as the decoder writes it, on every row, is `[op_a = 0]` on the register index.
      The decoder types the flag as a field element, so `rw` finds this form on every row. -/
  lemma reg_is_x0 (rd : regidx) :
      (if (rd == regidx.Regidx 0) then (1 : FKB) else 0) =
      if reg_to_KB rd = 0 then 1 else 0 := by
    obtain ⟨ r ⟩ := rd
    have h : (regidx.Regidx r == regidx.Regidx 0) = (r == 0) := rfl
    rw [h]
    simp only [reg_to_KB, regidx_to_fin, Fin.ext_iff, Fin.val_zero]
    by_cases hr : r = 0
    · subst hr; simp
    · have : r.toNat ≠ 0 := by
        intro h0; apply hr; exact BitVec.eq_of_toNat_eq (by simpa using h0)
      simp only [this, if_false]
      split
      · rename_i hb; exfalso; apply this; simp at hb; subst hb; rfl
      · rfl

  /-- A register index is below 32. -/
  lemma val_reg_to_KB_lt (rd : regidx) : (reg_to_KB rd).val < 32 := by
    simp [reg_to_KB]

  /-- A register index is below any bound of at least 32, such as an operand piece's `2^16`. -/
  lemma val_reg_to_KB_lt_of_le {n : ℕ} (rd : regidx) (h : 32 ≤ n) : (reg_to_KB rd).val < n :=
    lt_of_lt_of_le (val_reg_to_KB_lt rd) h

  /-! ## Decoding -/

  /-- Decode one Sail instruction at address `pc` into a Program-bus message
      `(multiplicity, 26 fields)` and the side conditions the instruction satisfies.
      Returns `none` for an instruction the Program table has no row for. -/
  def transpile_op
    (inst : instruction)
    (multiplicity : FKB)
    (pc : ℕ)
  : Option ((FKB × Vector FKB 26) × Prop) :=
    match inst with
    -- R-type ALU: `op_b = rs1`, `op_c = rs2`, no immediate (`rrs.rs:13-22`).
    | .RTYPE (rs2, rs1, rd, op) =>
      let opcode := opcode_of_rop op
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0,                 -- imm_b, imm_c
              0, 0, 0,              -- is_ecall, is_memory, is_store
              0, 0, 0, 0, 0, 0,     -- is_beq .. is_bgeu
              0, 0,                 -- is_jalr, is_jal
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    | .RTYPEW (rs2, rs1, rd, op) =>
      let opcode := opcode_of_ropw op
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    -- I-type ALU: `op_c` is the sign-extended immediate, `imm_c = 1` (`rrs.rs:26-35`).
    | .ITYPE (imm, rs1, rd, op) =>
      let opcode := opcode_of_iop op
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let oc := imm_operand imm true
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              oc[0], oc[1], oc[2],
              a_is_0,
              0, 1,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) )
    | .ADDIW (imm, rs1, rd) =>
      let opcode : FKB := 40
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let oc := imm_operand imm true
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              oc[0], oc[1], oc[2],
              a_is_0,
              0, 1,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) )
    -- Shift by an immediate: the shift amount is zero-extended (`rrs.rs:39-61`).
    | .SHIFTIOP (imm, rs1, rd, op) =>
      let opcode := opcode_of_sop op
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let oc := imm_operand imm false
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              oc[0], oc[1], oc[2],
              a_is_0,
              0, 1,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) )
    | .SHIFTIWOP (imm, rs1, rd, op) =>
      let opcode := opcode_of_sopw op
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let oc := imm_operand imm false
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              oc[0], oc[1], oc[2],
              a_is_0,
              0, 1,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) )
    -- Loads: I-type shape, `is_memory = 1` (`rrs.rs:264-282, 452-458`).
    | .LOAD (imm, rs1, rd, is_unsigned, width) =>
      let opcode : FKB :=
        match is_unsigned, width with
        | false, 1 => 10   -- LB
        | true,  1 => 13   -- LBU
        | false, 2 => 11   -- LH
        | true,  2 => 14   -- LHU
        | false, 4 => 12   -- LW
        | true,  4 => 45   -- LWU
        | false, 8 => 46   -- LD
        | _, _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
        let oc := imm_operand imm true
        .some (
          ( multiplicity,
            #v[ pc_lo pc, pc_hi pc, opcode,
                opcode, reg_to_KB rd,
                reg_to_KB rs1, 0, 0,
                oc[0], oc[1], oc[2],
                a_is_0,
                0, 1,
                0, 1, 0,            -- is_memory = 1
                0, 0, 0, 0, 0, 0,
                0, 0,
                pc_carry pc ] ),
          is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) )
    -- Stores: `op_a = rs2`, `op_b = rs1`, `op_c = imm`; `op_a_0` is `[rs2 = x0]`
    -- (`rrs.rs:65-74`, `instruction/columns.rs:92`).
    | .STORE (imm, rs2, rs1, width) =>
      let opcode : FKB :=
        match width with
        | 1 => 15   -- SB
        | 2 => 16   -- SH
        | 4 => 17   -- SW
        | 8 => 47   -- SD
        | _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 : FKB := if (rs2 == regidx.Regidx 0) then 1 else 0
        let oc := imm_operand imm true
        .some (
          ( multiplicity,
            #v[ pc_lo pc, pc_hi pc, opcode,
                opcode, reg_to_KB rs2,
                reg_to_KB rs1, 0, 0,
                oc[0], oc[1], oc[2],
                a_is_0,
                0, 1,
                0, 1, 1,            -- is_memory = 1, is_store = 1
                0, 0, 0, 0, 0, 0,
                0, 0,
                pc_carry pc ] ),
          is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    -- Branches: `op_a = rs1`, `op_b = rs2`, `op_c = offset`, always `imm_c = 1`;
    -- `op_a_0` is `[rs1 = x0]` (`rrs.rs:78-87`).
    | .BTYPE (imm, rs2, rs1, op) =>
      let opcode := opcode_of_bop op
      let a_is_0 : FKB := if (rs1 == regidx.Regidx 0) then 1 else 0
      let oc := imm_operand imm true
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rs1,
              reg_to_KB rs2, 0, 0,
              oc[0], oc[1], oc[2],
              a_is_0,
              0, 1,
              0, 0, 0,
              (if op == .BEQ  then 1 else 0),
              (if op == .BNE  then 1 else 0),
              (if op == .BLT  then 1 else 0),
              (if op == .BGE  then 1 else 0),
              (if op == .BLTU then 1 else 0),
              (if op == .BGEU then 1 else 0),
              0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) ∧ imm % 2 = 0 )
    -- JALR: `op_b = rs1`, `op_c = offset`, `imm_c = 1` (`rrs.rs:331-340`).
    | .JALR (imm, rs1, rd) =>
      let opcode : FKB := 25
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let oc := imm_operand imm true
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              oc[0], oc[1], oc[2],
              a_is_0,
              0, 1,
              0, 0, 0,
              0, 0, 0, 0, 0, 0,
              1, 0,                 -- is_jalr = 1
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) )
    -- JAL: `op_b = offset`, `op_c = 0`, both immediate flags (`rrs.rs:320-329`).
    | .JAL (imm, rd) =>
      let opcode : FKB := 24
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let ob := imm_operand imm true
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              ob[0], ob[1], ob[2],
              0, 0, 0,
              a_is_0,
              1, 1,
              0, 0, 0,
              0, 0, 0, 0, 0, 0,
              0, 1,                 -- is_jal = 1
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ imm % 2 = 0 )
    -- LUI is `ADD rd, 0, imm`; AUIPC is `ADD rd, imm, pc`; both immediate flags
    -- (`rrs.rs:342-366`). Sail's `imm` is the upper 20 bits.
    -- The two give rows of the same shape, and no selector tells them apart; they can even
    -- give the same row (`LUI rd, 0x10` and `AUIPC rd, 0` at `0x10000` both give
    -- `ADD rd, 0, 0x10000`). A row of this shape is one of the two, not a particular one.
    | .UTYPE (imm, rd, op) =>
      let opcode : FKB := 0
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      let u := imm_operand (imm ++ 0#12) true
      let ob : Vector FKB 3 := if op == .AUIPC then u else #v[0, 0, 0]
      let oc : Vector FKB 3 := if op == .AUIPC then #v[pc_lo pc, pc_hi pc, 0] else u
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              ob[0], ob[1], ob[2],
              oc[0], oc[1], oc[2],
              a_is_0,
              1, 1,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) )
    -- ECALL: `op_a = x5`, `op_b = x10`, `op_c = x11`, registers only (`rrs.rs:368-377`).
    | .ECALL () =>
      let opcode : FKB := 28
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, 5,
              10, 0, 0,
              11, 0, 0,
              0,
              0, 0,
              1, 0, 0,              -- is_ecall = 1
              0, 0, 0, 0, 0, 0,
              0, 0,
              pc_carry pc ] ),
        True )
    -- RV64M: R-type shape.
    | .MUL (rs2, rs1, rd, op) =>
      let opcode : FKB :=
        match op with
        | { result_part := .Low,  signed_rs1 := _,         signed_rs2 := _ }         => 30
        | { result_part := .High, signed_rs1 := .Signed,   signed_rs2 := .Signed }   => 31
        | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => 32
        | { result_part := .High, signed_rs1 := .Signed,   signed_rs2 := .Unsigned } => 33
        | _ => 0
      match opcode with
      | 0 => .none
      | opcode =>
        let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
        .some (
          ( multiplicity,
            #v[ pc_lo pc, pc_hi pc, opcode,
                opcode, reg_to_KB rd,
                reg_to_KB rs1, 0, 0,
                reg_to_KB rs2, 0, 0,
                a_is_0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                pc_carry pc ] ),
          is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    | .MULW (rs2, rs1, rd) =>
      let opcode : FKB := 48
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    -- Sail's fourth field is `is_unsigned`: DIV 34 / DIVU 35, REM 36 / REMU 37,
    -- DIVW 49 / DIVUW 50, REMW 51 / REMUW 52.
    | .DIV (rs2, rs1, rd, sgn) =>
      let opcode : FKB := match sgn with | true => 35 | false => 34
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    | .DIVW (rs2, rs1, rd, sgn) =>
      let opcode : FKB := match sgn with | true => 50 | false => 49
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    | .REM (rs2, rs1, rd, sgn) =>
      let opcode : FKB := match sgn with | true => 37 | false => 36
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    | .REMW (rs2, rs1, rd, sgn) =>
      let opcode : FKB := match sgn with | true => 52 | false => 51
      let a_is_0 : FKB := if (rd == regidx.Regidx 0) then 1 else 0
      .some (
        ( multiplicity,
          #v[ pc_lo pc, pc_hi pc, opcode,
              opcode, reg_to_KB rd,
              reg_to_KB rs1, 0, 0,
              reg_to_KB rs2, 0, 0,
              a_is_0,
              0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              pc_carry pc ] ),
        is_register (reg_to_KB rd) ∧ is_register (reg_to_KB rs1) ∧ is_register (reg_to_KB rs2) )
    -- Traps and every constructor not listed: no Program-table row.
    | _ => .none

  /-! ## Pico's decoder tests

      The four unit tests of `rrs.rs` (`:577-669`), restated on this decoder's message with
      multiplicity 1: each of their five row checks, and the no-op row their `FENCE` test
      compares every fence word with. Also the `LUI` / `AUIPC` coincidence noted at the `UTYPE`
      case. The slot addresses are Pico's `PC_BASE = 0x10000` plus 4 per slot. -/

  section Examples

    /-- `auipc x1, 0x1000` at `0x10000` gives `ADD x1, 0x0100_0000, 0x10000` (`rrs.rs:589-593`). -/
    example :
        (transpile_op (.UTYPE (0x1000#20, regidx.Regidx 1#5, .AUIPC)) 1 0x10000).map (·.1) =
        some (1, #v[0, 1, 0,  0, 1,  0, 0x0100, 0,  0, 1, 0,  0,  1, 1,
                    0, 0, 0,  0, 0, 0, 0, 0, 0,  0, 0,  0]) := by
      have h : (uop.AUIPC == uop.AUIPC) = true := rfl
      simp [transpile_op, h, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend, pc_lo, pc_hi,
            pc_carry, reg_to_KB, regidx_to_fin]
      decide

    /-- `auipc x2, 0` in the next slot, `0x10004`, gives `ADD x2, 0, 0x10004` (`rrs.rs:596-600`):
        the folded address is the slot's own. -/
    example :
        (transpile_op (.UTYPE (0#20, regidx.Regidx 2#5, .AUIPC)) 1 0x10004).map (·.1) =
        some (1, #v[4, 1, 0,  0, 2,  0, 0, 0,  4, 1, 0,  0,  1, 1,
                    0, 0, 0,  0, 0, 0, 0, 0, 0,  0, 0,  0]) := by
      have h : (uop.AUIPC == uop.AUIPC) = true := rfl
      simp [transpile_op, h, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend, pc_lo, pc_hi,
            pc_carry, reg_to_KB, regidx_to_fin]

    /-- `auipc x3, 0xfffff` at `0x10000`: the immediate `-0x1000` is the pieces `0xF000`,
        `0xFFFF` and sign 1 (`rrs.rs:612-615`). -/
    example :
        (transpile_op (.UTYPE (0xFFFFF#20, regidx.Regidx 3#5, .AUIPC)) 1 0x10000).map (·.1) =
        some (1, #v[0, 1, 0,  0, 3,  0xF000, 0xFFFF, 1,  0, 1, 0,  0,  1, 1,
                    0, 0, 0,  0, 0, 0, 0, 0, 0,  0, 0,  0]) := by
      have h : (uop.AUIPC == uop.AUIPC) = true := rfl
      simp [transpile_op, h, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend, pc_lo, pc_hi,
            pc_carry, reg_to_KB, regidx_to_fin]
      decide

    /-- `lui x4, 0x2` gives `ADD x4, 0, 0x2000` at every address (`rrs.rs:638-642`): no operand
        holds the pc. -/
    example (pc : ℕ) :
        (transpile_op (.UTYPE (0x2#20, regidx.Regidx 4#5, .LUI)) 1 pc).map (·.1) =
        some (1, #v[pc_lo pc, pc_hi pc, 0,  0, 4,  0, 0, 0,  0x2000, 0, 0,  0,  1, 1,
                    0, 0, 0,  0, 0, 0, 0, 0, 0,  0, 0,  pc_carry pc]) := by
      have h : (uop.LUI == uop.AUIPC) = false := rfl
      simp [transpile_op, h, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend, reg_to_KB,
            regidx_to_fin]
      decide

    /-- `auipc x5, 0x1` in slot 2, `0x10008`, after a `LUI` and a no-op, gives
        `ADD x5, 0x1000, 0x10008` (`rrs.rs:643-647`). -/
    example :
        (transpile_op (.UTYPE (0x1#20, regidx.Regidx 5#5, .AUIPC)) 1 0x10008).map (·.1) =
        some (1, #v[8, 1, 0,  0, 5,  0x1000, 0, 0,  8, 1, 0,  0,  1, 1,
                    0, 0, 0,  0, 0, 0, 0, 0, 0,  0, 0,  0]) := by
      have h : (uop.AUIPC == uop.AUIPC) = true := rfl
      simp [transpile_op, h, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend, pc_lo, pc_hi,
            pc_carry, reg_to_KB, regidx_to_fin]
      decide

    /-- `ADDI x0, x0, 0` gives Pico's no-op row `ADD x0, x0, 0` with `imm_c` set
        (`Instruction::nop`, `rrs.rs:95-100`) at every address. Pico's `FENCE` test
        (`rrs.rs:652-669`) checks that every fence word (`fence rw,rw`, `fence.tso`, `pause`,
        `fence 0,0`, `fence iorw,iorw`) transpiles to this row. -/
    example (pc : ℕ) :
        (transpile_op (.ITYPE (0#12, regidx.Regidx 0#5, regidx.Regidx 0#5, .ADDI)) 1 pc).map
          (·.1) =
        some (1, #v[pc_lo pc, pc_hi pc, 0,  0, 0,  0, 0, 0,  0, 0, 0,  1,  0, 1,
                    0, 0, 0,  0, 0, 0, 0, 0, 0,  0, 0,  pc_carry pc]) := by
      simp [transpile_op, opcode_of_iop, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend,
            reg_to_KB, regidx_to_fin]

    /-- `LUI rd, 0x10` and `AUIPC rd, 0` at `0x10000` give the same message. -/
    example (rd : regidx) :
        (transpile_op (.UTYPE (0x10#20, rd, .LUI)) 1 0x10000).map (·.1) =
        (transpile_op (.UTYPE (0#20, rd, .AUIPC)) 1 0x10000).map (·.1) := by
      have h1 : (uop.LUI == uop.AUIPC) = false := rfl
      have h2 : (uop.AUIPC == uop.AUIPC) = true := rfl
      simp [transpile_op, h1, h2, imm_operand, imm_to_KB, U64w.fromNat, BitVec.extend, pc_lo,
            pc_hi]
      decide

  end Examples

end Transpiler.V3
