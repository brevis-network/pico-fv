import PicoFV.RV64IM.Transpiler.Transpiler

/-! # Instruction decoder for the Pico v3.1.1 Program table (draft)

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
    * trap instructions (`EBREAK`, `UNIMP`, CSR, `MRET`, `WFI`) have no row: the Program table
      gives them no pc of their own (`riscv_program/traces.rs:111-120`), so the decoder returns
      `none` for them, as for every constructor it does not list;
    * no evenness side condition on the `JALR` offset: RISC-V allows an odd one, and the chip
      clears the low bit itself (`riscv_cpu/jump/constraints.rs:79-126`).

    Draft: the definitions are complete for every instruction the CPU chip accepts; the
    lemmas that relate a row back to its instruction and its operands to 64-bit values come
    with the full decoder.                                                                  -/

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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
        let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
        let a_is_0 := if (rs2 == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rs1 == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
    | .UTYPE (imm, rd, op) =>
      let opcode : FKB := 0
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
        let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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
      let a_is_0 := if (rd == regidx.Regidx 0) then 1 else 0
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

end Transpiler.V3
