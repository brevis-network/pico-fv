import PicoFV.Fundamentals.Interaction

import PicoFV.RV64IM.Transpiler.Transpiler
import PicoFV.RV64IM.RVSail.Execution

set_option maxHeartbeats 1_000_000_000

/-! # RV64 bus interactions

    Mirrors `PicoFV/RV32IM/RVSail/Buses.lean` for the RV64 Pico backend.
    Bus identifiers and roles are unchanged from the 32-bit version, but the
    payloads differ:

    * `pc` widens from `1` field element to `3` u16-limb fields
      (`Addr<T> = [T; 3]`, 48-bit address space).
    * `Word<T>` becomes `[T; 4]` of u16 limbs (vs `[T; 4]` of u8 bytes in
      RV32) — so operand limbs are bounded by `< 65536` rather than `< 256`.
    * The program bus gains 3 new memory selectors (`is_lwu`, `is_ld`,
      `is_sd`) and the W-variant ALU opcodes (40..44, 48..52); the memory
      bus inherits the 3 new memory selectors.
    * The state bus' single `ptr` field becomes 3 u16 limbs for the 48-bit
      register/memory address.

    Bus tag → payload length (from `Extraction/CpuChip.lean`):

    | bus | tag | data length |
    |-----|-----|-------------|
    | State   | 0 | 9   |
    | Program | 1 | 43  |
    | ALU     | 3 | 13  |
    | Byte    | 4 | 5   |
    | Memory  | 0 | 25  |
                                                                              -/

namespace RV64IM_Interactions

  open Interaction

  section Buses

    variable
      (F : Type)
      [Field F]

    section ProgramBus

      /-- Program bus entry — payload size 43 (`3 + 1 + 14 + 25`).

          Layout matches the `CpuChip` program-bus emit at
          `Extraction/CpuChip.lean:451`:
          `[pc[0..2], opcode, opcode, a[0..3], b[0..3], c[0..3], a_is_0,
            imm_b, imm_c, is_alu, is_ecall,
            is_lb..is_ld (7),
            is_sb..is_sd (4),
            is_beq..is_bgeu (6),
            is_jalr, is_jal,
            is_auipc, is_unimpl]`.                                          -/
      structure ProgramBusEntry where
        multiplicity : F
        pc_0 : F
        pc_1 : F
        pc_2 : F
        opcode : F
        opcode' : F
        a_0 : F
        a_1 : F
        a_2 : F
        a_3 : F
        b_0 : F
        b_1 : F
        b_2 : F
        b_3 : F
        c_0 : F
        c_1 : F
        c_2 : F
        c_3 : F
        a_is_0 : F
        imm_b : F
        imm_c : F
        is_alu : F
        is_ecall : F
        is_lb : F
        is_lbu : F
        is_lh : F
        is_lhu : F
        is_lw : F
        is_lwu : F      -- new for RV64
        is_ld : F       -- new for RV64
        is_sb : F
        is_sh : F
        is_sw : F
        is_sd : F       -- new for RV64
        is_beq : F
        is_bne : F
        is_blt : F
        is_bge : F
        is_bltu : F
        is_bgeu : F
        is_jalr : F
        is_jal : F
        is_auipc : F
        is_unimpl : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def ProgramBusEntry.deserialise
        (entry : FKB × Vector FKB 43)
      : ProgramBusEntry FKB :=
        {
          multiplicity := entry.1,
          pc_0 := entry.2[0],
          pc_1 := entry.2[1],
          pc_2 := entry.2[2],
          opcode := entry.2[3],
          opcode' := entry.2[4],
          a_0 := entry.2[5],
          a_1 := entry.2[6],
          a_2 := entry.2[7],
          a_3 := entry.2[8],
          b_0 := entry.2[9],
          b_1 := entry.2[10],
          b_2 := entry.2[11],
          b_3 := entry.2[12],
          c_0 := entry.2[13],
          c_1 := entry.2[14],
          c_2 := entry.2[15],
          c_3 := entry.2[16],
          a_is_0 := entry.2[17],
          imm_b := entry.2[18],
          imm_c := entry.2[19],
          is_alu := entry.2[20],
          is_ecall := entry.2[21],
          is_lb := entry.2[22],
          is_lbu := entry.2[23],
          is_lh := entry.2[24],
          is_lhu := entry.2[25],
          is_lw := entry.2[26],
          is_lwu := entry.2[27],
          is_ld := entry.2[28],
          is_sb := entry.2[29],
          is_sh := entry.2[30],
          is_sw := entry.2[31],
          is_sd := entry.2[32],
          is_beq := entry.2[33],
          is_bne := entry.2[34],
          is_blt := entry.2[35],
          is_bge := entry.2[36],
          is_bltu := entry.2[37],
          is_bgeu := entry.2[38],
          is_jalr := entry.2[39],
          is_jal := entry.2[40],
          is_auipc := entry.2[41],
          is_unimpl := entry.2[42],
        }

      /-- A `ProgramBusEntry` is well-formed iff there exists a Sail instruction
          whose RV64 transpilation produces this row. -/
      def ProgramBusEntry.operand_properties (entry : ProgramBusEntry FKB) : Prop :=
        ∃ instruction data props,
          (.some ⟨ data, props ⟩ =
            Transpiler.transpile_op instruction entry.multiplicity
              #v[entry.pc_0, entry.pc_1, entry.pc_2]) ∧
          (entry = ProgramBusEntry.deserialise data) ∧
          props

      instance : LawfulBEq bop where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      instance : LawfulBEq iop where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      instance : LawfulBEq rop where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      instance : LawfulBEq sop where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      instance : LawfulBEq uop where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      instance : LawfulBEq ropw where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      instance : LawfulBEq sopw where
        rfl := by intro op; cases op <;> rfl
        eq_of_beq := by intro op₁ op₂; cases op₁ <;> cases op₂ <;> simp <;> rfl

      /-- The opcode produced by `transpile_op` lies in the union of three
          contiguous ranges, with the unused RV32-inherited slots (`26`,
          `29`) and the gap between MUL/DIV/REM (`≤ 37`) and the W-variant
          ALU ops (`40..44`) (`38, 39`) explicitly excluded. -/
      lemma ProgramBusEntry.inversion_opcode_bounds
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ =
          Transpiler.transpile_op instr entry.multiplicity
            #v[entry.pc_0, entry.pc_1, entry.pc_2])
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        (entry.opcode.val ≤ 37 ∨
         (40 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 47) ∨
         (48 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 52)) ∧
        entry.opcode.val ≠ 26 ∧ entry.opcode.val ≠ 29 ∧ entry.opcode.val ≠ 38 ∧ entry.opcode.val ≠ 39
      := by
        have h_op_eq : entry.opcode = data.2[3]
        := by
          clear *- h_deser
          simp [deserialise] at h_deser
          grind
        simp [h_op_eq]; clear h_deser h_op_eq
        simp [
          Transpiler.transpile_op,
          Transpiler.opcode_of_rop,
          Transpiler.opcode_of_iop,
          Transpiler.opcode_of_sop,
          Transpiler.opcode_of_bop,
          Transpiler.opcode_of_uop,
          Transpiler.opcode_of_ropw,
          Transpiler.opcode_of_sopw
        ] at h_trans
        cases instr <;> simp at h_trans
        all_goals
          try (obtain ⟨ h_trans, h_props ⟩ := h_trans)
          try simp [h_trans]
          try grind
        all_goals
          split at h_trans <;>
          simp at h_trans
          simp [h_trans]
          grind (splits := 16)

      /-- For each opcode value, fixes the Sail constructor (or rules it out).
          Analogous in spirit to the RV32 version but with
          additional cases for `RTYPEW`, `SHIFTIWOP`, `ADDIW`, `MULW`, `DIVW`,
          `REMW`, and the new memory ops `LWU`, `LD`, `SD`. -/
      lemma ProgramBusEntry.operand_properties_inversion
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ =
          Transpiler.transpile_op instr entry.multiplicity
            #v[entry.pc_0, entry.pc_1, entry.pc_2])
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        -- RV32-shared opcodes (0..37 minus 26, 29 placeholders)
        (entry.opcode = 0 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .ADD)) ∨
          (entry.imm_b = 0 ∧ entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ADDI)) ∨
          (entry.imm_b = 1 ∧ entry.imm_c = 1 ∧ ∃ imm rd, instr = .UTYPE (imm, rd, .LUI))) ∧
        (entry.opcode = 1 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SUB))) ∧
        (entry.opcode = 2 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .XOR)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .XORI))) ∧
        (entry.opcode = 3 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .OR)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ORI))) ∧
        (entry.opcode = 4 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .AND)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ANDI))) ∧
        (entry.opcode = 5 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SLL)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SLLI))) ∧
        (entry.opcode = 6 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SRL)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SRLI))) ∧
        (entry.opcode = 7 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SRA)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SRAI))) ∧
        (entry.opcode = 8 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SLT)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .SLTI))) ∧
        (entry.opcode = 9 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SLTU)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .SLTIU))) ∧
        -- LOAD family (RV64: LW is signed; LWU/LD are new)
        (entry.opcode = 10 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 1)) ∧
        (entry.opcode = 11 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 2)) ∧
        (entry.opcode = 12 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 4)) ∧
        (entry.opcode = 13 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 1)) ∧
        (entry.opcode = 14 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 2)) ∧
        (entry.opcode = 45 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 4)) ∧
        (entry.opcode = 46 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 8)) ∧
        -- STORE family (SD is new)
        (entry.opcode = 15 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 1)) ∧
        (entry.opcode = 16 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 2)) ∧
        (entry.opcode = 17 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 4)) ∧
        (entry.opcode = 47 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 8)) ∧
        -- Branches
        (entry.opcode = 18 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BEQ)) ∧
        (entry.opcode = 19 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BNE)) ∧
        (entry.opcode = 20 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BLT)) ∧
        (entry.opcode = 21 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BGE)) ∧
        (entry.opcode = 22 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BLTU)) ∧
        (entry.opcode = 23 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BGEU)) ∧
        -- Jumps
        (entry.opcode = 24 → ∃ imm rd, instr = .JAL (imm, rd)) ∧
        (entry.opcode = 25 → ∃ imm rs1 rd, instr = .JALR (imm, rs1, rd)) ∧
        -- AUIPC, ECALL
        (entry.opcode = 27 → ∃ imm rd, instr = .UTYPE (imm, rd, .AUIPC)) ∧
        (entry.opcode = 28 → instr = .ECALL ()) ∧
        -- MUL family (64-bit)
        (entry.opcode = 30 → ∃ rs2 rs1 rd sl sr, instr = .MUL (rs2, rs1, rd, { result_part := .Low, signed_rs1 := sl, signed_rs2 := sr })) ∧
        (entry.opcode = 31 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed })) ∧
        (entry.opcode = 32 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) ∧
        (entry.opcode = 33 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })) ∧
        -- DIV/REM (64-bit). Sail's 4th-field bool is `is_unsigned`:
        --   chip opcode 34 = DIV  (signed,   `is_unsigned = false`),
        --   chip opcode 35 = DIVU (unsigned, `is_unsigned = true`),
        --   chip opcode 36 = REM  (signed,   `is_unsigned = false`),
        --   chip opcode 37 = REMU (unsigned, `is_unsigned = true`).
        (entry.opcode = 34 → ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, false)) ∧
        (entry.opcode = 35 → ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, true)) ∧
        (entry.opcode = 36 → ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, false)) ∧
        (entry.opcode = 37 → ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, true)) ∧
        -- W-variants of R-type ops (RV64-only)
        (entry.opcode = 40 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .ADDW)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ADDIW (imm, rs1, rd))) ∧
        (entry.opcode = 41 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SUBW))) ∧
        (entry.opcode = 42 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SLLW)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIWOP (imm, rs1, rd, .SLLIW))) ∧
        (entry.opcode = 43 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SRLW)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIWOP (imm, rs1, rd, .SRLIW))) ∧
        (entry.opcode = 44 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SRAW)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIWOP (imm, rs1, rd, .SRAIW))) ∧
        -- W-variants of MUL/DIV/REM
        (entry.opcode = 48 → ∃ rs2 rs1 rd, instr = .MULW (rs2, rs1, rd)) ∧
        -- DIVW/REMW (RV64-only 32-bit). Same `is_unsigned` convention as above:
        --   chip opcode 49 = DIVW,  opcode 50 = DIVUW,
        --   chip opcode 51 = REMW,  opcode 52 = REMUW.
        (entry.opcode = 49 → ∃ rs2 rs1 rd, instr = .DIVW (rs2, rs1, rd, false)) ∧
        (entry.opcode = 50 → ∃ rs2 rs1 rd, instr = .DIVW (rs2, rs1, rd, true)) ∧
        (entry.opcode = 51 → ∃ rs2 rs1 rd, instr = .REMW (rs2, rs1, rd, false)) ∧
        (entry.opcode = 52 → ∃ rs2 rs1 rd, instr = .REMW (rs2, rs1, rd, true))
      := by
        have ⟨ h_op_eq, h_imm_b_eq, h_imm_c_eq ⟩ :
            entry.opcode = data.2[3] ∧ entry.imm_b = data.2[18] ∧ entry.imm_c = data.2[19]
        := by
          clear *- h_deser
          simp [deserialise] at h_deser
          grind
        clear h_deser;
        simp [
          Transpiler.transpile_op,
          Transpiler.opcode_of_rop,
          Transpiler.opcode_of_iop,
          Transpiler.opcode_of_sop,
          Transpiler.opcode_of_bop,
          Transpiler.opcode_of_uop,
          Transpiler.opcode_of_ropw,
          Transpiler.opcode_of_sopw
        ] at h_trans
        cases instr <;> simp at h_trans

        case LOAD instr =>
          split at h_trans
          . grind
          . case h_2 opcode h =>
              split at h <;> simp [*] at h_trans <;>
              simp [h_trans.1] at h_op_eq h_imm_b_eq h_imm_c_eq <;>
              clear h_trans <;>
              simp [*] <;>
              grind

        case STORE instr =>
          split at h_trans
          . grind
          . case h_2 opcode h =>
              split at h <;> simp [*] at h_trans <;>
              simp [h_trans.1] at h_op_eq h_imm_b_eq h_imm_c_eq <;>
              clear h_trans <;>
              simp [*] <;>
              grind

        case MUL instr =>
          split at h_trans
          . grind
          . case h_2 opcode h =>
              split at h <;> simp [*] at h_trans <;>
              simp [h_trans.1] at h_op_eq h_imm_b_eq h_imm_c_eq <;>
              clear h_trans <;>
              simp [*] <;>
              grind

        all_goals
          simp [h_trans.1] at h_op_eq h_imm_b_eq h_imm_c_eq
          clear h_trans
          (try split at h_op_eq) <;>
          simp [*] <;>
          grind

      /-- For each opcode produced by the transpiler the 23-tuple of opcode
          selectors

          `(is_alu, is_ecall,
            is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld,
            is_sb, is_sh, is_sw, is_sd,
            is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
            is_jalr, is_jal,
            is_auipc, is_unimpl)`

          is forced to a unique value; whenever a single instruction
          constructor maps to a given opcode the matching `imm_b` / `imm_c`
          are also forced. (When several constructors share an opcode —
          e.g. `0` = ADD/ADDI/LUI, or `40` = ADDW/ADDIW — the unconstrained
          immediate-marker is captured by `operand_properties_inversion`.)
                                                                              -/
      lemma ProgramBusEntry.inversion_opcode_selectors
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ =
          Transpiler.transpile_op instr entry.multiplicity
            #v[entry.pc_0, entry.pc_1, entry.pc_2])
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        -- Opcodes 0..9 — R-type / ITYPE / SHIFTIOP / (LUI at 0).  For
        -- opcode 0 both `imm_b` and `imm_c` vary; for 1..9 only `imm_c`
        -- varies (covered by `operand_properties_inversion`).
        (entry.opcode = 0 → ( entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 1 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 2 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 3 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 4 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 5 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 6 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 7 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 8 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 9 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- Opcodes 10..14 — RV32-shared loads.  `imm_b = 0`, `imm_c = 1`.
        (entry.opcode = 10 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 11 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 12 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 13 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 14 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- Opcodes 15..17 — RV32-shared stores.
        (entry.opcode = 15 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 16 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 17 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- Opcodes 18..23 — branches.
        (entry.opcode = 18 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 19 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 20 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 21 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 22 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 23 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 )) ∧
        -- Jumps: JAL = 24 (imm_b = 1, imm_c = 1); JALR = 25 (imm_b = 0).
        (entry.opcode = 24 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 )) ∧
        (entry.opcode = 25 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 )) ∧
        -- AUIPC at 27, ECALL at 28.
        (entry.opcode = 27 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 )) ∧
        (entry.opcode = 28 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- MUL family at 30..33 — all `imm_b = 0`, `imm_c = 0`, `is_alu = 1`.
        (entry.opcode = 30 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 31 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 32 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 33 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- DIV/REM at 34..37.
        (entry.opcode = 34 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 35 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 36 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 37 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- W-variants at 40..44.  Opcode 41 (SUBW) has unique constructor, so
        -- both `imm_b` and `imm_c` are forced to 0; opcodes 40, 42, 43, 44
        -- admit both an `RTYPEW` and an immediate variant, leaving `imm_c`
        -- unconstrained (covered by `operand_properties_inversion`).
        (entry.opcode = 40 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 41 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 42 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 43 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 44 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- New RV64 memory ops: LWU = 45, LD = 46, SD = 47.
        (entry.opcode = 45 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 46 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 47 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        -- MULW = 48 and DIV/REM-W family at 49..52 — all `imm_b = 0`,
        -- `imm_c = 0`, `is_alu = 1`.
        (entry.opcode = 48 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 49 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 50 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 51 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 52 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_lwu, entry.is_ld, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_sd, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ))
      := by
        simp [
          Transpiler.transpile_op,
          Transpiler.opcode_of_rop,
          Transpiler.opcode_of_iop,
          Transpiler.opcode_of_sop,
          Transpiler.opcode_of_bop,
          Transpiler.opcode_of_uop,
          Transpiler.opcode_of_ropw,
          Transpiler.opcode_of_sopw
        ] at h_trans
        split at h_trans <;> try simp at h_trans
        -- 1. RTYPE
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 2. RTYPEW
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 3. ITYPE
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 4. ADDIW
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 5. SHIFTIOP
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 6. SHIFTIWOP
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 7. LOAD (inner match)
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
          grind
        -- 8. STORE (inner match)
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
          grind
        -- 9. BTYPE
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 10. JALR
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 11. JAL
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 12. UTYPE
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 13. MUL (inner match)
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
        -- 14. MULW
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 15. DIV (sgn match in opcode)
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 16. DIVW (sgn match in opcode)
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 17. REM (sgn match in opcode)
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 18. REMW (sgn match in opcode)
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp

      /-- For immediate-bearing rows the four operand limbs respect the u16
          range used by RV64 (`< 65536`). The RV32 analogue used `< 256`. -/
      lemma ProgramBusEntry.ub_imm
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ =
          Transpiler.transpile_op instr entry.multiplicity
            #v[entry.pc_0, entry.pc_1, entry.pc_2])
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        (entry.imm_b = 1 → entry.b_0.val < 65536 ∧ entry.b_1.val < 65536 ∧
                           entry.b_2.val < 65536 ∧ entry.b_3.val < 65536) ∧
        (entry.imm_c = 1 → entry.c_0.val < 65536 ∧ entry.c_1.val < 65536 ∧
                           entry.c_2.val < 65536 ∧ entry.c_3.val < 65536)
      := by
        simp [
          Transpiler.transpile_op,
          Transpiler.opcode_of_rop,
          Transpiler.opcode_of_iop,
          Transpiler.opcode_of_sop,
          Transpiler.opcode_of_bop,
          Transpiler.opcode_of_uop,
          Transpiler.opcode_of_ropw,
          Transpiler.opcode_of_sopw
        ] at h_trans
        split at h_trans <;> try simp at h_trans
        -- 1. RTYPE: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 2. RTYPEW: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 3. ITYPE: imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 4. ADDIW: imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 5. SHIFTIOP: imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 6. SHIFTIWOP: imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 7. LOAD (inner match): imm_c = 1
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 8. STORE (inner match): imm_c = 1
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 9. BTYPE: imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 10. JALR: imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 11. JAL: imm_b = 1, imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 12. UTYPE: imm_b = 1, imm_c = 1
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> clear *- <;> grind [Transpiler.imm_to_KB_limbs]
        -- 13. MUL (inner match): no imm
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
        -- 14. MULW: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 15. DIV: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 16. DIVW: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 17. REM: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        -- 18. REMW: no imm
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp

      /-- Program bus entry instance.

          `axioms` requires the program counter (3 u16 limbs encoding a 48-bit
          address) to be 4-byte aligned and to lie below `2^48`.             -/
      @[simp, grind]
      instance ProgramBusEntryInstance
      : BusEntry FKB (ProgramBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 43,
          data := fun ⟨_, pc_0, pc_1, pc_2, opcode, opcode', a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, imm_b, imm_c, is_alu, is_ecall, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, is_auipc, is_unimpl⟩ =>
                    #v[pc_0, pc_1, pc_2, opcode, opcode', a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, imm_b, imm_c, is_alu, is_ecall, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, is_auipc, is_unimpl]

          -- Program counter is bounded and 4-byte aligned axiomatically.
          -- `< 2^48` follows from each limb being u16-bounded (externally
          -- enforced via the byte-bus `U16Range`), so the bound below is
          -- precise — no headroom needed for `pc + 4`, since RV64 PC values
          -- only need to fit in 48 bits, not the full 64.
          axioms := fun entry =>
            (¬ entry.multiplicity = 0) →
              entry.pc_0.val % 4 = 0

          -- No chip-external constraints
          externals := fun _ => True

          -- Well-formedness entirely derived from the fact that the entries
          -- come from the transpiler
          wf_properties := ProgramBusEntry.operand_properties

          deserialise := ProgramBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 64) (gen := 64) (ematch := 32) (ringSteps := 16384)
      }

    end ProgramBus

    section ALUBus

      /-- ALU bus entry — payload size 13.

          Layout: `[ALU_opcode, a[0..3], b[0..3], c[0..3]]`. Each operand limb
          is a u16 (vs u8 in RV32). -/
      structure ALUBusEntry where
        multiplicity : F
        ALU_opcode : F
        a_0 : F
        a_1 : F
        a_2 : F
        a_3 : F
        b_0 : F
        b_1 : F
        b_2 : F
        b_3 : F
        c_0 : F
        c_1 : F
        c_2 : F
        c_3 : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def ALUBusEntry.deserialise
        (entry : FKB × Vector FKB 13)
      : ALUBusEntry FKB :=
        {
          multiplicity := entry.1,
          ALU_opcode := entry.2[0],
          a_0 := entry.2[1],
          a_1 := entry.2[2],
          a_2 := entry.2[3],
          a_3 := entry.2[4],
          b_0 := entry.2[5],
          b_1 := entry.2[6],
          b_2 := entry.2[7],
          b_3 := entry.2[8],
          c_0 := entry.2[9],
          c_1 := entry.2[10],
          c_2 := entry.2[11],
          c_3 := entry.2[12],
        }

      /-- Set of ALU bus opcodes whose backing chip / gadget enforces
          u16 operand limb bounds *internally*. For these opcodes the
          chip can prove `operand_range` from its own constraints, so
          `operand_range` lives in `wf_properties` and *not* in
          `externals`.

          From inspection of the Pico Rust sources & extracted Lean
          chips:
          - `BitwiseChip` (2, 3, 4): byte-bus AND/OR/XOR lookups require
            `x_2 < 256 ∧ x_3 < 256` on the operand bytes after the
            u16→u8 split, giving full u16 bounds.
          - `MulChip` / `MulwChip` (30..33, 48): `MulGadget` emits
            `[byte_op = 7] (low_byte, (limb − low_byte)·inv(256))` pairs
            for each operand limb. -/
      def ALUBus.operandsInternal (ALU_opcode : FKB) : Prop :=
        ALU_opcode ∈ Finset.Icc 2 4 ∨
        ALU_opcode ∈ Finset.Icc 30 33 ∨
        ALU_opcode = 48

      /-- Set of all valid ALU bus opcodes. -/
      def ALUBus.validOpcode (ALU_opcode : FKB) : Prop :=
        ALU_opcode ∈ Finset.Icc 0 9 ∨
        ALU_opcode ∈ Finset.Icc 30 37 ∨
        ALU_opcode ∈ Finset.Icc 40 44 ∨
        ALU_opcode ∈ Finset.Icc 48 52

      /-- Per-entry operand u16 range (all 8 limbs). -/
      def ALUBus.operandRange
        (b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 : FKB) : Prop :=
        b_0.val < 65536 ∧ b_1.val < 65536 ∧ b_2.val < 65536 ∧ b_3.val < 65536 ∧
        c_0.val < 65536 ∧ c_1.val < 65536 ∧ c_2.val < 65536 ∧ c_3.val < 65536

      /-- ALU bus pure specification (the `wf_properties` payload).

          For every valid opcode the spec asserts `result_range` (all
          four result limbs are u16) — factored to the top — and then a
          per-opcode arithmetic relation `a = <pure execute function>`.
          The relation additionally is guarded by `operand_range` *iff*
          the corresponding chip enforces operand u16 bounds itself
          (`ALUBus.operandsInternal`): that's `2..4` (Bitwise) and
          `30..33, 48` (Mul family). For every other opcode the operand
          bounds come in through `ALUBus.externals` (asserted by the
          receiving `CpuChip` via its state-bus reads).

          The arithmetic relations reuse the `_pure` execute functions
          from `RV64IM.RVSail.Execution`:
          - `execute_RTYPE_pure` for 64-bit R-type ALU ops `0..9`
          - `execute_RTYPEW_pure` for W-variants `40..44`
          - `execute_MUL_pure` / `execute_MULW_pure` for MUL family
          - `execute_DIV_REM_pure` / `execute_DIVW_REMW_pure` for DIV/REM. -/
      def ALUBus.Spec
        (ALU_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 : FKB) :=
        let a := U64w.toBV #v[a_0, a_1, a_2, a_3]
        let b := U64w.toBV #v[b_0, b_1, b_2, b_3]
        let c := U64w.toBV #v[c_0, c_1, c_2, c_3]
        let result_range :=
          a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536
        let operand_range :=
          ALUBus.operandRange b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3
        result_range ∧
        match ALU_opcode with
        -- 64-bit R-type ALU (chips: AddChip, SubChip, BitwiseChip,
        -- SLLChip, ShiftRightChip, LtChip).
        | 0 => a = RV64IM.execute_RTYPE_pure b c .ADD
        | 1 => a = RV64IM.execute_RTYPE_pure b c .SUB
        -- Bitwise: operand_range in spec; chip enforces internally.
        | 2 => operand_range ∧ a = RV64IM.execute_RTYPE_pure b c .XOR
        | 3 => operand_range ∧ a = RV64IM.execute_RTYPE_pure b c .OR
        | 4 => operand_range ∧ a = RV64IM.execute_RTYPE_pure b c .AND
        | 5 => a = RV64IM.execute_RTYPE_pure b c .SLL
        | 6 => a = RV64IM.execute_RTYPE_pure b c .SRL
        | 7 => a = RV64IM.execute_RTYPE_pure b c .SRA
        | 8 => a = RV64IM.execute_RTYPE_pure b c .SLT
        | 9 => a = RV64IM.execute_RTYPE_pure b c .SLTU
        -- MUL family 64-bit (operand_range in spec; chip enforces).
        | 30 => operand_range ∧ a = RV64IM.execute_MUL_pure b c .MUL
        | 31 => operand_range ∧ a = RV64IM.execute_MUL_pure b c .MULH
        | 32 => operand_range ∧ a = RV64IM.execute_MUL_pure b c .MULHU
        | 33 => operand_range ∧ a = RV64IM.execute_MUL_pure b c .MULHSU
        -- DIV/REM (64-bit)
        | 34 => a = (RV64IM.execute_DIV_REM_pure b c .DRS).1
        | 35 => a = (RV64IM.execute_DIV_REM_pure b c .DRU).1
        | 36 => a = (RV64IM.execute_DIV_REM_pure b c .DRS).2
        | 37 => a = (RV64IM.execute_DIV_REM_pure b c .DRU).2
        -- W-variants — 32-bit RTYPEW ops, sign-extended to 64 bits.
        | 40 => a = RV64IM.execute_RTYPEW_pure (b.setWidth 32) (c.setWidth 32) .ADDW
        | 41 => a = RV64IM.execute_RTYPEW_pure (b.setWidth 32) (c.setWidth 32) .SUBW
        | 42 => a = RV64IM.execute_RTYPEW_pure (b.setWidth 32) (c.setWidth 32) .SLLW
        | 43 => a = RV64IM.execute_RTYPEW_pure (b.setWidth 32) (c.setWidth 32) .SRLW
        | 44 => a = RV64IM.execute_RTYPEW_pure (b.setWidth 32) (c.setWidth 32) .SRAW
        -- MULW (operand_range in spec; chip enforces internally).
        | 48 => operand_range ∧
                  a = RV64IM.execute_MULW_pure (b.setWidth 32) (c.setWidth 32)
        -- DIVW/REMW family (32-bit)
        | 49 => a = (RV64IM.execute_DIVW_REMW_pure (b.setWidth 32) (c.setWidth 32) .DRS).1
        | 50 => a = (RV64IM.execute_DIVW_REMW_pure (b.setWidth 32) (c.setWidth 32) .DRU).1
        | 51 => a = (RV64IM.execute_DIVW_REMW_pure (b.setWidth 32) (c.setWidth 32) .DRS).2
        | 52 => a = (RV64IM.execute_DIVW_REMW_pure (b.setWidth 32) (c.setWidth 32) .DRU).2
        | _ => True

      /-- ALU bus externals for one entry. Active when multiplicity ≠ 0:
          asserts the opcode is in the valid ALU set, and asserts
          `operand_range` for every opcode whose backing chip does *not*
          enforce u16 operand bounds internally (everything outside
          `ALUBus.operandsInternal`). -/
      def ALUBus.externals (entry : ALUBusEntry FKB) : Prop :=
        ¬(entry.multiplicity = 0) →
          ALUBus.validOpcode entry.ALU_opcode ∧
          (¬ ALUBus.operandsInternal entry.ALU_opcode →
            ALUBus.operandRange entry.b_0 entry.b_1 entry.b_2 entry.b_3
                                entry.c_0 entry.c_1 entry.c_2 entry.c_3)

      /-- ALU bus entry instance. -/
      @[simp, grind]
      instance ALUBusEntryInstance
      : BusEntry FKB (ALUBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 13,
          data := fun ⟨_, ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3⟩ =>
                    #v[ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3]

          axioms := fun _ => True

          externals := ALUBus.externals

          wf_properties :=
            fun ⟨ _, ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3 ⟩ =>
              ALUBus.Spec ALU_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3

          deserialise := ALUBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 13) (gen := 16) (ematch := 8)
      }

    end ALUBus

    section ByteBus

      /-- Byte bus entry — unchanged from RV32 (5-field payload).

          The byte chip in RV64 inherits the RV32 opcode set; the chip's
          internal representation still works on bytes since u16 limbs are
          decomposed when the bitwise / comparison gadgets are dispatched.
                                                                              -/
      structure ByteBusEntry where
        multiplicity : F
        byte_opcode : F
        x_0 : F
        x_1 : F
        x_2 : F
        x_3 : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def ByteBusEntry.deserialise
        (entry : FKB × Vector FKB 5)
      : ByteBusEntry FKB :=
        {
          multiplicity := entry.1,
          byte_opcode := entry.2[0],
          x_0 := entry.2[1],
          x_1 := entry.2[2],
          x_2 := entry.2[3],
          x_3 := entry.2[4],
        }

      /-- Byte bus pure specification.

          The RV64 byte chip reuses the RV32 opcodes 0..8 verbatim
          (AND/OR/XOR/SLL/ShrCarry/LTU/MSB/U8Range/U16Range), and adds a
          new variant:

          * `9 = BitRange` — verifies that the value `x_0` fits in `x_2`
            bits, i.e. `x_0 < 2^x_2`. The chip emits
            `add_bit_range_check(a, num_bits)` as
            `(BitRange, a, 0, num_bits, 0)`. -/
      def ByteBus.Spec (byte_opcode x_0 x_1 x_2 x_3 : FKB) :=
        match byte_opcode with
        | 0 => x_0 = x_2 &&& x_3 ∧ x_0.val < 256 ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 1 => x_0 = x_2 ||| x_3 ∧ x_0.val < 256 ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 2 => x_0 = x_2 ^^^ x_3 ∧ x_0.val < 256 ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 3 => x_0 = (x_2 <<< x_3) % 256 ∧ x_0.val < 256 ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 4 => x_0 = x_2 >>> x_3 ∧ x_1 = x_2 - (x_0 <<< x_3) ∧ x_0.val < 256 ∧ x_1.val < 256 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 5 => (x_0 = if x_2 < x_3 then 1 else 0) ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 6 => (x_0 = if x_2 < 128 then 0 else 1) ∧ x_0.val < 256 ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 7 => x_0 = 0 ∧ x_1 = 0 ∧ x_2.val < 256 ∧ x_3.val < 256
        | 8 => x_0.val < 65536 ∧ x_1 = 0 ∧ x_2 = 0 ∧ x_3 = 0
        | 9 => x_1 = 0 ∧ x_2.val ≤ 16 ∧ x_3 = 0 ∧ x_0.val < 2 ^ x_2.val
        | _ => True

      @[simp, grind]
      instance ByteBusEntryInstance
      : BusEntry FKB (ByteBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 5,
          data := fun ⟨_, byte_opcode, x_0, x_1, x_2, x_3⟩ =>
                    #v[byte_opcode, x_0, x_1, x_2, x_3]

          axioms := fun _ => True
          externals := fun _ => True

          wf_properties :=
            fun ⟨ _, byte_opcode, x_0, x_1, x_2, x_3 ⟩ =>
              ByteBus.Spec byte_opcode x_0 x_1 x_2 x_3

          deserialise := ByteBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (gen := 8)
      }

    end ByteBus

    section StateBus

      /-- State bus entry — payload size 9.

          Layout (from `Extraction/CpuChip.lean:460-461`):
          `[chunk, clk, ptr_0, ptr_1, ptr_2, x_0, x_1, x_2, x_3]`.

          Differences vs RV32 (7-field payload):

          * `ptr` widens from one field element to 3 u16 limbs (48-bit
            address space). For register accesses only `ptr_0` is non-zero.
          * The value `x_0..x_3` are u16 limbs (vs u8 limbs in RV32).        -/
      structure StateBusEntry where
        multiplicity : F
        chunk : F
        clk : F
        ptr_0 : F
        ptr_1 : F
        ptr_2 : F
        x_0 : F
        x_1 : F
        x_2 : F
        x_3 : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def StateBusEntry.deserialise
        (entry : FKB × Vector FKB 9)
      : StateBusEntry FKB :=
        {
          multiplicity := entry.1,
          chunk := entry.2[0],
          clk := entry.2[1],
          ptr_0 := entry.2[2],
          ptr_1 := entry.2[3],
          ptr_2 := entry.2[4],
          x_0 := entry.2[5],
          x_1 := entry.2[6],
          x_2 := entry.2[7],
          x_3 := entry.2[8],
        }

      @[simp, grind]
      instance StateBusEntryInstance
      : BusEntry FKB (StateBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 9,
          data := fun ⟨_, chunk, clk, ptr_0, ptr_1, ptr_2, x_0, x_1, x_2, x_3⟩ =>
                    #v[chunk, clk, ptr_0, ptr_1, ptr_2, x_0, x_1, x_2, x_3]

          axioms := fun _ => True
          externals := fun _ => True

          -- u16 range on each value limb
          wf_properties :=
            fun ⟨ _, _, _, _, _, _, x_0, x_1, x_2, x_3 ⟩ =>
              x_0.val < 65536 ∧ x_1.val < 65536 ∧ x_2.val < 65536 ∧ x_3.val < 65536

          deserialise := StateBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (gen := 12) (ematch := 6)
      }

    end StateBus

    section MemoryBus

      /-- Memory bus entry — payload size 25.

          Layout (from `Extraction/CpuChip.lean:470`):
          `[mem_opcode, a[0..3], b[0..3], c[0..3], a_is_0,
            is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld,
            is_sb, is_sh, is_sw, is_sd]`.

          Differences vs RV32 (22-field payload): 3 new memory selectors
          (`is_lwu, is_ld, is_sd`) for the RV64-only memory ops; operand
          limbs widen from u8 to u16.                                        -/
      structure MemoryBusEntry where
        multiplicity : F
        mem_opcode : F
        a_0 : F
        a_1 : F
        a_2 : F
        a_3 : F
        b_0 : F
        b_1 : F
        b_2 : F
        b_3 : F
        c_0 : F
        c_1 : F
        c_2 : F
        c_3 : F
        a_is_0 : F
        is_lb : F
        is_lbu : F
        is_lh : F
        is_lhu : F
        is_lw : F
        is_lwu : F
        is_ld : F
        is_sb : F
        is_sh : F
        is_sw : F
        is_sd : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def MemoryBusEntry.deserialise
        (entry : FKB × Vector FKB 25)
      : MemoryBusEntry FKB :=
        {
          multiplicity := entry.1,
          mem_opcode := entry.2[0],
          a_0 := entry.2[1],
          a_1 := entry.2[2],
          a_2 := entry.2[3],
          a_3 := entry.2[4],
          b_0 := entry.2[5],
          b_1 := entry.2[6],
          b_2 := entry.2[7],
          b_3 := entry.2[8],
          c_0 := entry.2[9],
          c_1 := entry.2[10],
          c_2 := entry.2[11],
          c_3 := entry.2[12],
          a_is_0 := entry.2[13],
          is_lb := entry.2[14],
          is_lbu := entry.2[15],
          is_lh := entry.2[16],
          is_lhu := entry.2[17],
          is_lw := entry.2[18],
          is_lwu := entry.2[19],
          is_ld := entry.2[20],
          is_sb := entry.2[21],
          is_sh := entry.2[22],
          is_sw := entry.2[23],
          is_sd := entry.2[24],
        }

      /-- Memory bus pure specification.

          The chip lays out the loaded value across the four u16 limbs so
          that `a := U64w.toBV #v[a_0, a_1, a_2, a_3]` is already the
          fully sign- or zero-extended 64-bit result — see
          `vm/src/chips/chips/riscv_memory/read_write/constraints.rs`
          (e.g. for LB it builds
           `Word([byte + 0xFF00·msb, 0xFFFF·msb, 0xFFFF·msb, 0xFFFF·msb])`,
           and analogously for LH/LW; the unsigned variants use `0` in the
           upper limbs). The bus spec therefore equates `a` to the
           appropriate extension of its own truncation.

          RV64 deltas vs RV32:
          * Address `b + c` lives in the 48-bit Pico address space
            (`< Pico_address_space_size_64 = 2^48`).
          * `LWU` (`45`) is zero-extended `LW`; `LD` (`46`) / `SD` (`47`)
            are 8-byte ops with no extension.
          * Alignment: 2-byte (LH/LHU/SH), 4-byte (LW/LWU/SW), 8-byte (LD/SD).
                                                                              -/
      def MemoryBus.Spec
        (mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 a_is_0 : FKB) : Prop :=
        let a := U64w.toBV #v[a_0, a_1, a_2, a_3]
        let b := U64w.toBV #v[b_0, b_1, b_2, b_3]
        let c := U64w.toBV #v[c_0, c_1, c_2, c_3]
        let addr := (b + c).toNat
        -- For load ops the result has u16-limbed range; stores leave it
        -- unconstrained on the bus side.
        ((mem_opcode.val ≤ 14 ∨ mem_opcode.val = 45 ∨ mem_opcode.val = 46) →
            a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536) ∧
        -- Address must lie in the user-accessible range [2^16, 2^48):
        -- the low 64 KiB are reserved (Pico's stack-guard region —
        -- enforced by MemoryReadWriteChip's `constraint_1`).
        65536 ≤ addr ∧ addr < Pico_address_space_size_64 ∧
        -- Alignment requirements
        (mem_opcode = 11 ∨ mem_opcode = 14 ∨ mem_opcode = 16 → 2 ∣ addr) ∧
        (mem_opcode = 12 ∨ mem_opcode = 17 ∨ mem_opcode = 45 → 4 ∣ addr) ∧
        (mem_opcode = 46 ∨ mem_opcode = 47 → 8 ∣ addr) ∧
        -- Load result equations: gated on `a_is_0 = 0` (rd ≠ x0) since the
        -- chip leaves `a_*` unconstrained on x0 loads (zeroing is enforced
        -- CPU-side via c16-c19 and exposed through the externals below).
        (mem_opcode = 10 → a_is_0 = 0 → a = BitVec.signExtend 64 (a.truncate 8)) ∧   -- LB
        (mem_opcode = 11 → a_is_0 = 0 → a = BitVec.signExtend 64 (a.truncate 16)) ∧  -- LH
        (mem_opcode = 12 → a_is_0 = 0 → a = BitVec.signExtend 64 (a.truncate 32)) ∧  -- LW
        (mem_opcode = 13 → a_is_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 8)) ∧   -- LBU
        (mem_opcode = 14 → a_is_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 16)) ∧  -- LHU
        (mem_opcode = 45 → a_is_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 32))    -- LWU
        -- LD (46) needs no extension; SB/SH/SW/SD (15-17, 47) don't
        -- constrain `a` on the bus.

      @[simp, grind]
      instance MemoryBusEntryInstance
      : BusEntry FKB (MemoryBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 25,
          data := fun ⟨_, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd⟩ =>
                    #v[mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd]

          axioms := fun _ => True

          -- Opcode is constrained to the RV64 mem-op set; operands are
          -- range-checked by the chip externally; one selector is asserted
          -- per opcode (load selectors for 10..14, 45, 46; store selectors
          -- for 15..17, 47).
          externals := fun ⟨multiplicity, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd⟩ =>
            ¬(multiplicity = 0) →
              (mem_opcode ∈ Finset.Icc 10 17 ∨ mem_opcode ∈ Finset.Icc 45 47) ∧
              b_0.val < 65536 ∧ b_1.val < 65536 ∧ b_2.val < 65536 ∧ b_3.val < 65536 ∧
              c_0.val < 65536 ∧ c_1.val < 65536 ∧ c_2.val < 65536 ∧ c_3.val < 65536 ∧
              (mem_opcode = 10 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 11 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 12 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 13 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 14 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 45 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 46 → (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0) ∧
                (¬ a_is_0 = 0 → a_0 = 0 ∧ a_1 = 0 ∧ a_2 = 0 ∧ a_3 = 0)) ∧
              (mem_opcode = 15 → a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536 ∧
                (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0)) ∧
              (mem_opcode = 16 → a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536 ∧
                (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0)) ∧
              (mem_opcode = 17 → a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536 ∧
                (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0)) ∧
              (mem_opcode = 47 → a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536 ∧
                (is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld, is_sb, is_sh, is_sw, is_sd) = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1))

          wf_properties := fun ⟨_, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, _, _, _, _, _, _, _, _, _, _, _⟩ =>
            MemoryBus.Spec mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 a_is_0

          deserialise := MemoryBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 28) (gen := 32) (ematch := 16)
      }

    end MemoryBus

  end Buses

  section ChipRows

    structure BusRow where
      Program : List (ProgramBusEntry FKB)
      ALU : List (ALUBusEntry FKB)
      Byte : List (ByteBusEntry FKB)
      State : List (StateBusEntry FKB)
      Memory : List (MemoryBusEntry FKB)

    /-- Filter a `BusRow` to keep only entries with negative multiplicity (= -1).
        These are the "read" entries: the chip assumes them and sends them
        to other chips for verification via the bus argument. -/
    def BusRow.readEntries (br : BusRow) : BusRow :=
      { Program := br.Program.filter (fun e => e.multiplicity = -1)
        ALU     := br.ALU.filter     (fun e => e.multiplicity = -1)
        Byte    := br.Byte.filter    (fun e => e.multiplicity = -1)
        State   := br.State.filter   (fun e => e.multiplicity = -1)
        Memory  := br.Memory.filter  (fun e => e.multiplicity = -1) }

    /-- Concatenate two `BusRow`s pointwise on each of the five lists. -/
    def BusRow.append (r1 r2 : BusRow) : BusRow :=
      { Program := r1.Program ++ r2.Program
        ALU     := r1.ALU     ++ r2.ALU
        Byte    := r1.Byte    ++ r2.Byte
        State   := r1.State   ++ r2.State
        Memory  := r1.Memory  ++ r2.Memory }

    instance : Append BusRow := ⟨BusRow.append⟩

    lemma BusRow.append_eq (r1 r2 : BusRow) :
      r1 ++ r2 =
        { Program := r1.Program ++ r2.Program
          ALU     := r1.ALU     ++ r2.ALU
          Byte    := r1.Byte    ++ r2.Byte
          State   := r1.State   ++ r2.State
          Memory  := r1.Memory  ++ r2.Memory } := rfl

    @[simp] lemma BusRow.append_Program (r1 r2 : BusRow) :
      (r1 ++ r2).Program = r1.Program ++ r2.Program := rfl
    @[simp] lemma BusRow.append_ALU (r1 r2 : BusRow) :
      (r1 ++ r2).ALU = r1.ALU ++ r2.ALU := rfl
    @[simp] lemma BusRow.append_Byte (r1 r2 : BusRow) :
      (r1 ++ r2).Byte = r1.Byte ++ r2.Byte := rfl
    @[simp] lemma BusRow.append_State (r1 r2 : BusRow) :
      (r1 ++ r2).State = r1.State ++ r2.State := rfl
    @[simp] lemma BusRow.append_Memory (r1 r2 : BusRow) :
      (r1 ++ r2).Memory = r1.Memory ++ r2.Memory := rfl

    def bus_row_axioms (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.axioms FKB) ++
         row.ALU.map (BusEntry.axioms FKB) ++
         row.Byte.map (BusEntry.axioms FKB) ++
         row.State.map (BusEntry.axioms FKB) ++
         row.Memory.map (BusEntry.axioms FKB))

    def bus_row_ext_asm (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.ext_assume FKB) ++
         row.ALU.map (BusEntry.ext_assume FKB) ++
         row.Byte.map (BusEntry.ext_assume FKB) ++
         row.State.map (BusEntry.ext_assume FKB) ++
         row.Memory.map (BusEntry.ext_assume FKB))

    def bus_row_ext_asrt (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.ext_assert FKB) ++
         row.ALU.map (BusEntry.ext_assert FKB) ++
         row.Byte.map (BusEntry.ext_assert FKB) ++
         row.State.map (BusEntry.ext_assert FKB) ++
         row.Memory.map (BusEntry.ext_assert FKB))

    def bus_row_wf_asm (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.wf_assume FKB) ++
         row.ALU.map (BusEntry.wf_assume FKB) ++
         row.Byte.map (BusEntry.wf_assume FKB) ++
         row.State.map (BusEntry.wf_assume FKB) ++
         row.Memory.map (BusEntry.wf_assume FKB))

    def bus_row_wf_asrt (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.wf_assert FKB) ++
         row.ALU.map (BusEntry.wf_assert FKB) ++
         row.Byte.map (BusEntry.wf_assert FKB) ++
         row.State.map (BusEntry.wf_assert FKB) ++
         row.Memory.map (BusEntry.wf_assert FKB))

    -- =====================================================================
    -- Decomposition over `++` on `BusRow`. Each of the four bus-side
    -- assumption/assertion predicates distributes pointwise over
    -- concatenation. Lets a chip that embeds a gadget reduce its own
    -- bus-side hypothesis to the gadget's contribution + chip extras.
    -- =====================================================================

    @[simp]
    lemma bus_row_ext_asm_append (b1 b2 : BusRow) :
      bus_row_ext_asm (b1 ++ b2) ↔ bus_row_ext_asm b1 ∧ bus_row_ext_asm b2
    := by
      simp only [bus_row_ext_asm, BusRow.append_eq, List.map_append,
                 List.forall_append]
      tauto

    @[simp]
    lemma bus_row_ext_asrt_append (b1 b2 : BusRow) :
      bus_row_ext_asrt (b1 ++ b2) ↔ bus_row_ext_asrt b1 ∧ bus_row_ext_asrt b2
    := by
      simp only [bus_row_ext_asrt, BusRow.append_eq, List.map_append,
                 List.forall_append]
      tauto

    @[simp]
    lemma bus_row_wf_asm_append (b1 b2 : BusRow) :
      bus_row_wf_asm (b1 ++ b2) ↔ bus_row_wf_asm b1 ∧ bus_row_wf_asm b2
    := by
      simp only [bus_row_wf_asm, BusRow.append_eq, List.map_append,
                 List.forall_append]
      tauto

    @[simp]
    lemma bus_row_wf_asrt_append (b1 b2 : BusRow) :
      bus_row_wf_asrt (b1 ++ b2) ↔ bus_row_wf_asrt b1 ∧ bus_row_wf_asrt b2
    := by
      simp only [bus_row_wf_asrt, BusRow.append_eq, List.map_append,
                 List.forall_append]
      tauto

    /-- Deserialise a raw bus row (list of (multiplicity, [bus_id, ...data])
        tuples) into a typed `BusRow`. Bus tag layout matches RV32 exactly;
        the per-bus data lengths change to (State 9, Program 43, ALU 13,
        Byte 5, Memory 25). State and Memory both use tag `0` and are
        disambiguated by payload length. -/
    def deserialise_bus_row (row : List (FKB × List FKB)) : BusRow :=
      let initial_bus_row : BusRow :=
        { Program := [], ALU := [], Byte := [], State := [], Memory := [] }
      List.foldl
        (fun result ⟨ multiplicity, entry ⟩ =>
          let bus_id := entry.head!
          let entry_data := entry.tail!
          match bus_id with
          | 0 =>
              if _ : entry_data.length = 9 then
                let entry_data_vector : Vector FKB 9 := ⟨ entry_data.toArray, by simp; omega ⟩
                let bus_entry := StateBusEntry.deserialise (multiplicity, entry_data_vector)
                { result with State := result.State ++ [ bus_entry ] }
              else (
                if _ : entry_data.length = 25 then
                  let entry_data_vector : Vector FKB 25 := ⟨ entry_data.toArray, by simp; omega ⟩
                  let bus_entry := MemoryBusEntry.deserialise (multiplicity, entry_data_vector)
                  { result with Memory := result.Memory ++ [ bus_entry ] }
                else result
              )
          | 1 =>
            if _ : entry_data.length = 43 then
              let entry_data_vector : Vector FKB 43 := ⟨ entry_data.toArray, by simp; omega ⟩
              let bus_entry := ProgramBusEntry.deserialise (multiplicity, entry_data_vector)
              { result with Program := result.Program ++ [ bus_entry ] }
            else result
          | 3 =>
              if _ : entry_data.length = 13 then
                let entry_data_vector : Vector FKB 13 := ⟨ entry_data.toArray, by simp; omega ⟩
                let bus_entry := ALUBusEntry.deserialise (multiplicity, entry_data_vector)
                { result with ALU := result.ALU ++ [ bus_entry ] }
              else result
          | 4 =>
            if _ : entry_data.length = 5 then
              let entry_data_vector : Vector FKB 5 := ⟨ entry_data.toArray, by simp; omega ⟩
              let bus_entry := ByteBusEntry.deserialise (multiplicity, entry_data_vector)
              { result with Byte := result.Byte ++ [ bus_entry ] }
            else result
          | _ => result
        )
        initial_bus_row
        row

  end ChipRows

end RV64IM_Interactions
