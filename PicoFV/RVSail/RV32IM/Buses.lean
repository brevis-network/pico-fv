import PicoFV.Fundamentals.Interaction

import PicoFV.RVSail.RV32IM.Execution

set_option maxHeartbeats 1_000_000_000

namespace RV32IM_Interactions

  open Interaction

  section Buses

    variable
      (F : Type)
      [Field F]

    section ProgramBus

      /-- Program bus entry -/
      structure ProgramBusEntry where
        multiplicity : F
        pc : F
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
        is_sb : F
        is_sh : F
        is_sw : F
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
        (entry : FKB × Vector FKB 38)
      : ProgramBusEntry FKB :=
        {
          multiplicity := entry.1,
          pc := entry.2[0],
          opcode := entry.2[1],
          opcode' := entry.2[2],
          a_0 := entry.2[3],
          a_1 := entry.2[4],
          a_2 := entry.2[5],
          a_3 := entry.2[6],
          b_0 := entry.2[7],
          b_1 := entry.2[8],
          b_2 := entry.2[9],
          b_3 := entry.2[10],
          c_0 := entry.2[11],
          c_1 := entry.2[12],
          c_2 := entry.2[13],
          c_3 := entry.2[14],
          a_is_0 := entry.2[15],
          imm_b := entry.2[16],
          imm_c := entry.2[17],
          is_alu := entry.2[18],
          is_ecall := entry.2[19],
          is_lb := entry.2[20],
          is_lbu := entry.2[21],
          is_lh := entry.2[22],
          is_lhu := entry.2[23],
          is_lw := entry.2[24],
          is_sb := entry.2[25],
          is_sh := entry.2[26],
          is_sw := entry.2[27],
          is_beq := entry.2[28],
          is_bne := entry.2[29],
          is_blt := entry.2[30],
          is_bge := entry.2[31],
          is_bltu := entry.2[32],
          is_bgeu := entry.2[33],
          is_jalr := entry.2[34],
          is_jal := entry.2[35],
          is_auipc := entry.2[36],
          is_unimpl := entry.2[37],
        }

      def ProgramBusEntry.operand_properties (entry : ProgramBusEntry FKB) : Prop :=
        ∃ instruction data props,
          (.some ⟨ data, props ⟩ = Transpiler.transpile_op instruction entry.multiplicity entry.pc) ∧
          (entry = ProgramBusEntry.deserialise data) ∧
          props

      lemma ProgramBusEntry.inversion_opcode_bounds
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ = Transpiler.transpile_op instr entry.multiplicity entry.pc)
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        entry.opcode.val ≤ 37 ∧ entry.opcode.val ≠ 26 ∧ entry.opcode.val ≠ 29
      := by
        have h_op_eq : entry.opcode = data.2[1]
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
          Transpiler.opcode_of_uop
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
          grind

      lemma ProgramBusEntry.operand_properties_inversion
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ = Transpiler.transpile_op instr entry.multiplicity entry.pc)
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
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
        (entry.opcode = 10 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 1)) ∧
        (entry.opcode = 11 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 2)) ∧
        (entry.opcode = 12 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 4)) ∧
        (entry.opcode = 13 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 1)) ∧
        (entry.opcode = 14 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 2)) ∧
        (entry.opcode = 15 → ∃ imm rs1 rd, instr = .STORE (imm, rs1, rd, 1)) ∧
        (entry.opcode = 16 → ∃ imm rs1 rd, instr = .STORE (imm, rs1, rd, 2)) ∧
        (entry.opcode = 17 → ∃ imm rs1 rd, instr = .STORE (imm, rs1, rd, 4)) ∧
        (entry.opcode = 18 → ∃ imm rs1 rd, instr = .BTYPE (imm, rs1, rd, .BEQ)) ∧
        (entry.opcode = 19 → ∃ imm rs1 rd, instr = .BTYPE (imm, rs1, rd, .BNE)) ∧
        (entry.opcode = 20 → ∃ imm rs1 rd, instr = .BTYPE (imm, rs1, rd, .BLT)) ∧
        (entry.opcode = 21 → ∃ imm rs1 rd, instr = .BTYPE (imm, rs1, rd, .BGE)) ∧
        (entry.opcode = 22 → ∃ imm rs1 rd, instr = .BTYPE (imm, rs1, rd, .BLTU)) ∧
        (entry.opcode = 23 → ∃ imm rs1 rd, instr = .BTYPE (imm, rs1, rd, .BGEU)) ∧
        (entry.opcode = 24 → ∃ imm rd, instr = .JAL (imm, rd)) ∧
        (entry.opcode = 25 → ∃ imm rd rs1, instr = .JALR (imm, rd, rs1)) ∧
        (entry.opcode = 27 → ∃ imm rd, instr = .UTYPE (imm, rd, .AUIPC)) ∧
        (entry.opcode = 28 → instr = .ECALL ()) ∧
        (entry.opcode = 30 → ∃ rs2 rs1 rd sl sr, instr = .MUL (rs2, rs1, rd, { result_part := .Low, signed_rs1 := sl, signed_rs2 := sr })) ∧
        (entry.opcode = 31 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed })) ∧
        (entry.opcode = 32 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) ∧
        (entry.opcode = 33 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })) ∧
        (entry.opcode = 34 → ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, false)) ∧
        (entry.opcode = 35 → ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, true)) ∧
        (entry.opcode = 36 → ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, false)) ∧
        (entry.opcode = 37 → ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, true))
      := by
        have ⟨ h_op_eq, h_imm_b_eq, h_imm_c_eq ⟩ : entry.opcode = data.2[1] ∧ entry.imm_b = data.2[16] ∧ entry.imm_c = data.2[17]
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
          Transpiler.opcode_of_uop
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

      lemma ProgramBusEntry.inversion_opcode_selectors
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ = Transpiler.transpile_op instr entry.multiplicity entry.pc)
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        (entry.opcode =  0 → ( entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  1 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  2 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  3 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  4 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  5 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  6 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  7 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  8 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode =  9 → ( entry.imm_b, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 10 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 11 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 12 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 13 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 14 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 15 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 16 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 17 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 18 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 19 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 20 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 21 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 22 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 23 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 )) ∧
        (entry.opcode = 24 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 )) ∧
        (entry.opcode = 25 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 )) ∧
        (entry.opcode = 27 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 )) ∧
        (entry.opcode = 28 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 30 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 31 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 32 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 33 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 34 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 35 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 36 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
        (entry.opcode = 37 → ( entry.imm_b, entry.imm_c, entry.is_alu, entry.is_ecall, entry.is_lb, entry.is_lbu, entry.is_lh, entry.is_lhu, entry.is_lw, entry.is_sb, entry.is_sh, entry.is_sw, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal, entry.is_auipc, entry.is_unimpl ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ))
      := by
        simp [
          Transpiler.transpile_op,
          Transpiler.opcode_of_rop,
          Transpiler.opcode_of_iop,
          Transpiler.opcode_of_sop,
          Transpiler.opcode_of_bop,
          Transpiler.opcode_of_uop
        ] at h_trans
        split at h_trans <;> try simp at h_trans
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
          grind
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
          grind
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; simp
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp

      lemma ProgramBusEntry.ub_imm
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ = Transpiler.transpile_op instr entry.multiplicity entry.pc)
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        (entry.imm_b = 1 → entry.b_0 < 256 ∧ entry.b_1 < 256 ∧ entry.b_2 < 256 ∧ entry.b_3 < 256) ∧
        (entry.imm_c = 1 → entry.c_0 < 256 ∧ entry.c_1 < 256 ∧ entry.c_2 < 256 ∧ entry.c_3 < 256)
      := by
        simp [
          Transpiler.transpile_op,
          Transpiler.opcode_of_rop,
          Transpiler.opcode_of_iop,
          Transpiler.opcode_of_sop,
          Transpiler.opcode_of_bop,
          Transpiler.opcode_of_uop
        ] at h_trans
        split at h_trans <;> try simp at h_trans
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp [Transpiler.imm_to_KB_bytes]
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; simp
        . split at h_trans <;> simp at h_trans
          simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp
        . simp [h_trans.1, deserialise] at h_deser
          rw [h_deser]; clear *-; (try split) <;> simp

      /-- Program bus entry instance -/
      @[simp, grind]
      instance ProgramBusEntryInstance
      : BusEntry FKB (ProgramBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 38,
          data := fun ⟨_, pc, opcode, opcode', a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, imm_b, imm_c, is_alu, is_ecall, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, is_auipc, is_unimpl⟩ =>
                    #v[pc, opcode, opcode', a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, imm_b, imm_c, is_alu, is_ecall, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, is_auipc, is_unimpl]

          -- Program counter is bounded and aligned axiomatically
          axioms := fun entry =>
            (¬ entry.multiplicity = 0) → entry.pc < 2 ^ 30 ∧ entry.pc % 4 = 0

          -- No chip-external constraints
          externals := fun _ => True

          -- Well formedness entirely derived from the fact that the entries come from the transpiler
          wf_properties := ProgramBusEntry.operand_properties

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          ext_assume_cond := fun entry => entry.1 = 1,
          ext_assert_cond := fun entry => entry.1 = -1,

          deserialise := ProgramBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 64) (gen := 64) (ematch := 32) (ringSteps := 16384)
      }

    end ProgramBus

    section ALUBus

      /-- ALU bus entry -/
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

      def ALUBus.Spec (ALU_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 : FKB) :=
        let result_range := a_0 < 256 ∧ a_1 < 256 ∧ a_2 < 256 ∧ a_3 < 256
        let operand_range := b_0 < 256 ∧ b_1 < 256 ∧ b_2 < 256 ∧ b_3 < 256 ∧ c_0 < 256 ∧ c_1 < 256 ∧ c_2 < 256 ∧ c_3 < 256
        match ALU_opcode with
        | 0 => result_range ∧ operand_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] + U32.toBV #v[c_0, c_1, c_2, c_3]
        | 1 => result_range ∧ operand_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] - U32.toBV #v[c_0, c_1, c_2, c_3]
        | 2 => result_range ∧ operand_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] ^^^ U32.toBV #v[c_0, c_1, c_2, c_3]
        | 3 => result_range ∧ operand_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] ||| U32.toBV #v[c_0, c_1, c_2, c_3]
        | 4 => result_range ∧ operand_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] &&& U32.toBV #v[c_0, c_1, c_2, c_3]
        | 5 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] <<< (U32.toNat #v[c_0, c_1, c_2, c_3] % 32)
        | 6 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] >>> (U32.toNat #v[c_0, c_1, c_2, c_3] % 32)
        | 7 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = (U32.toBV #v[b_0, b_1, b_2, b_3]).sshiftRight (U32.toNat #v[c_0, c_1, c_2, c_3] % 32)
        | 8 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = if (U32.toBV #v[b_0, b_1, b_2, b_3]).toInt < (U32.toBV #v[c_0, c_1, c_2, c_3]).toInt then 1#32 else 0#32
        | 9 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = if (U32.toBV #v[b_0, b_1, b_2, b_3]).toNat < (U32.toBV #v[c_0, c_1, c_2, c_3]).toNat then 1#32 else 0#32
        | 30 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MUL
        | 31 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MULH
        | 32 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MULHU
        | 33 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MULHSU
        | 34 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRS).1
        | 35 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRU).1
        | 36 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRS).2
        | 37 => result_range ∧ U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRU).2
        | _ => True

      /-- ALU bus entry instance -/
      @[simp, grind]
      instance ALUBusEntryInstance
      : BusEntry FKB (ALUBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 13,
          data := fun ⟨_, ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3⟩ =>
                    #v[ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3]

          -- No axioms
          axioms := fun _ => True

          -- Operands are range-checked externally to the chip
          externals := fun entry =>
            ¬(entry.multiplicity = 0) →
              (entry.ALU_opcode ∈ Finset.Icc 0 9 ∨ entry.ALU_opcode ∈ Finset.Icc 30 37) ∧
              (entry.ALU_opcode > 4 →
                 entry.b_0 < 256 ∧ entry.b_1 < 256 ∧ entry.b_2 < 256 ∧ entry.b_3 < 256 ∧
                 entry.c_0 < 256 ∧ entry.c_1 < 256 ∧ entry.c_2 < 256 ∧ entry.c_3 < 256)

          -- Well formedness derived from byte lookup table construction
          wf_properties :=
            fun ⟨ _, ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3 ⟩ =>
              ALUBus.Spec ALU_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          ext_assume_cond := fun entry => entry.1 = 1,
          ext_assert_cond := fun entry => entry.1 = -1,

          deserialise := ALUBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 13) (gen := 16) (ematch := 8)
      }

    end ALUBus

    section ByteBus

      /-- Byte bus entry -/
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

      def ByteBus.Spec (byte_opcode x_0 x_1 x_2 x_3 : FKB) :=
        match byte_opcode with
        | 0 => x_0 = x_2 &&& x_3 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 1 => x_0 = x_2 ||| x_3 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 2 => x_0 = x_2 ^^^ x_3 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 3 => x_0 = (x_2 <<< x_3) % 256 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 4 => x_0 = x_2 >>> x_3 ∧ x_1 = x_2 - (x_0 <<< x_3) ∧ x_0 < 256 ∧ x_1 < 256 ∧ x_2 < 256 ∧ x_3 < 256
        | 5 => (x_0 = if x_2 < x_3 then 1 else 0) ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 6 => (x_0 = if x_2 < 128 then 0 else 1) ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 7 => x_0 = 0 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 8 => x_0 < 65536 ∧ x_1 = 0 ∧ x_2 = 0 ∧ x_3 = 0
        | _ => True

      /-- Byte bus entry instance -/
      @[simp, grind]
      instance ByteBusEntryInstance
      : BusEntry FKB (ByteBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 5,
          data := fun ⟨_, byte_opcode, x_0, x_1, x_2, x_3⟩ =>
                    #v[byte_opcode, x_0, x_1, x_2, x_3]

          -- No axioms
          axioms := fun _ => True

          -- No externals
          externals := fun _ => True

          -- Well formedness derived from byte lookup table construction
          wf_properties :=
            fun ⟨ _, byte_opcode, x_0, x_1, x_2, x_3 ⟩ =>
              ByteBus.Spec byte_opcode x_0 x_1 x_2 x_3

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          ext_assume_cond := fun entry => entry.1 = 1,
          ext_assert_cond := fun entry => entry.1 = -1,

          deserialise := ByteBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (gen := 8)
      }

    end ByteBus

    section StateBus

      /-- Byte bus entry -/
      structure StateBusEntry where
        multiplicity : F
        chunk : F
        clk : F
        ptr : F
        x_0 : F
        x_1 : F
        x_2 : F
        x_3 : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def StateBusEntry.deserialise
        (entry : FKB × Vector FKB 7)
      : StateBusEntry FKB :=
        {
          multiplicity := entry.1,
          chunk := entry.2[0],
          clk := entry.2[1],
          ptr := entry.2[2],
          x_0 := entry.2[3],
          x_1 := entry.2[4],
          x_2 := entry.2[5],
          x_3 := entry.2[6],
        }

      /-- Register bus entry instance -/
      @[simp, grind]
      instance StateBusEntryInstance
      : BusEntry FKB (StateBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 7,
          data := fun ⟨_, chunk, clk, ptr, x_0, x_1, x_2, x_3⟩ =>
                    #v[chunk, clk, ptr, x_0, x_1, x_2, x_3]

          -- No axioms
          axioms := fun _ => True

          -- No externals
          externals := fun _ => True

          -- Well formedness
          wf_properties :=
            fun ⟨ _, chunk, clk, ptr, x_0, x_1, x_2, x_3 ⟩ =>
              x_0 < 256 ∧ x_1 < 256 ∧ x_2 < 256 ∧ x_3 < 256

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          ext_assume_cond := fun entry => entry.1 = 1,
          ext_assert_cond := fun entry => entry.1 = -1,

          deserialise := StateBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (gen := 10)
      }

    end StateBus

    section MemoryBus

      /-- Memory summary bus entry -/
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
        is_sb : F
        is_sh : F
        is_sw : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def MemoryBusEntry.deserialise
        (entry : FKB × Vector FKB 22)
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
          a_is_0 := entry.2[13]
          is_lb := entry.2[14],
          is_lbu := entry.2[15],
          is_lh := entry.2[16],
          is_lhu := entry.2[17],
          is_lw := entry.2[18],
          is_sb := entry.2[19],
          is_sh := entry.2[20],
          is_sw := entry.2[21],
        }

      def MemoryBus.Spec (mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 a_is_0 _is_lb _is_lbu is_lh is_lhu is_lw _is_sb is_sh is_sw : FKB) : Prop :=
        let width :=
          if is_lw = 1 ∨ is_sw = 1 then 4
            else if is_lh = 1 ∨ is_lhu = 1 ∨ is_sh = 1
              then 2 else 1
        (a_is_0 = 0 → a_0 < 256 ∧ a_1 < 256 ∧ a_2 < 256 ∧ a_3 < 256) ∧
        (U32.toBV #v[b_0, b_1, b_2, b_3] + U32.toBV #v[c_0, c_1, c_2, c_3]).toNat + width < Pico_address_space_size_32 ∧
        (mem_opcode = 10 → a_is_0 = 0 → U32.toBV #v[a_0, a_1, a_2, a_3] = BitVec.extend (BitVec.ofNat 8 a_0.val) 32 true) ∧
        (mem_opcode = 11 → a_is_0 = 0 → U32.toBV #v[a_0, a_1, a_2, a_3] = BitVec.extend ((BitVec.ofNat 8 a_1.val) ++ (BitVec.ofNat 8 a_0.val)) 32 true) ∧
        (mem_opcode = 13 → a_is_0 = 0 → U32.toBV #v[a_0, a_1, a_2, a_3] = BitVec.extend (BitVec.ofNat 8 a_0.val) 32 false) ∧
        (mem_opcode = 14 → a_is_0 = 0 → U32.toBV #v[a_0, a_1, a_2, a_3] = BitVec.extend ((BitVec.ofNat 8 a_1.val) ++ (BitVec.ofNat 8 a_0.val)) 32 false)

      /-- Program bus entry instance -/
      @[simp, grind]
      instance MemoryBusEntryInstance
      : BusEntry FKB (MemoryBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 22,
          data := fun ⟨_, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw⟩ =>
                    #v[mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw]

          -- No axioms
          axioms := fun _ => True

          -- Opcode and selectors are constrainted externally
          externals := fun ⟨multiplicity, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw⟩ =>
            ¬(multiplicity = 0) →
              mem_opcode ∈ Finset.Icc 10 17 ∧
              b_0 < 256 ∧ b_1 < 256 ∧ b_2 < 256 ∧ b_3 < 256 ∧
              c_0 < 256 ∧ c_1 < 256 ∧ c_2 < 256 ∧ c_3 < 256 ∧
              (mem_opcode = 10 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 1, 0, 0, 0, 0, 0, 0, 0 )) ∧
              (mem_opcode = 11 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 0, 1, 0, 0, 0, 0, 0 )) ∧
              (mem_opcode = 12 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 0, 0, 0, 1, 0, 0, 0 )) ∧
              (mem_opcode = 13 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 1, 0, 0, 0, 0, 0, 0 )) ∧
              (mem_opcode = 14 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 0, 0, 1, 0, 0, 0, 0 )) ∧
              (mem_opcode = 15 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 0, 0, 0, 0, 1, 0, 0 )) ∧
              (mem_opcode = 16 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 0, 0, 0, 0, 0, 1, 0 )) ∧
              (mem_opcode = 17 → ( is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw ) = ( 0, 0, 0, 0, 0, 0, 0, 1 ))

          -- Well formedness entirely derived from the fact that the entries come from the transpiler
          wf_properties := fun ⟨_, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw⟩ =>
            MemoryBus.Spec mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 a_is_0 is_lb is_lbu is_lh is_lhu is_lw is_sb is_sh is_sw

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          ext_assume_cond := fun entry => entry.1 = 1,
          ext_assert_cond := fun entry => entry.1 = -1,

          deserialise := MemoryBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (splits := 24) (gen := 28) (ematch := 12)
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

    def deserialise_bus_row (row : List (FKB × List FKB)) : BusRow :=
      let initial_bus_row : BusRow := { Program := [], ALU := [], Byte := [], State := [], Memory := [] }
      List.foldl
        (fun result ⟨ multiplicity, entry ⟩ =>
          let bus_id := entry.head!
          let entry_data := entry.tail!
          match bus_id with
          | 0 =>
              if _ : entry_data.length = 7 then
                let entry_data_vector : Vector FKB 7 := ⟨ entry_data.toArray, by simp; omega ⟩
                let bus_entry := StateBusEntry.deserialise (multiplicity, entry_data_vector)
                { result with State := result.State ++ [ bus_entry ] }
              else (
                if _ : entry_data.length = 22 then
                  let entry_data_vector : Vector FKB 22 := ⟨ entry_data.toArray, by simp; omega ⟩
                  let bus_entry := MemoryBusEntry.deserialise (multiplicity, entry_data_vector)
                  { result with Memory := result.Memory ++ [ bus_entry ] }
                else result
              )
          | 1 =>
            if _ : entry_data.length = 38 then
              let entry_data_vector : Vector FKB 38 := ⟨ entry_data.toArray, by simp; omega ⟩
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

end RV32IM_Interactions
