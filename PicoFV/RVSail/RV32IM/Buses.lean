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

      lemma ProgramBusEntry.operand_properties_inversion
        { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ = Transpiler.transpile_op instr entry.multiplicity entry.pc)
        (h_deser : entry = ProgramBusEntry.deserialise data)
      :
        (entry.opcode = 0 →
          (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .ADD)) ∨
          (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ADDI))) ∧
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
          (entry.imm_b = 0 ∧ entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SLLI)) ∨
          (entry.imm_b = 1 ∧ entry.imm_c = 1 ∧ ∃ imm rd, instr = .UTYPE (imm, rd, .LUI))) ∧
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

      /-- Program bus entry instance -/
      @[simp, grind]
      instance ProgramBusEntryInstance
      : BusEntry FKB (ProgramBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 38,
          data := fun ⟨_, pc, opcode, opcode', a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, imm_b, imm_c, is_alu, is_ecall, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, is_auipc, is_unimpl⟩ =>
                    #v[pc, opcode, opcode', a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, a_is_0, imm_b, imm_c, is_alu, is_ecall, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_sb, is_sh, is_sw, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, is_auipc, is_unimpl]

          -- Program counter is bounded and aligned
          axioms := fun entry => entry.pc < 2 ^ 30 ∧ entry.pc % 4 = 0

          -- Well formedness entirely derived from the fact that the entries come from the transpiler
          wf_properties := ProgramBusEntry.operand_properties

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

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
        a_0 < 256 ∧ a_1 < 256 ∧ a_2 < 256 ∧ a_3 < 256 ∧
        b_0 < 256 ∧ b_1 < 256 ∧ b_2 < 256 ∧ b_3 < 256 ∧
        c_0 < 256 ∧ c_1 < 256 ∧ c_2 < 256 ∧ c_3 < 256 ∧
        match ALU_opcode with
        | 0 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] + U32.toBV #v[c_0, c_1, c_2, c_3]
        | 1 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] - U32.toBV #v[c_0, c_1, c_2, c_3]
        | 2 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] ^^^ U32.toBV #v[c_0, c_1, c_2, c_3]
        | 3 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] ||| U32.toBV #v[c_0, c_1, c_2, c_3]
        | 4 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] &&& U32.toBV #v[c_0, c_1, c_2, c_3]
        | 5 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] <<< (U32.toNat #v[c_0, c_1, c_2, c_3] % 32)
        | 6 => U32.toBV #v[a_0, a_1, a_2, a_3] = U32.toBV #v[b_0, b_1, b_2, b_3] >>> (U32.toNat #v[c_0, c_1, c_2, c_3] % 32)
        | 7 => U32.toBV #v[a_0, a_1, a_2, a_3] = (U32.toBV #v[b_0, b_1, b_2, b_3]).sshiftRight (U32.toNat #v[c_0, c_1, c_2, c_3] % 32)
        | 8 => U32.toBV #v[a_0, a_1, a_2, a_3] = if (U32.toBV #v[b_0, b_1, b_2, b_3]).toInt < (U32.toBV #v[c_0, c_1, c_2, c_3]).toInt then 1#32 else 0#32
        | 9 => U32.toBV #v[a_0, a_1, a_2, a_3] = if (U32.toBV #v[b_0, b_1, b_2, b_3]).toNat < (U32.toBV #v[c_0, c_1, c_2, c_3]).toNat then 1#32 else 0#32
        | 30 => U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MUL
        | 31 => U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MULH
        | 32 => U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MULHU
        | 33 => U32.toBV #v[a_0, a_1, a_2, a_3] = RV32IM.execute_MUL_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .MULHSU
        | 34 => U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRS).1
        | 35 => U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRU).1
        | 36 => U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRS).2
        | 37 => U32.toBV #v[a_0, a_1, a_2, a_3] = (RV32IM.execute_DIV_REM_pure (U32.toBV #v[b_0, b_1, b_2, b_3]) (U32.toBV #v[c_0, c_1, c_2, c_3]) .DRU).2
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

          -- No axions
          axioms := fun _ => True

          -- Well formedness derived from byte lookup table construction
          wf_properties :=
            fun ⟨ _, ALU_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3 ⟩ =>
              ALUBus.Spec ALU_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

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

      def ByteBusEntry.Spec (byte_opcode x_0 x_1 x_2 x_3 : FKB) :=
        match byte_opcode with
        | 0 => x_0 = x_2 &&& x_3 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 1 => x_0 = x_2 ||| x_3 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 2 => x_0 = x_2 ^^^ x_3 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 3 => x_0 = (x_2 <<< x_3) % 256 ∧ x_0 < 256 ∧ x_1 = 0 ∧ x_2 < 256 ∧ x_3 < 256
        | 4 => x_0 = x_2 >>> x_3 ∧ x_1 = x_2 - (x_0 <<< x_3) ∧ x_0 < 256 ∧ x_1 < 256 ∧ x_2 < 256 ∧ x_3 < 256
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

          -- No axions
          axioms := fun _ => True

          -- Well formedness derived from byte lookup table construction
          wf_properties :=
            fun ⟨ _, byte_opcode, x_0, x_1, x_2, x_3 ⟩ =>
              ByteBusEntry.Spec byte_opcode x_0 x_1 x_2 x_3

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          deserialise := ByteBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (gen := 8)
      }

    end ByteBus

    section RegisterBus

      /-- Byte bus entry -/
      structure RegisterBusEntry where
        multiplicity : F
        chunk : F
        clk : F
        register : F
        x_0 : F
        x_1 : F
        x_2 : F
        x_3 : F
      deriving BEq, DecidableEq, Inhabited

      @[simp, grind]
      def RegisterBusEntry.deserialise
        (entry : FKB × Vector FKB 7)
      : RegisterBusEntry FKB :=
        {
          multiplicity := entry.1,
          chunk := entry.2[0],
          clk := entry.2[1],
          register := entry.2[2],
          x_0 := entry.2[3],
          x_1 := entry.2[4],
          x_2 := entry.2[5],
          x_3 := entry.2[6],
        }

      /-- Register bus entry instance -/
      @[simp, grind]
      instance RegisterBusEntryInstance
      : BusEntry FKB (RegisterBusEntry FKB) :=
      {
          multiplicity := fun entry => entry.1,

          data_length := 7,
          data := fun ⟨_, chunk, clk, register, x_0, x_1, x_2, x_3⟩ =>
                    #v[chunk, clk, register, x_0, x_1, x_2, x_3]

          -- No axions
          axioms := fun _ => True

          -- Well formedness
          wf_properties :=
            fun ⟨ _, chunk, clk, register, x_0, x_1, x_2, x_3 ⟩ =>
              chunk < 65536 ∧ clk < 16777216 ∧ register < 32 ∧ x_0 < 256 ∧ x_1 < 256 ∧ x_2 < 256 ∧ x_3 < 256

          wf_assume_cond := fun entry => entry.1 = -1,
          wf_assert_cond := fun entry => entry.1 = 1,

          deserialise := RegisterBusEntry.deserialise

          inv_deser_ser := by simp
          inv_ser_deser := by
            simp_all
            intro b; cases b
            simp_all; grind (gen := 10)
      }

    end RegisterBus

  end Buses

  section ChipRows

    structure BusRow where
      Program : List (ProgramBusEntry FKB)
      ALU : List (ALUBusEntry FKB)
      Byte : List (ByteBusEntry FKB)
      Register : List (RegisterBusEntry FKB)

    def bus_row_axioms (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.axioms FKB) ++
         row.ALU.map (BusEntry.axioms FKB) ++
         row.Byte.map (BusEntry.axioms FKB) ++
         row.Register.map (BusEntry.axioms FKB))

    def bus_row_assumptions (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.assume FKB) ++
         row.ALU.map (BusEntry.assume FKB) ++
         row.Byte.map (BusEntry.assume FKB) ++
         row.Register.map (BusEntry.assume FKB))

    def bus_row_assertions (row : BusRow) : Prop :=
      List.Forall id
        (row.Program.map (BusEntry.assert FKB) ++
         row.ALU.map (BusEntry.assert FKB) ++
         row.Byte.map (BusEntry.assert FKB) ++
         row.Register.map (BusEntry.assert FKB))

  end ChipRows

end RV32IM_Interactions
