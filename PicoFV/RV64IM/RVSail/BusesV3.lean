import PicoFV.Fundamentals.Interaction

import PicoFV.RV64IM.Transpiler.TranspilerV3
import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.RVSail.Operations

set_option maxHeartbeats 1_000_000_000

/-! # Bus contracts of the Pico v3.1.1 CPU chip

    The Pico v3.1.1 `CpuChip` sends 17 messages per row (`riscv_cpu/constraints.rs`, extracted
    in `Extraction/CpuChip.lean`). This file states what the CPU chip may assume about the
    messages other tables answer, and what it must guarantee about the ones it sends, for the
    message formats that changed from 2.x. It sits beside `Buses.lean`, whose 2.x contracts stay
    unchanged because the memory chip's proofs still use them.

    | message | tag (`LookupType`) | fields | contract |
    |---------|-----|----|----------|
    | Program (instruction fetch) | 2 (Program) | 26 | `V3.ProgramBusEntry`, this file |
    | register read / write | 1 (Memory) | 9 | `StateBusEntry`, `Buses.lean`, unchanged |
    | memory dispatch | 1 (Memory) | 17 | `V3.MemoryBusEntry`, this file |
    | ALU dispatch, ALU compare | 4 (Alu) | 13 | `ALUBusEntry`, `Buses.lean` |
    | byte range checks | 5 (Byte) | 5 | `ByteBusEntry`, `Buses.lean`, unchanged |
    | Ecall | 13 (Ecall) | 20 | none: ignored, as tag 8 was in 2.x |

    The register-access message keeps its 2.x shape `[chunk, clk, addr(3), value(4)]`
    (`machine/builder/riscv_memory.rs:174-208`), so its 2.x contract is reused: a value read
    from the register file has four 16-bit pieces. The ALU contract is reused as well: it
    covers the two comparison opcodes 264 and 265 (`SLT` / `SLTU` + 256) that the CPU sends
    for every branch.

    Open `RV64IM_Interactions.V3`, not `RV64IM_Interactions`, in a file that uses these: the
    entry, row and predicate names are the same as the 2.x ones.                           -/

namespace RV64IM_Interactions.V3

  open Interaction

  export RV64IM_Interactions (StateBusEntry ALUBusEntry ByteBusEntry)

  section ProgramBus

    variable (F : Type) [Field F]

    /-- Program bus entry, payload size 26 (`2 + 1 + 9 + 13 + 1`).

        Layout of the `CpuChip` send (`Extraction/CpuChip.lean`, "Looking Program"):
        `[pc[0], pc[1], opcode, opcode, op_a, op_b(limb0, limb1, sign),
          op_c(limb0, limb1, sign), op_a_0,
          imm_b, imm_c, is_ecall, is_memory, is_store,
          is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal,
          pc_carry]`.                                                                   -/
    structure ProgramBusEntry where
      multiplicity : F
      pc_0 : F
      pc_1 : F
      opcode : F
      opcode' : F
      op_a : F
      b_0 : F
      b_1 : F
      b_sign : F
      c_0 : F
      c_1 : F
      c_sign : F
      op_a_0 : F
      imm_b : F
      imm_c : F
      is_ecall : F
      is_memory : F
      is_store : F
      is_beq : F
      is_bne : F
      is_blt : F
      is_bge : F
      is_bltu : F
      is_bgeu : F
      is_jalr : F
      is_jal : F
      pc_carry : F
    deriving BEq, DecidableEq, Inhabited

    @[simp, grind]
    def ProgramBusEntry.deserialise
      (entry : FKB × Vector FKB 26)
    : ProgramBusEntry FKB :=
      {
        multiplicity := entry.1,
        pc_0 := entry.2[0],
        pc_1 := entry.2[1],
        opcode := entry.2[2],
        opcode' := entry.2[3],
        op_a := entry.2[4],
        b_0 := entry.2[5],
        b_1 := entry.2[6],
        b_sign := entry.2[7],
        c_0 := entry.2[8],
        c_1 := entry.2[9],
        c_sign := entry.2[10],
        op_a_0 := entry.2[11],
        imm_b := entry.2[12],
        imm_c := entry.2[13],
        is_ecall := entry.2[14],
        is_memory := entry.2[15],
        is_store := entry.2[16],
        is_beq := entry.2[17],
        is_bne := entry.2[18],
        is_blt := entry.2[19],
        is_bge := entry.2[20],
        is_bltu := entry.2[21],
        is_bgeu := entry.2[22],
        is_jalr := entry.2[23],
        is_jal := entry.2[24],
        pc_carry := entry.2[25],
      }

    /-- What the Program table delivers: the message is the table row Pico builds for some
        instruction at some address `pc`.

        Pico builds the table at keygen (`riscv_program/traces.rs:78-153`): row `i` holds the
        address `pc_base + 4 i`, with `pc_base` 4-aligned (`traces.rs:83-87`) and every address
        below `0x7800_0000` (`traces.rs:107-110`), its two 16-bit pieces, the decoded
        instruction and `pc_carry = [pc[0] >= 0xFFFC]` (`traces.rs:121-128`). A trap
        instruction gets a copy of row 0 instead (`traces.rs:116-120`) and padding repeats row
        0 (`traces.rs:140-150`), so every row is of this form. The table is preprocessed, and
        the CPU sends with multiplicity `is_real`, so on a real row the whole message equals
        one such row (`riscv_cpu/constraints.rs:42-75`). -/
    def ProgramBusEntry.operand_properties (entry : ProgramBusEntry FKB) : Prop :=
      ∃ instruction pc data props,
        pc % 4 = 0 ∧ pc < Transpiler.V3.code_address_bound ∧
        (.some ⟨ data, props ⟩ = Transpiler.V3.transpile_op instruction entry.multiplicity pc) ∧
        (entry = ProgramBusEntry.deserialise data) ∧
        props

    /-! ### From a Program message back to its instruction

        Each lemma takes the two facts `operand_properties` gives after unpacking: the decoder
        produced `data` for `instr` at `pc`, and the message is `data`. They are stated on the
        message, not on a chip's columns. -/

    section Inversion

    open Transpiler Transpiler.V3

    /-- A load's row, with its opcode read off `is_unsigned` and the width. -/
    lemma transpile_op_LOAD_row {imm : BitVec 12} {rs1 rd : regidx} {u : Bool} {wd : word_width}
        {m : FKB} {pc : ℕ} {data : FKB × Vector FKB 26} {props : Prop}
        (h : Transpiler.V3.transpile_op (.LOAD (imm, rs1, rd, u, wd)) m pc = some (data, props)) :
        ∃ opc : FKB,
          ((u = false ∧ wd = 1 ∧ opc = 10) ∨ (u = true ∧ wd = 1 ∧ opc = 13) ∨
           (u = false ∧ wd = 2 ∧ opc = 11) ∨ (u = true ∧ wd = 2 ∧ opc = 14) ∨
           (u = false ∧ wd = 4 ∧ opc = 12) ∨ (u = true ∧ wd = 4 ∧ opc = 45) ∨
           (u = false ∧ wd = 8 ∧ opc = 46)) ∧
          data = (m, #v[pc_lo pc, pc_hi pc, opc, opc, reg_to_KB rd, reg_to_KB rs1, 0, 0,
                        (imm_operand imm true)[0], (imm_operand imm true)[1],
                        (imm_operand imm true)[2],
                        ((if rd == regidx.Regidx 0 then 1 else 0 : ℕ) : FKB), 0, 1, 0, 1, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, pc_carry pc]) := by
      simp only [Transpiler.V3.transpile_op] at h
      split at h
      · simp at h
      · rename_i opc hopc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨ _, ?_, h.1.symm ⟩
        clear h
        split at hopc <;> simp_all

    /-- A store's row, with its opcode read off the width. -/
    lemma transpile_op_STORE_row {imm : BitVec 12} {rs2 rs1 : regidx} {wd : word_width}
        {m : FKB} {pc : ℕ} {data : FKB × Vector FKB 26} {props : Prop}
        (h : Transpiler.V3.transpile_op (.STORE (imm, rs2, rs1, wd)) m pc = some (data, props)) :
        ∃ opc : FKB,
          ((wd = 1 ∧ opc = 15) ∨ (wd = 2 ∧ opc = 16) ∨ (wd = 4 ∧ opc = 17) ∨
           (wd = 8 ∧ opc = 47)) ∧
          data = (m, #v[pc_lo pc, pc_hi pc, opc, opc, reg_to_KB rs2, reg_to_KB rs1, 0, 0,
                        (imm_operand imm true)[0], (imm_operand imm true)[1],
                        (imm_operand imm true)[2],
                        ((if rs2 == regidx.Regidx 0 then 1 else 0 : ℕ) : FKB), 0, 1, 0, 1, 1,
                        0, 0, 0, 0, 0, 0, 0, 0, pc_carry pc]) := by
      simp only [Transpiler.V3.transpile_op] at h
      split at h
      · simp at h
      · rename_i opc hopc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨ _, ?_, h.1.symm ⟩
        clear h
        split at hopc <;> simp_all

    set_option hygiene false in
    /-- Splits a decoded Program-bus message by instruction: one goal per Sail constructor and
        operation the decoder gives a row, with the message's 26 fields written out. Expects
        `data`, `h_trans` and `h_deser` as in the lemmas below. -/
    local macro "program_bus_cases" : tactic => `(tactic| (
      obtain ⟨ m, v ⟩ := data
      subst h_deser
      simp only [ProgramBusEntry.deserialise] at h_trans ⊢
      cases instr
      case' RTYPE x => obtain ⟨ rs2, rs1, rd, op ⟩ := x; cases op
      case' RTYPEW x => obtain ⟨ rs2, rs1, rd, op ⟩ := x; cases op
      case' ITYPE x => obtain ⟨ imm, rs1, rd, op ⟩ := x; cases op
      case' ADDIW x => obtain ⟨ imm, rs1, rd ⟩ := x
      case' SHIFTIOP x => obtain ⟨ imm, rs1, rd, op ⟩ := x; cases op
      case' SHIFTIWOP x => obtain ⟨ imm, rs1, rd, op ⟩ := x; cases op
      case' LOAD x =>
        obtain ⟨ imm, rs1, rd, u, wd ⟩ := x
        obtain ⟨ opc, h_opc, h_v ⟩ := transpile_op_LOAD_row h_trans.symm
        simp only [Prod.mk.injEq] at h_v
        obtain ⟨ -, rfl ⟩ := h_v
        clear h_trans
        rcases h_opc with ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ |
          ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩
      case' STORE x =>
        obtain ⟨ imm, rs2, rs1, wd ⟩ := x
        obtain ⟨ opc, h_opc, h_v ⟩ := transpile_op_STORE_row h_trans.symm
        simp only [Prod.mk.injEq] at h_v
        obtain ⟨ -, rfl ⟩ := h_v
        clear h_trans
        rcases h_opc with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩
      case' BTYPE x => obtain ⟨ imm, rs2, rs1, op ⟩ := x; cases op
      case' JALR x => obtain ⟨ imm, rs1, rd ⟩ := x
      case' JAL x => obtain ⟨ imm, rd ⟩ := x
      case' UTYPE x => obtain ⟨ imm, rd, op ⟩ := x; cases op
      case' MUL x =>
        obtain ⟨ rs2, rs1, rd, ⟨ rp, s1, s2 ⟩ ⟩ := x
        cases rp <;> cases s1 <;> cases s2
      case' MULW x => obtain ⟨ rs2, rs1, rd ⟩ := x
      case' DIV x => obtain ⟨ rs2, rs1, rd, sgn ⟩ := x; cases sgn
      case' DIVW x => obtain ⟨ rs2, rs1, rd, sgn ⟩ := x; cases sgn
      case' REM x => obtain ⟨ rs2, rs1, rd, sgn ⟩ := x; cases sgn
      case' REMW x => obtain ⟨ rs2, rs1, rd, sgn ⟩ := x; cases sgn
      all_goals (try simp [Transpiler.V3.transpile_op, opcode_of_rop, opcode_of_ropw,
                           opcode_of_iop, opcode_of_sop, opcode_of_sopw, opcode_of_bop,
                           -Vector.eq_mk] at h_trans)
      all_goals (try (obtain ⟨ h_v, - ⟩ := h_trans; subst h_v))))

    /-- The message's pc fields are the two pieces of the instruction's address, and its
        `pc_carry` is that address's carry. -/
    lemma ProgramBusEntry.inversion_pc
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.pc_0 = pc_lo pc ∧ entry.pc_1 = pc_hi pc ∧ entry.pc_carry = Transpiler.V3.pc_carry pc
    := by
      program_bus_cases
      all_goals simp

    /-- With the Program promise's conditions on the address (4-aligned, below `0x7800_0000`):
        the pc pieces are 16-bit, the high piece is at most `0x77FF`, the low piece is
        4-aligned, the two pieces make the address, and `pc_carry` is `[pc[0] >= 0xFFFC]`. -/
    lemma ProgramBusEntry.inversion_pc_facts
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
      (h_al : pc % 4 = 0) (h_lt : pc < Transpiler.V3.code_address_bound)
    :
      entry.pc_0.val < 65536 ∧ entry.pc_1.val < 65536 ∧ entry.pc_1.val ≤ 0x77FF ∧
      entry.pc_0.val % 4 = 0 ∧
      entry.pc_0.val + 65536 * entry.pc_1.val = pc ∧ pc < 0x7800_0000 ∧
      entry.pc_carry = (if 0xFFFC ≤ entry.pc_0.val then 1 else 0)
    := by
      obtain ⟨ e0, e1, e25 ⟩ := ProgramBusEntry.inversion_pc h_trans h_deser
      obtain ⟨ hlo, hhi, hsum ⟩ := Transpiler.V3.pc_pieces h_lt
      have h4 := Transpiler.V3.pc_lo_mod_four h_al
      rw [e0, e1, e25, Transpiler.V3.pc_carry_eq]
      simp only [Transpiler.V3.code_address_bound] at h_lt
      exact ⟨ hlo, by omega, hhi, h4, hsum, h_lt, rfl ⟩

    /-- The two opcode fields are equal, and the opcode is one the decoder produces: 0 to 25,
        28, 30 to 37, or 40 to 52. There is no 26, 27, 29, 38 or 39; in particular no row has
        the `AUIPC` opcode 27, which Pico v3.1.1 no longer emits. -/
    lemma ProgramBusEntry.inversion_opcode_bounds
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.opcode' = entry.opcode ∧
      (entry.opcode.val ≤ 25 ∨ entry.opcode.val = 28 ∨
       (30 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 37) ∨
       (40 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 52))
    := by
      program_bus_cases
      all_goals simp

    /-- For each opcode value, the Sail instruction the row was decoded from. Against 2.x:
        opcode 0 with both immediate flags is `LUI` or `AUIPC` (no field tells them apart),
        each with its operand shape; there is no opcode 27; opcode 28 is `ECALL`. -/
    lemma ProgramBusEntry.operand_properties_inversion
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      -- Opcode 0: ADD, ADDI, or one of LUI and AUIPC, which give rows of the same shape.
      (entry.opcode = 0 →
        (entry.imm_b = 0 ∧ entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .ADD)) ∨
        (entry.imm_b = 0 ∧ entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ADDI)) ∨
        (entry.imm_b = 1 ∧ entry.imm_c = 1 ∧ ∃ imm rd,
          (instr = .UTYPE (imm, rd, .LUI) ∧
            entry.b_0 = 0 ∧ entry.b_1 = 0 ∧ entry.b_sign = 0 ∧
            entry.c_0 = (imm_operand (imm ++ 0#12) true)[0] ∧
            entry.c_1 = (imm_operand (imm ++ 0#12) true)[1] ∧
            entry.c_sign = (imm_operand (imm ++ 0#12) true)[2]) ∨
          (instr = .UTYPE (imm, rd, .AUIPC) ∧
            entry.b_0 = (imm_operand (imm ++ 0#12) true)[0] ∧
            entry.b_1 = (imm_operand (imm ++ 0#12) true)[1] ∧
            entry.b_sign = (imm_operand (imm ++ 0#12) true)[2] ∧
            entry.c_0 = pc_lo pc ∧ entry.c_1 = pc_hi pc ∧ entry.c_sign = 0))) ∧
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
      -- Loads and stores
      (entry.opcode = 10 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 1)) ∧
      (entry.opcode = 11 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 2)) ∧
      (entry.opcode = 12 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 4)) ∧
      (entry.opcode = 13 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 1)) ∧
      (entry.opcode = 14 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 2)) ∧
      (entry.opcode = 45 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 4)) ∧
      (entry.opcode = 46 → ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 8)) ∧
      (entry.opcode = 15 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 1)) ∧
      (entry.opcode = 16 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 2)) ∧
      (entry.opcode = 17 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 4)) ∧
      (entry.opcode = 47 → ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 8)) ∧
      -- Branches and jumps
      (entry.opcode = 18 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BEQ)) ∧
      (entry.opcode = 19 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BNE)) ∧
      (entry.opcode = 20 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BLT)) ∧
      (entry.opcode = 21 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BGE)) ∧
      (entry.opcode = 22 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BLTU)) ∧
      (entry.opcode = 23 → ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BGEU)) ∧
      (entry.opcode = 24 → ∃ imm rd, instr = .JAL (imm, rd)) ∧
      (entry.opcode = 25 → ∃ imm rs1 rd, instr = .JALR (imm, rs1, rd)) ∧
      (entry.opcode = 28 → instr = .ECALL ()) ∧
      -- Multiply, divide, remainder. Sail's last `DIV` / `REM` field is `is_unsigned`.
      (entry.opcode = 30 → ∃ rs2 rs1 rd sl sr, instr = .MUL (rs2, rs1, rd, { result_part := .Low, signed_rs1 := sl, signed_rs2 := sr })) ∧
      (entry.opcode = 31 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed })) ∧
      (entry.opcode = 32 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })) ∧
      (entry.opcode = 33 → ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })) ∧
      (entry.opcode = 34 → ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, false)) ∧
      (entry.opcode = 35 → ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, true)) ∧
      (entry.opcode = 36 → ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, false)) ∧
      (entry.opcode = 37 → ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, true)) ∧
      -- Word ALU
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
      -- Word multiply, divide, remainder
      (entry.opcode = 48 → ∃ rs2 rs1 rd, instr = .MULW (rs2, rs1, rd)) ∧
      (entry.opcode = 49 → ∃ rs2 rs1 rd, instr = .DIVW (rs2, rs1, rd, false)) ∧
      (entry.opcode = 50 → ∃ rs2 rs1 rd, instr = .DIVW (rs2, rs1, rd, true)) ∧
      (entry.opcode = 51 → ∃ rs2 rs1 rd, instr = .REMW (rs2, rs1, rd, false)) ∧
      (entry.opcode = 52 → ∃ rs2 rs1 rd, instr = .REMW (rs2, rs1, rd, true))
    := by
      program_bus_cases
      all_goals simp

    /-- For each opcode value, the class selectors, and the immediate flags the opcode
        forces. Where two instruction shapes share an opcode (an ALU operation with a register
        or an immediate third operand, and opcode 0) the flag that varies is left out; its
        value is in `operand_properties_inversion`. -/
    lemma ProgramBusEntry.inversion_opcode_selectors
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      -- ALU, opcode 0: ADD, ADDI, LUI, AUIPC; both immediate flags vary
      (entry.opcode = 0 → ( entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- SUB: registers only
      (entry.opcode = 1 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- ALU with a register or an immediate third operand: `imm_c` varies
      (entry.opcode = 2 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 3 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 4 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 5 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 6 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 7 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 8 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 9 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- loads
      (entry.opcode = 10 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 11 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 12 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 13 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 14 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- stores
      (entry.opcode = 15 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 16 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 17 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- branches
      (entry.opcode = 18 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 19 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 20 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 21 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 )) ∧
      (entry.opcode = 22 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 )) ∧
      (entry.opcode = 23 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 )) ∧
      -- jumps
      (entry.opcode = 24 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 )) ∧
      (entry.opcode = 25 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0 )) ∧
      -- ECALL
      (entry.opcode = 28 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- multiply, divide, remainder
      (entry.opcode = 30 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 31 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 32 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 33 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 34 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 35 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 36 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 37 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- word ALU; `imm_c` varies except for SUBW
      (entry.opcode = 40 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 41 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 42 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 43 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 44 → ( entry.imm_b, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- LWU, LD, SD
      (entry.opcode = 45 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 46 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 47 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      -- word multiply, divide, remainder
      (entry.opcode = 48 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 49 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 50 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 51 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 )) ∧
      (entry.opcode = 52 → ( entry.imm_b, entry.imm_c, entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne, entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal ) = ( 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ))
    := by
      program_bus_cases
      all_goals simp

    /-- Every flag and selector is 0 or 1, at most one instruction class is set, and a store
        is a memory instruction. -/
    lemma ProgramBusEntry.inversion_selectors_one_hot
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      (entry.imm_b = 0 ∨ entry.imm_b = 1) ∧ (entry.imm_c = 0 ∨ entry.imm_c = 1) ∧
      (entry.is_ecall = 0 ∨ entry.is_ecall = 1) ∧ (entry.is_memory = 0 ∨ entry.is_memory = 1) ∧
      (entry.is_store = 0 ∨ entry.is_store = 1) ∧
      (entry.is_beq = 0 ∨ entry.is_beq = 1) ∧ (entry.is_bne = 0 ∨ entry.is_bne = 1) ∧
      (entry.is_blt = 0 ∨ entry.is_blt = 1) ∧ (entry.is_bge = 0 ∨ entry.is_bge = 1) ∧
      (entry.is_bltu = 0 ∨ entry.is_bltu = 1) ∧ (entry.is_bgeu = 0 ∨ entry.is_bgeu = 1) ∧
      (entry.is_jalr = 0 ∨ entry.is_jalr = 1) ∧ (entry.is_jal = 0 ∨ entry.is_jal = 1) ∧
      (entry.is_ecall + entry.is_memory + entry.is_beq + entry.is_bne + entry.is_blt +
        entry.is_bge + entry.is_bltu + entry.is_bgeu + entry.is_jalr + entry.is_jal = 0 ∨
       entry.is_ecall + entry.is_memory + entry.is_beq + entry.is_bne + entry.is_blt +
        entry.is_bge + entry.is_bltu + entry.is_bgeu + entry.is_jalr + entry.is_jal = 1) ∧
      (entry.is_store = 1 → entry.is_memory = 1)
    := by
      program_bus_cases
      all_goals simp

    /-- Operand facts: `op_a` is a register index and `op_a_0` is `[op_a = 0]`; an operand
        whose immediate flag is 0 is a register index (second piece and sign 0); every piece
        is 16-bit and every sign is 0 or 1. -/
    lemma ProgramBusEntry.inversion_operands
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.V3.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.op_a.val < 32 ∧ entry.op_a_0 = (if entry.op_a = 0 then 1 else 0) ∧
      (entry.imm_b = 0 → entry.b_0.val < 32 ∧ entry.b_1 = 0 ∧ entry.b_sign = 0) ∧
      (entry.imm_c = 0 → entry.c_0.val < 32 ∧ entry.c_1 = 0 ∧ entry.c_sign = 0) ∧
      entry.b_0.val < 65536 ∧ entry.b_1.val < 65536 ∧ (entry.b_sign = 0 ∨ entry.b_sign = 1) ∧
      entry.c_0.val < 65536 ∧ entry.c_1.val < 65536 ∧ (entry.c_sign = 0 ∨ entry.c_sign = 1)
    := by
      program_bus_cases
      all_goals simp [reg_to_KB_lt]
      all_goals (repeat' apply And.intro)
      all_goals first
        | exact reg_is_x0 _
        | exact lt_trans (reg_to_KB_lt _) (by norm_num)
        | exact (imm_operand_limbs _ _).1
        | exact (imm_operand_limbs _ _).2.1
        | exact (imm_operand_limbs _ _).2.2
        | omega

    end Inversion

    @[simp, grind]
    instance ProgramBusEntryInstance
    : BusEntry FKB (ProgramBusEntry FKB) :=
    {
        multiplicity := fun entry => entry.1,

        data_length := 26,
        data := fun ⟨_, pc_0, pc_1, opcode, opcode', op_a, b_0, b_1, b_sign, c_0, c_1, c_sign, op_a_0, imm_b, imm_c, is_ecall, is_memory, is_store, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, pc_carry⟩ =>
                  #v[pc_0, pc_1, opcode, opcode', op_a, b_0, b_1, b_sign, c_0, c_1, c_sign, op_a_0, imm_b, imm_c, is_ecall, is_memory, is_store, is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu, is_jalr, is_jal, pc_carry]

        -- The pc facts are part of `operand_properties`: they come from the same table.
        axioms := fun _ => True

        -- The CPU chip asserts nothing to the Program table.
        externals := fun _ => True

        wf_properties := ProgramBusEntry.operand_properties

        deserialise := ProgramBusEntry.deserialise

        inv_deser_ser := by simp
        inv_ser_deser := by
          simp_all
          intro b; cases b
          simp_all; grind (splits := 32) (gen := 32) (ematch := 16)
    }

  end ProgramBus

  section MemoryBus

    variable (F : Type) [Field F]

    /-- Memory dispatch entry, payload size 17.

        Layout of the `CpuChip` send (`riscv_cpu/constraints.rs:117-133`):
        `[opcode, a(4), b(4), c(4), op_a_0, is_memory, chunk, clk]`. The access width is
        no longer a selector: the memory chip derives it from the opcode
        (`riscv_memory/read_write/constraints.rs:146-191`). `a` is the value of register `a`
        after the row: the loaded value for a load, the stored value for a store. -/
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
      op_a_0 : F
      is_memory : F
      chunk : F
      clk : F
    deriving BEq, DecidableEq, Inhabited

    @[simp, grind]
    def MemoryBusEntry.deserialise
      (entry : FKB × Vector FKB 17)
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
        op_a_0 := entry.2[13],
        is_memory := entry.2[14],
        chunk := entry.2[15],
        clk := entry.2[16],
      }

    /-- The memory opcodes: `LB 10, LH 11, LW 12, LBU 13, LHU 14, SB 15, SH 16, SW 17,
        LWU 45, LD 46, SD 47` (`compiler/riscv/opcode.rs`). -/
    def MemoryBus.validOpcode (mem_opcode : FKB) : Prop :=
      mem_opcode ∈ Finset.Icc 10 17 ∨ mem_opcode ∈ Finset.Icc 45 47

    def MemoryBus.isStore (mem_opcode : FKB) : Prop :=
      mem_opcode ∈ Finset.Icc 15 17 ∨ mem_opcode = 47

    /-- What the memory chip guarantees, which the CPU chip assumes when it sends.

        Same content as the 2.x `MemoryBus.Spec`, keyed on the opcode as before, except the
        address bound: the v3.1.1 memory chip proves `b + c` with an in-chip carry chain whose
        third and fourth result limbs are zero, so the address is below `2^32`, and its stack
        guard keeps it at or above `2^16` (`riscv_memory/read_write/constraints.rs:209-255`).
        The `chunk` and `clk` fields carry no promise here; the memory chip's own proofs may
        need one. -/
    def MemoryBus.Spec
      (mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 op_a_0 : FKB) : Prop :=
      let a := U64w.toBV #v[a_0, a_1, a_2, a_3]
      let b := U64w.toBV #v[b_0, b_1, b_2, b_3]
      let c := U64w.toBV #v[c_0, c_1, c_2, c_3]
      let addr := (b + c).toNat
      ((mem_opcode.val ≤ 14 ∨ mem_opcode.val = 45 ∨ mem_opcode.val = 46) →
          a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536) ∧
      65536 ≤ addr ∧ addr < 2 ^ 32 ∧
      (mem_opcode = 11 ∨ mem_opcode = 14 ∨ mem_opcode = 16 → 2 ∣ addr) ∧
      (mem_opcode = 12 ∨ mem_opcode = 17 ∨ mem_opcode = 45 → 4 ∣ addr) ∧
      (mem_opcode = 46 ∨ mem_opcode = 47 → 8 ∣ addr) ∧
      (mem_opcode = 10 → op_a_0 = 0 → a = BitVec.signExtend 64 (a.truncate 8)) ∧   -- LB
      (mem_opcode = 11 → op_a_0 = 0 → a = BitVec.signExtend 64 (a.truncate 16)) ∧  -- LH
      (mem_opcode = 12 → op_a_0 = 0 → a = BitVec.signExtend 64 (a.truncate 32)) ∧  -- LW
      (mem_opcode = 13 → op_a_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 8)) ∧   -- LBU
      (mem_opcode = 14 → op_a_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 16)) ∧  -- LHU
      (mem_opcode = 45 → op_a_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 32))    -- LWU

    /-- What the CPU chip guarantees when it sends, which the memory chip may assume.

        From the CPU constraints: the opcode and `is_memory` come from the Program table
        (`is_memory` is the multiplicity); `b` is a register value or, with `c`, an immediate
        whose limbs are 16-bit; a store's `a` is the previous register value
        (`register/constraints.rs:117-123`); `op_a_0 = 1` forces `a = 0`
        (`register/constraints.rs:73-76`). -/
    def MemoryBus.externals (entry : MemoryBusEntry FKB) : Prop :=
      ¬ (entry.multiplicity = 0) →
        MemoryBus.validOpcode entry.mem_opcode ∧
        entry.is_memory = 1 ∧
        entry.b_0.val < 65536 ∧ entry.b_1.val < 65536 ∧
        entry.b_2.val < 65536 ∧ entry.b_3.val < 65536 ∧
        entry.c_0.val < 65536 ∧ entry.c_1.val < 65536 ∧
        entry.c_2.val < 65536 ∧ entry.c_3.val < 65536 ∧
        (MemoryBus.isStore entry.mem_opcode →
          entry.a_0.val < 65536 ∧ entry.a_1.val < 65536 ∧
          entry.a_2.val < 65536 ∧ entry.a_3.val < 65536) ∧
        (¬ entry.op_a_0 = 0 → entry.a_0 = 0 ∧ entry.a_1 = 0 ∧ entry.a_2 = 0 ∧ entry.a_3 = 0)

    @[simp, grind]
    instance MemoryBusEntryInstance
    : BusEntry FKB (MemoryBusEntry FKB) :=
    {
        multiplicity := fun entry => entry.1,

        data_length := 17,
        data := fun ⟨_, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, op_a_0, is_memory, chunk, clk⟩ =>
                  #v[mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, op_a_0, is_memory, chunk, clk]

        axioms := fun _ => True

        externals := MemoryBus.externals

        wf_properties := fun ⟨_, mem_opcode, a_0, a_1, a_2, a_3, b_0, b_1, b_2, b_3, c_0, c_1, c_2, c_3, op_a_0, _, _, _⟩ =>
          MemoryBus.Spec mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 op_a_0

        deserialise := MemoryBusEntry.deserialise

        inv_deser_ser := by simp
        inv_ser_deser := by
          simp_all
          intro b; cases b
          simp_all; grind (splits := 20) (gen := 20) (ematch := 10)
    }

  end MemoryBus

  section ChipRows

    /-- The CPU chip's messages on one row, sorted by contract. -/
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

    /-- Sort a raw row of messages (multiplicity, `[tag, ...data]`) into a `BusRow`. Tags are
        Pico's `LookupType` discriminants: Memory 1 (register access, 9 fields, and memory
        dispatch, 17 fields, told apart by length), Program 2 (26), Alu 4 (13), Byte 5 (5).
        Ecall 13 and every other tag are ignored. -/
    def deserialise_bus_row (row : List (FKB × List FKB)) : BusRow :=
      let initial_bus_row : BusRow :=
        { Program := [], ALU := [], Byte := [], State := [], Memory := [] }
      List.foldl
        (fun result ⟨ multiplicity, entry ⟩ =>
          let bus_id := entry.head!
          let entry_data := entry.tail!
          match bus_id with
          | 1 =>
              if _ : entry_data.length = 9 then
                let entry_data_vector : Vector FKB 9 := ⟨ entry_data.toArray, by simp; omega ⟩
                let bus_entry := RV64IM_Interactions.StateBusEntry.deserialise (multiplicity, entry_data_vector)
                { result with State := result.State ++ [ bus_entry ] }
              else (
                if _ : entry_data.length = 17 then
                  let entry_data_vector : Vector FKB 17 := ⟨ entry_data.toArray, by simp; omega ⟩
                  let bus_entry := MemoryBusEntry.deserialise (multiplicity, entry_data_vector)
                  { result with Memory := result.Memory ++ [ bus_entry ] }
                else result
              )
          | 2 =>
            if _ : entry_data.length = 26 then
              let entry_data_vector : Vector FKB 26 := ⟨ entry_data.toArray, by simp; omega ⟩
              let bus_entry := ProgramBusEntry.deserialise (multiplicity, entry_data_vector)
              { result with Program := result.Program ++ [ bus_entry ] }
            else result
          | 4 =>
              if _ : entry_data.length = 13 then
                let entry_data_vector : Vector FKB 13 := ⟨ entry_data.toArray, by simp; omega ⟩
                let bus_entry := RV64IM_Interactions.ALUBusEntry.deserialise (multiplicity, entry_data_vector)
                { result with ALU := result.ALU ++ [ bus_entry ] }
              else result
          | 5 =>
            if _ : entry_data.length = 5 then
              let entry_data_vector : Vector FKB 5 := ⟨ entry_data.toArray, by simp; omega ⟩
              let bus_entry := RV64IM_Interactions.ByteBusEntry.deserialise (multiplicity, entry_data_vector)
              { result with Byte := result.Byte ++ [ bus_entry ] }
            else result
          | _ => result
        )
        initial_bus_row
        row

  end ChipRows

  section BusOperations

    open RV64IM

    /-- Access width of a memory opcode (`LD`/`SD` 8 bytes, `LW`/`LWU`/`SW` 4, `LH`/`LHU`/`SH`
        2, `LB`/`LBU`/`SB` 1). -/
    def mem_width_of_opcode (mem_opcode : FKB) : Option MemoryWidth :=
      if mem_opcode = 46 ∨ mem_opcode = 47 then .some .Double
      else if mem_opcode = 12 ∨ mem_opcode = 45 ∨ mem_opcode = 17 then .some .Word
      else if mem_opcode = 11 ∨ mem_opcode = 14 ∨ mem_opcode = 16 then .some .Half
      else if mem_opcode = 10 ∨ mem_opcode = 13 ∨ mem_opcode = 15 then .some .Byte
      else .none

    /-- The register and memory operations a row's messages stand for: a pc read per Program
        message, a register read or write per register-access message, and a memory read or
        write per memory dispatch. Same as the 2.x `bus_operations` except that the pc has two
        pieces and the access width and direction come from the opcode. -/
    def bus_operations (row : BusRow) : List Operation :=
      let program : List Operation :=
        List.map (fun program_row =>
          .ReadPC (BitVec.ofNatLT (w := 64)
            (program_row.pc_0.val + 65536 * program_row.pc_1.val)
            (by omega))
        ) row.Program
      let state : List Operation :=
        List.filterMap (
          fun (state_row : StateBusEntry FKB) =>
            let value := U64w.toBV
              #v[state_row.x_0, state_row.x_1, state_row.x_2, state_row.x_3]
            let addr := state_row.ptr_0.val + 65536 * state_row.ptr_1.val
                      + 65536 * 65536 * state_row.ptr_2.val
            if _ : addr < 32 then
              let register : regidx := .Regidx (BitVec.ofNatLT (w := 5) addr (by omega))
              if (state_row.multiplicity = 1) then
                .some (.ReadReg register value)
              else if (state_row.multiplicity = -1) then
                .some (.WriteReg register value)
              else .none
            else
              if (state_row.multiplicity = 1) then
                .some (.ReadMem addr .Double value)
              else if (state_row.multiplicity = -1) then
                .some (.WriteMem addr .Double value)
              else .none
        ) row.State
      let memory : List Operation :=
        List.filterMap (
          fun (memory_row : MemoryBusEntry FKB) =>
            match mem_width_of_opcode memory_row.mem_opcode with
            | .none => .none
            | .some width =>
              let address :=
                (U64w.toBV #v[memory_row.b_0, memory_row.b_1, memory_row.b_2, memory_row.b_3]
                  + U64w.toBV #v[memory_row.c_0, memory_row.c_1, memory_row.c_2, memory_row.c_3]).toNat
              let is_store : Bool :=
                memory_row.mem_opcode == 15 ∨ memory_row.mem_opcode == 16
                  ∨ memory_row.mem_opcode == 17 ∨ memory_row.mem_opcode == 47
              match is_store with
              | true =>
                match width with
                | .Byte   => .some (.WriteMem address .Byte   (BitVec.ofNat 8  (memory_row.a_0).val))
                | .Half   => .some (.WriteMem address .Half   (BitVec.ofNat 16 (memory_row.a_0).val))
                | .Word   => .some (.WriteMem address .Word
                                     ((BitVec.ofNat 16 (memory_row.a_1).val)
                                     ++ (BitVec.ofNat 16 (memory_row.a_0).val)))
                | .Double => .some (.WriteMem address .Double
                                     (U64w.toBV #v[memory_row.a_0, memory_row.a_1, memory_row.a_2, memory_row.a_3]))
              | false =>
                if memory_row.op_a_0 = 1 then
                  .some (.ReadMemAny address width)
                else
                  match width with
                  | .Byte   => .some (.ReadMem address .Byte   (BitVec.ofNat 8  (memory_row.a_0).val))
                  | .Half   => .some (.ReadMem address .Half   (BitVec.ofNat 16 (memory_row.a_0).val))
                  | .Word   => .some (.ReadMem address .Word
                                       ((BitVec.ofNat 16 (memory_row.a_1).val)
                                       ++ (BitVec.ofNat 16 (memory_row.a_0).val)))
                  | .Double => .some (.ReadMem address .Double
                                       (U64w.toBV #v[memory_row.a_0, memory_row.a_1, memory_row.a_2, memory_row.a_3]))
        ) row.Memory
      program ++ state ++ memory

  end BusOperations

end RV64IM_Interactions.V3
