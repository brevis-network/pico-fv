import PicoFV.Fundamentals.Interaction

import PicoFV.RV64IM.Transpiler.Transpiler
import PicoFV.RV64IM.RVSail.Execution
import PicoFV.RV64IM.RVSail.Operations

set_option maxHeartbeats 1_000_000_000

/-! # Bus contracts

    The Pico v3.1.1 `CpuChip` sends 17 messages per row (`riscv_cpu/constraints.rs`, extracted
    in `Extraction/CpuChip.lean`). This file states what the CPU chip may assume about the
    messages other tables answer, and what it must guarantee about the ones it sends, for the
    messages its row carries. It also holds the v3.2.0 code-range contract between the rows that
    write guest memory (store rows of the two memory chips, and precompile rows) and the Program
    table, which the CPU chip never sends. Every chip's row is this file's `BusRow`.

    | message | tag (`LookupType`) | fields | contract |
    |---------|-----|----|----------|
    | Program (instruction fetch) | 2 (Program) | 26 | `ProgramBusEntry`, this file |
    | register read / write | 1 (Memory) | 9 | `StateBusEntry`, this file, 2.x shape |
    | memory dispatch | 1 (Memory) | 17 | `MemoryBusEntry`, this file |
    | ALU dispatch, ALU compare | 4 (Alu) | 13 | `ALUBusEntry`, this file |
    | byte range checks | 5 (Byte) | 5 | `ByteBusEntry`, this file, 2.x shape |
    | Ecall | 13 (Ecall) | 20 | none: ignored, as tag 8 was in 2.x |
    | code range | 2 (Program) | 4 | `CodeRangeBusEntry`, this file |

    The CPU chip does not send the code-range message: a store row of either memory chip, and a
    precompile row for what it writes, does, through the `code_range` gadget
    (`gadgets/code_range.rs:1-11`, `Spec/CodeRangeGadget.lean`), and the Program table answers it. It
    shares the Program tag with the instruction fetch and is told apart by its length, 4 against
    26 (`riscv_program/constraints.rs:55-57` at v3.2.0).

    The register-access message keeps its 2.x shape `[chunk, clk, addr(3), value(4)]`
    (`machine/builder/riscv_memory.rs:174-208`), so its contract is the 2.x one: a value read
    from the register file has four 16-bit pieces. The ALU contract is reused as well: it
    covers the two comparison opcodes 264 and 265 (`SLT` / `SLTU` + 256) that the CPU sends
    for every branch.

    Pico line numbers in this file are at v3.1.1 (`2acc7c1828fb`), except in `MemoryBus.Spec`,
    the memory chips' citations in `MemoryBusEntry` and the code-range section, which are at
    v3.2.0 (`fcfa50462465`).
    From v3.1.1 to v3.1.6, and to v3.2.0, the CPU chip's constraint files are unchanged; its
    trace generation (`riscv_cpu/event.rs`, `traces.rs`) changed, as did the Program chip's and
    `MemoryReadWriteChip`'s columns, constraints and trace generation. Since v3.1.2 the memory
    dispatch has a second receiver, `MemoryUnalignedChip`, so `MemoryBus.Spec` states only what
    both receivers prove. -/

namespace RV64IM_Interactions

  open Interaction

  /-! Lawful `==` on the decoder's opcode enums, so `simp` decides `op₁ == op₂`. -/

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

  /-! The register-access, ALU and byte contracts, unchanged in shape since 2.x. -/

  section SharedBuses

    variable
      (F : Type)
      [Field F]

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

      /-- Set of all valid ALU bus opcodes.

          `264` and `265` are the two branch-comparison opcodes,
          `SLT + LT_CMP_OPCODE_TAG` and `SLTU + LT_CMP_OPCODE_TAG` with
          the tag `1 <<< 8` (`alu/lt/columns.rs:22`). The CPU sends one
          of them for every branch and reads both strict comparison bits
          off the single reply; `LtChip` serves them on its merged rows
          (`is_cmp = 1`). The tag keeps such a reply from pairing with a
          plain `SLT` / `SLTU` dispatch. -/
      def ALUBus.validOpcode (ALU_opcode : FKB) : Prop :=
        ALU_opcode ∈ Finset.Icc 0 9 ∨
        ALU_opcode ∈ Finset.Icc 30 37 ∨
        ALU_opcode ∈ Finset.Icc 40 44 ∨
        ALU_opcode ∈ Finset.Icc 48 52 ∨
        ALU_opcode = 264 ∨
        ALU_opcode = 265

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
          - `execute_DIV_REM_pure` / `execute_DIVW_REMW_pure` for DIV/REM.

          The two branch-comparison opcodes `264` / `265` are the
          exception to "`a` = one pure execute function": they carry two
          strict comparison bits in pieces 0 and 1, so their relation is
          stated limb by limb. Like `8` / `9`, they are not in
          `ALUBus.operandsInternal`: `LtChip` does not range-check its
          operands, it receives their bounds through `externals`. -/
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
        -- Branch comparisons (`LtChip`'s merged rows). The result is not
        -- one word but two strict comparison bits: piece 0 is `[b < c]`,
        -- piece 1 is `[c < b]`, and pieces 2 and 3 are zero. The CPU
        -- recovers `[b = c]` as `1 - a_0 - a_1`.
        | 264 => a_0 = (if b.slt c then 1 else 0) ∧
                 a_1 = (if c.slt b then 1 else 0) ∧
                 a_2 = 0 ∧ a_3 = 0
        | 265 => a_0 = (if b.ult c then 1 else 0) ∧
                 a_1 = (if c.ult b then 1 else 0) ∧
                 a_2 = 0 ∧ a_3 = 0
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

          Layout (from `Extraction/CpuChip.lean:462-463` at the tag `pico-v3-before-cpu`, 2.x):
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

  end SharedBuses

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
        pc % 4 = 0 ∧ pc < Transpiler.code_address_bound ∧
        (.some ⟨ data, props ⟩ = Transpiler.transpile_op instruction entry.multiplicity pc) ∧
        (entry = ProgramBusEntry.deserialise data) ∧
        props

    /-! ### From a Program message back to its instruction

        `ProgramBusEntry.inversion` takes the two facts `operand_properties` gives after
        unpacking (the decoder produced `data` for `instr` at `pc`, and the message is `data`)
        and returns every fact below at once, with one case split over the decoder. The lemmas
        after it pick out one group each. The facts that depend on the opcode are stated as
        functions of `entry.opcode.val`: with `h : entry.opcode = k`, `rw [h]` turns them into
        the facts for `k` (see the `example` at the end of the section). They are stated on the
        message, not on a chip's columns. -/

    section Inversion

    open Transpiler

    /-- A load's row, with its opcode read off `is_unsigned` and the width. -/
    lemma transpile_op_load_row {imm : BitVec 12} {rs1 rd : regidx} {u : Bool} {wd : word_width}
        {m : FKB} {pc : ℕ} {data : FKB × Vector FKB 26} {props : Prop}
        (h : Transpiler.transpile_op (.LOAD (imm, rs1, rd, u, wd)) m pc = some (data, props)) :
        ∃ opc : FKB,
          ((u = false ∧ wd = 1 ∧ opc = 10) ∨ (u = true ∧ wd = 1 ∧ opc = 13) ∨
           (u = false ∧ wd = 2 ∧ opc = 11) ∨ (u = true ∧ wd = 2 ∧ opc = 14) ∨
           (u = false ∧ wd = 4 ∧ opc = 12) ∨ (u = true ∧ wd = 4 ∧ opc = 45) ∨
           (u = false ∧ wd = 8 ∧ opc = 46)) ∧
          data = (m, #v[pc_lo pc, pc_hi pc, opc, opc, reg_to_KB rd, reg_to_KB rs1, 0, 0,
                        (imm_operand imm true)[0], (imm_operand imm true)[1],
                        (imm_operand imm true)[2],
                        (if rd == regidx.Regidx 0 then 1 else 0), 0, 1, 0, 1, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, pc_carry pc]) := by
      simp only [Transpiler.transpile_op] at h
      split at h
      · simp at h
      · rename_i opc hopc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨ _, ?_, h.1.symm ⟩
        clear h
        split at hopc <;> simp_all

    /-- A store's row, with its opcode read off the width. -/
    lemma transpile_op_store_row {imm : BitVec 12} {rs2 rs1 : regidx} {wd : word_width}
        {m : FKB} {pc : ℕ} {data : FKB × Vector FKB 26} {props : Prop}
        (h : Transpiler.transpile_op (.STORE (imm, rs2, rs1, wd)) m pc = some (data, props)) :
        ∃ opc : FKB,
          ((wd = 1 ∧ opc = 15) ∨ (wd = 2 ∧ opc = 16) ∨ (wd = 4 ∧ opc = 17) ∨
           (wd = 8 ∧ opc = 47)) ∧
          data = (m, #v[pc_lo pc, pc_hi pc, opc, opc, reg_to_KB rs2, reg_to_KB rs1, 0, 0,
                        (imm_operand imm true)[0], (imm_operand imm true)[1],
                        (imm_operand imm true)[2],
                        (if rs2 == regidx.Regidx 0 then 1 else 0), 0, 1, 0, 1, 1,
                        0, 0, 0, 0, 0, 0, 0, 0, pc_carry pc]) := by
      simp only [Transpiler.transpile_op] at h
      split at h
      · simp at h
      · rename_i opc hopc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨ _, ?_, h.1.symm ⟩
        clear h
        split at hopc <;> simp_all

    /-- The instruction a message with opcode `k` was decoded from. Where two instruction
        shapes share an opcode (an ALU operation with a register or an immediate third operand,
        and opcode 0) the immediate flags tell them apart, except `LUI` and `AUIPC`: they give
        rows of the same shape, so opcode 0 with both flags is one of the two, each with its
        operand shape. `False` for an opcode the decoder never produces. Against 2.x: there is
        no opcode 27 (`AUIPC`), and opcode 28 is `ECALL`. -/
    def ProgramBusEntry.decoded_from (entry : ProgramBusEntry FKB) (instr : instruction)
        (pc : ℕ) : ℕ → Prop
      -- ALU
      | 0 =>
        (entry.imm_b = 0 ∧ entry.imm_c = 0 ∧
          ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .ADD)) ∨
        (entry.imm_b = 0 ∧ entry.imm_c = 1 ∧
          ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ADDI)) ∨
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
            entry.c_0 = pc_lo pc ∧ entry.c_1 = pc_hi pc ∧ entry.c_sign = 0))
      | 1 => entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SUB)
      | 2 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .XOR)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .XORI))
      | 3 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .OR)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ORI))
      | 4 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .AND)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .ANDI))
      | 5 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SLL)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SLLI))
      | 6 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SRL)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SRLI))
      | 7 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SRA)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIOP (imm, rs1, rd, .SRAI))
      | 8 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SLT)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .SLTI))
      | 9 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPE (rs2, rs1, rd, .SLTU)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ITYPE (imm, rs1, rd, .SLTIU))
      -- Loads and stores
      | 10 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 1)
      | 11 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 2)
      | 12 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 4)
      | 13 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 1)
      | 14 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 2)
      | 45 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, true, 4)
      | 46 => ∃ imm rs1 rd, instr = .LOAD (imm, rs1, rd, false, 8)
      | 15 => ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 1)
      | 16 => ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 2)
      | 17 => ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 4)
      | 47 => ∃ imm rs2 rs1, instr = .STORE (imm, rs2, rs1, 8)
      -- Branches and jumps
      | 18 => ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BEQ)
      | 19 => ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BNE)
      | 20 => ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BLT)
      | 21 => ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BGE)
      | 22 => ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BLTU)
      | 23 => ∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BGEU)
      | 24 => ∃ imm rd, instr = .JAL (imm, rd)
      | 25 => ∃ imm rs1 rd, instr = .JALR (imm, rs1, rd)
      | 28 => instr = .ECALL ()
      -- Multiply, divide, remainder. Sail's last `DIV` / `REM` field is `is_unsigned`.
      | 30 => ∃ rs2 rs1 rd sl sr,
          instr = .MUL (rs2, rs1, rd, { result_part := .Low, signed_rs1 := sl, signed_rs2 := sr })
      | 31 => ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed })
      | 32 => ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })
      | 33 => ∃ rs2 rs1 rd, instr = .MUL (rs2, rs1, rd,
          { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned })
      | 34 => ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, false)
      | 35 => ∃ rs2 rs1 rd, instr = .DIV (rs2, rs1, rd, true)
      | 36 => ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, false)
      | 37 => ∃ rs2 rs1 rd, instr = .REM (rs2, rs1, rd, true)
      -- Word ALU
      | 40 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .ADDW)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .ADDIW (imm, rs1, rd))
      | 41 => entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SUBW)
      | 42 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SLLW)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIWOP (imm, rs1, rd, .SLLIW))
      | 43 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SRLW)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIWOP (imm, rs1, rd, .SRLIW))
      | 44 =>
        (entry.imm_c = 0 ∧ ∃ rs2 rs1 rd, instr = .RTYPEW (rs2, rs1, rd, .SRAW)) ∨
        (entry.imm_c = 1 ∧ ∃ imm rs1 rd, instr = .SHIFTIWOP (imm, rs1, rd, .SRAIW))
      -- Word multiply, divide, remainder
      | 48 => ∃ rs2 rs1 rd, instr = .MULW (rs2, rs1, rd)
      | 49 => ∃ rs2 rs1 rd, instr = .DIVW (rs2, rs1, rd, false)
      | 50 => ∃ rs2 rs1 rd, instr = .DIVW (rs2, rs1, rd, true)
      | 51 => ∃ rs2 rs1 rd, instr = .REMW (rs2, rs1, rd, false)
      | 52 => ∃ rs2 rs1 rd, instr = .REMW (rs2, rs1, rd, true)
      | _ => False

    /-- A message's 11 class selectors, in field order: `is_ecall`, `is_memory`, `is_store`,
        `is_beq`, `is_bne`, `is_blt`, `is_bge`, `is_bltu`, `is_bgeu`, `is_jalr`, `is_jal`. -/
    def ProgramBusEntry.class_selectors (entry : ProgramBusEntry FKB) : Vector FKB 11 :=
      #v[entry.is_ecall, entry.is_memory, entry.is_store, entry.is_beq, entry.is_bne,
         entry.is_blt, entry.is_bge, entry.is_bltu, entry.is_bgeu, entry.is_jalr, entry.is_jal]

    /-- The class selectors the decoder sets for each opcode, in the order of
        `ProgramBusEntry.class_selectors` (`opcode_selector/columns.rs:66-104`): `is_memory` for
        a load, `is_memory` and `is_store` for a store, the branch's own selector, `is_jal`,
        `is_jalr`, `is_ecall`, and none for every other opcode. -/
    def class_selectors_of_opcode : ℕ → Vector FKB 11
      | 10 | 11 | 12 | 13 | 14 | 45 | 46 => #v[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      | 15 | 16 | 17 | 47 => #v[0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
      | 18 => #v[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
      | 19 => #v[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
      | 20 => #v[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
      | 21 => #v[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
      | 22 => #v[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
      | 23 => #v[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
      | 25 => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
      | 24 => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
      | 28 => #v[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      | _ => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

    /-- `imm_b` as the opcode fixes it: 1 for `JAL`, 0 for every other opcode except 0, where
        it tells `LUI` and `AUIPC` (1) from `ADD` and `ADDI` (0), so `none`. -/
    def imm_b_of_opcode : ℕ → Option FKB
      | 0 => none
      | 24 => some 1
      | _ => some 0

    /-- `imm_c` as the opcode fixes it: 1 for loads, stores, branches and jumps; `none` for an
        ALU opcode whose third operand is a register or an immediate; 0 for every other
        opcode. -/
    def imm_c_of_opcode : ℕ → Option FKB
      | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 40 | 42 | 43 | 44 => none
      | 10 | 11 | 12 | 13 | 14 | 45 | 46 | 15 | 16 | 17 | 47 => some 1
      | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 => some 1
      | _ => some 0

    /-- Everything a decoded Program message says about itself and its instruction. -/
    structure ProgramBusEntry.RowFacts (entry : ProgramBusEntry FKB) (instr : instruction)
        (pc : ℕ) : Prop where
      /-- The pc fields are the two pieces of the instruction's address. -/
      pc_0 : entry.pc_0 = pc_lo pc
      pc_1 : entry.pc_1 = pc_hi pc
      /-- `pc_carry` is that address's carry. -/
      pc_carry : entry.pc_carry = Transpiler.pc_carry pc
      /-- The two opcode fields are equal. -/
      opcode' : entry.opcode' = entry.opcode
      /-- The opcode is one the decoder produces: 0 to 25, 28, 30 to 37, or 40 to 52. -/
      opcode_range : entry.opcode.val ≤ 25 ∨ entry.opcode.val = 28 ∨
        (30 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 37) ∨
        (40 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 52)
      /-- The instruction, by opcode. -/
      decoded_from : entry.decoded_from instr pc entry.opcode.val
      /-- The class selectors, by opcode. -/
      class_selectors : entry.class_selectors = class_selectors_of_opcode entry.opcode.val
      /-- The immediate flags, where the opcode fixes them. -/
      imm_b : ∀ f, imm_b_of_opcode entry.opcode.val = some f → entry.imm_b = f
      imm_c : ∀ f, imm_c_of_opcode entry.opcode.val = some f → entry.imm_c = f
      /-- Every flag and selector is 0 or 1, at most one instruction class is set, and a store
          is a memory instruction. -/
      one_hot :
        (entry.imm_b = 0 ∨ entry.imm_b = 1) ∧ (entry.imm_c = 0 ∨ entry.imm_c = 1) ∧
        (entry.is_ecall = 0 ∨ entry.is_ecall = 1) ∧
        (entry.is_memory = 0 ∨ entry.is_memory = 1) ∧
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
      /-- `op_a` is a register index and `op_a_0` is `[op_a = 0]`. -/
      op_a : entry.op_a.val < 32
      op_a_0 : entry.op_a_0 = if entry.op_a = 0 then 1 else 0
      /-- An operand whose immediate flag is 0 is a register index (second piece and sign 0). -/
      b_register : entry.imm_b = 0 → entry.b_0.val < 32 ∧ entry.b_1 = 0 ∧ entry.b_sign = 0
      c_register : entry.imm_c = 0 → entry.c_0.val < 32 ∧ entry.c_1 = 0 ∧ entry.c_sign = 0
      /-- Every operand piece is 16-bit and every sign is 0 or 1. -/
      b_pieces : entry.b_0.val < 65536 ∧ entry.b_1.val < 65536 ∧
        (entry.b_sign = 0 ∨ entry.b_sign = 1)
      c_pieces : entry.c_0.val < 65536 ∧ entry.c_1.val < 65536 ∧
        (entry.c_sign = 0 ∨ entry.c_sign = 1)

    /-- A message whose 26 fields are written out, as a structure: rewriting with this once
        keeps a proof from carrying 26 copies of the row. -/
    lemma ProgramBusEntry.deserialise_vec
        (m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
           a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 : FKB) :
        ProgramBusEntry.deserialise
          (m, #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
                 a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25]) =
          ⟨ m, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
               a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25 ⟩ := rfl

    /-- Proves `RowFacts` for one row whose 26 fields are written out. -/
    local macro "row_facts" : tactic => `(tactic| (
      rw [ProgramBusEntry.deserialise_vec]
      refine ⟨ ?pc_0, ?pc_1, ?pc_carry, ?opcode', ?opcode_range, ?decoded_from,
               ?class_selectors, ?imm_b, ?imm_c, ?one_hot, ?op_a, ?op_a_0, ?b_register,
               ?c_register, ?b_pieces, ?c_pieces ⟩
      all_goals dsimp only [ProgramBusEntry.class_selectors]
      case decoded_from => simp [ProgramBusEntry.decoded_from]
      case class_selectors => simp only [class_selectors_of_opcode]
      case op_a_0 => first | exact reg_is_x0 _ | decide
      case imm_b => intro f h; cases h <;> rfl
      case imm_c => intro f h; cases h <;> rfl
      -- The rest are closed facts about literals, or bounds on a register index, an operand
      -- piece or a pc piece.
      all_goals first
        | decide
        | exact val_reg_to_KB_lt _
        | exact fun _ => ⟨ val_reg_to_KB_lt _, rfl, rfl ⟩
        | exact fun h => absurd h (by decide)
        | exact imm_operand_limbs _ _
        | exact ⟨ val_reg_to_KB_lt_of_le _ (by decide), by decide, Or.inl rfl ⟩
        | (simp [val_reg_to_KB_lt, val_reg_to_KB_lt_of_le, imm_operand_limbs] <;> omega)))

    /-- A decoded Program message satisfies `RowFacts`. This is the only proof that splits over
        the decoder's cases: one goal per Sail constructor and operation it gives a row, with
        the message's 26 fields written out. -/
    theorem ProgramBusEntry.inversion
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.RowFacts instr pc
    := by
      obtain ⟨ m, v ⟩ := data
      subst h_deser
      simp only [ProgramBusEntry.deserialise] at h_trans
      cases instr
      case' RTYPE x => obtain ⟨ rs2, rs1, rd, op ⟩ := x; cases op
      case' RTYPEW x => obtain ⟨ rs2, rs1, rd, op ⟩ := x; cases op
      case' ITYPE x => obtain ⟨ imm, rs1, rd, op ⟩ := x; cases op
      case' ADDIW x => obtain ⟨ imm, rs1, rd ⟩ := x
      case' SHIFTIOP x => obtain ⟨ imm, rs1, rd, op ⟩ := x; cases op
      case' SHIFTIWOP x => obtain ⟨ imm, rs1, rd, op ⟩ := x; cases op
      -- Loads and stores: the opcode is computed by a `match`, so the helpers above give the
      -- row, and these cases are finished here.
      case' LOAD x =>
        obtain ⟨ imm, rs1, rd, u, wd ⟩ := x
        obtain ⟨ opc, h_opc, h_v ⟩ := transpile_op_load_row h_trans.symm
        clear h_trans
        simp only [Prod.mk.injEq, true_and] at h_v
        subst h_v
        rcases h_opc with ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ |
          ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl ⟩ |
          ⟨ rfl, rfl, rfl ⟩ <;> row_facts
      case' STORE x =>
        obtain ⟨ imm, rs2, rs1, wd ⟩ := x
        obtain ⟨ opc, h_opc, h_v ⟩ := transpile_op_store_row h_trans.symm
        clear h_trans
        simp only [Prod.mk.injEq, true_and] at h_v
        subst h_v
        rcases h_opc with ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ |
          ⟨ rfl, rfl ⟩ <;> row_facts
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
      -- Unfolding the decoder closes every case it gives no row (`some _ = none`) and leaves
      -- `v = row ∧ props = side conditions` in the others.
      all_goals simp [Transpiler.transpile_op, opcode_of_rop, opcode_of_ropw, opcode_of_iop,
                      opcode_of_sop, opcode_of_sopw, opcode_of_bop, -Vector.eq_mk] at h_trans
      all_goals (obtain ⟨ h_v, - ⟩ := h_trans; subst h_v)
      all_goals row_facts

    /-- The message's pc fields are the two pieces of the instruction's address, and its
        `pc_carry` is that address's carry. -/
    lemma ProgramBusEntry.inversion_pc
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.pc_0 = pc_lo pc ∧ entry.pc_1 = pc_hi pc ∧ entry.pc_carry = Transpiler.pc_carry pc
    :=
      have h := ProgramBusEntry.inversion h_trans h_deser
      ⟨ h.pc_0, h.pc_1, h.pc_carry ⟩

    /-- With the Program promise's conditions on the address (4-aligned, below `0x7800_0000`):
        the low pc piece is 16-bit and 4-aligned, the high piece is at most `0x77FF`, the two
        pieces make the address, and `pc_carry` is `[pc[0] >= 0xFFFC]`. -/
    lemma ProgramBusEntry.inversion_pc_facts
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
      (h_al : pc % 4 = 0) (h_lt : pc < Transpiler.code_address_bound)
    :
      entry.pc_0.val < 65536 ∧ entry.pc_1.val ≤ 0x77FF ∧ entry.pc_0.val % 4 = 0 ∧
      entry.pc_0.val + 65536 * entry.pc_1.val = pc ∧
      entry.pc_carry = (if 0xFFFC ≤ entry.pc_0.val then 1 else 0)
    := by
      obtain ⟨ e0, e1, e25 ⟩ := ProgramBusEntry.inversion_pc h_trans h_deser
      obtain ⟨ hlo, hhi, hsum ⟩ := Transpiler.pc_pieces h_lt
      rw [e0, e1, e25, Transpiler.pc_carry_eq]
      exact ⟨ hlo, hhi, Transpiler.pc_lo_mod_four h_al, hsum, rfl ⟩

    /-- The two opcode fields are equal, and the opcode is one the decoder produces: 0 to 25,
        28, 30 to 37, or 40 to 52. There is no 26, 27, 29, 38 or 39; in particular no row has
        the `AUIPC` opcode 27, which Pico v3.1.1 no longer emits. -/
    lemma ProgramBusEntry.inversion_opcode_bounds
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.opcode' = entry.opcode ∧
      (entry.opcode.val ≤ 25 ∨ entry.opcode.val = 28 ∨
       (30 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 37) ∨
       (40 ≤ entry.opcode.val ∧ entry.opcode.val ≤ 52))
    :=
      have h := ProgramBusEntry.inversion h_trans h_deser
      ⟨ h.opcode', h.opcode_range ⟩

    /-- The Sail instruction the row was decoded from, by opcode (`decoded_from`). -/
    lemma ProgramBusEntry.operand_properties_inversion
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.decoded_from instr pc entry.opcode.val
    :=
      (ProgramBusEntry.inversion h_trans h_deser).decoded_from

    /-- The class selectors, and the immediate flags where the opcode fixes them, by opcode.
        Where two instruction shapes share an opcode the flag that varies is `none`; its value
        is in `operand_properties_inversion`. -/
    lemma ProgramBusEntry.inversion_opcode_selectors
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.class_selectors = class_selectors_of_opcode entry.opcode.val ∧
      (∀ f, imm_b_of_opcode entry.opcode.val = some f → entry.imm_b = f) ∧
      (∀ f, imm_c_of_opcode entry.opcode.val = some f → entry.imm_c = f)
    :=
      have h := ProgramBusEntry.inversion h_trans h_deser
      ⟨ h.class_selectors, h.imm_b, h.imm_c ⟩

    /-- Every flag and selector is 0 or 1, at most one instruction class is set, and a store
        is a memory instruction. -/
    lemma ProgramBusEntry.inversion_selectors_one_hot
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      (entry.imm_b = 0 ∨ entry.imm_b = 1) ∧ (entry.imm_c = 0 ∨ entry.imm_c = 1) ∧
      (entry.is_ecall = 0 ∨ entry.is_ecall = 1) ∧
      (entry.is_memory = 0 ∨ entry.is_memory = 1) ∧
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
    :=
      (ProgramBusEntry.inversion h_trans h_deser).one_hot

    /-- Operand facts: `op_a` is a register index and `op_a_0` is `[op_a = 0]`; an operand
        whose immediate flag is 0 is a register index (second piece and sign 0); every piece
        is 16-bit and every sign is 0 or 1. -/
    lemma ProgramBusEntry.inversion_operands
      { entry : ProgramBusEntry FKB }
      (h_trans : .some ⟨ data, props ⟩ =
        Transpiler.transpile_op instr entry.multiplicity pc)
      (h_deser : entry = ProgramBusEntry.deserialise data)
    :
      entry.op_a.val < 32 ∧ entry.op_a_0 = (if entry.op_a = 0 then 1 else 0) ∧
      (entry.imm_b = 0 → entry.b_0.val < 32 ∧ entry.b_1 = 0 ∧ entry.b_sign = 0) ∧
      (entry.imm_c = 0 → entry.c_0.val < 32 ∧ entry.c_1 = 0 ∧ entry.c_sign = 0) ∧
      entry.b_0.val < 65536 ∧ entry.b_1.val < 65536 ∧ (entry.b_sign = 0 ∨ entry.b_sign = 1) ∧
      entry.c_0.val < 65536 ∧ entry.c_1.val < 65536 ∧ (entry.c_sign = 0 ∨ entry.c_sign = 1)
    :=
      have h := ProgramBusEntry.inversion h_trans h_deser
      ⟨ h.op_a, h.op_a_0, h.b_register, h.c_register, h.b_pieces.1, h.b_pieces.2.1,
        h.b_pieces.2.2, h.c_pieces.1, h.c_pieces.2.1, h.c_pieces.2.2 ⟩

    /-- How a later proof reads the opcode facts: rewrite with the opcode it has, and the
        functions of the opcode reduce to that opcode's facts. -/
    example { entry : ProgramBusEntry FKB }
        (h_trans : .some ⟨ data, props ⟩ =
          Transpiler.transpile_op instr entry.multiplicity pc)
        (h_deser : entry = ProgramBusEntry.deserialise data)
        (h_opc : entry.opcode = 18) :
        (∃ imm rs2 rs1, instr = .BTYPE (imm, rs2, rs1, .BEQ)) ∧ entry.is_beq = 1 ∧
        entry.imm_c = 1 := by
      have h := ProgramBusEntry.inversion h_trans h_deser
      have h_instr := h.decoded_from
      have h_sel := h.class_selectors
      have h_c := h.imm_c
      rw [h_opc] at h_instr h_sel h_c
      exact ⟨ h_instr, congrArg (·[3]) h_sel, h_c 1 rfl ⟩

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
        no longer a selector: each memory chip derives it from the opcode, through the one-hot
        flags of `eval_instruction_flags` (v3.2.0: `riscv_memory/read_write/constraints.rs:165-210`,
        called by the unaligned chip at `riscv_memory/unaligned/constraints.rs:44-45`). `a` is
        the value of register `a` after the row: the loaded value for a load, the stored value
        for a store. -/
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

    /-- What the memory chips guarantee, which the CPU chip assumes when it sends.

        Two chips receive the memory dispatch at the pin, `MemoryReadWriteChip` and, since
        v3.1.2, `MemoryUnalignedChip`; either may take any load or store, so this states only
        what both prove. Lines below are in `vm/src/chips/chips/riscv_memory/` at v3.2.0:
        `rw` is `read_write/constraints.rs`, `un` is `unaligned/constraints.rs`. Both receive
        the same 17-field message (`rw:49-84`, `un:44-63`).

        - A load's value has four 16-bit pieces. `rw`: the pieces are the memory value's
          (`:417-442`), which the memory argument's promise bounds (`StateBusEntry`,
          this file), or a byte split by the U8Range check at `:535-542`, plus the
          `0xFF00` / `0xFFFF` sign fill. `un`: every piece is two of the bytes the access
          reads, selected at `:216-227` and placed at `:232-250`, plus the same fill; those
          bytes are U8Range-checked (`:185-205`), the first dword's on every row and the second
          dword's on a row whose access crosses into it (the check's count is `cross`,
          `:194-199`). On another row the second dword's bytes are unchecked, and meet only zero
          coefficients. Neither chip constrains the value of a load into `x0`; there the
          clause holds because the CPU sends zero (`MemoryBus.externals`). So the clause rests on
          each chip's constraints together with the memory argument's promise and the CPU's
          duty as a sender, not on the constraints alone.
        - `2^16 ≤ addr < 2^32` for `addr = b + c`. Both chips add `b + c` with a carry chain
          whose third and fourth result pieces are zero (`rw:242-253`, `un:70-81`), bound the
          two low pieces (`rw:259-266, 301-309`, `un:82-89, 109-116`), and require the second
          piece to be non-zero (`rw:271-274`, `un:90-93`).
        - When `op_a_0 = 0`, a load's value is the sign or zero extension its opcode names.
          `rw:417-442` and `un:232-250` set each piece of `a` from the bytes read, gated by
          `op_a_0`, which both make boolean (`rw:497`, `un:251`); the sign bit is fixed by a
          U16Range check (`rw:451-494`, `un:256-271`).

        No alignment clause: `rw:311-325` refuses a misaligned access, but `un` takes any byte
        offset (`un:100-108`). Nothing is promised about which memory a load reads, about the
        `chunk` and `clk` fields, or that a store misses the program's code. -/
    def MemoryBus.Spec
      (mem_opcode a_0 a_1 a_2 a_3 b_0 b_1 b_2 b_3 c_0 c_1 c_2 c_3 op_a_0 : FKB) : Prop :=
      let a := U64w.toBV #v[a_0, a_1, a_2, a_3]
      let b := U64w.toBV #v[b_0, b_1, b_2, b_3]
      let c := U64w.toBV #v[c_0, c_1, c_2, c_3]
      let addr := (b + c).toNat
      ((mem_opcode.val ≤ 14 ∨ mem_opcode.val = 45 ∨ mem_opcode.val = 46) →
          a_0.val < 65536 ∧ a_1.val < 65536 ∧ a_2.val < 65536 ∧ a_3.val < 65536) ∧
      65536 ≤ addr ∧ addr < 2 ^ 32 ∧
      (mem_opcode = 10 → op_a_0 = 0 → a = BitVec.signExtend 64 (a.truncate 8)) ∧   -- LB
      (mem_opcode = 11 → op_a_0 = 0 → a = BitVec.signExtend 64 (a.truncate 16)) ∧  -- LH
      (mem_opcode = 12 → op_a_0 = 0 → a = BitVec.signExtend 64 (a.truncate 32)) ∧  -- LW
      (mem_opcode = 13 → op_a_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 8)) ∧   -- LBU
      (mem_opcode = 14 → op_a_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 16)) ∧  -- LHU
      (mem_opcode = 45 → op_a_0 = 0 → a = BitVec.zeroExtend 64 (a.truncate 32))    -- LWU

    /-- What the CPU chip guarantees when it sends, which both memory chips may assume.

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

  section CodeRangeBus

    variable (F : Type) [Field F]

    /-- Code-range entry, payload size 4: `[code_start(2), code_end(2)]`, each end of the
        program's code as two 16-bit pieces (`gadgets/code_range.rs`, `code_range_message`). A
        store row of either memory chip sends it with multiplicity `is_store`, and every
        precompile chip sends it for what its event writes (`code_range.rs:1-11`,
        `CodeRangeCols::eval`, the `looking` call); the Program table answers it with a
        prover-chosen multiplicity (`riscv_program/constraints.rs:58-66`, `columns.rs:46-52`).

        Multiplicities summed onto one row. Trace generation puts the record's whole count of
        code-range lookups, one per store and one per precompile event
        (`code_range.rs:71-73`), on Program row 0 (`riscv_program/columns.rs:48-51`,
        `traces.rs:178-180`). With `N` such lookups in a chunk, the table answers once at
        multiplicity `-N`. `wf_assert_cond` holds only at `-1` (`Fundamentals/Interaction.lean`),
        so for `N ≠ 1` a Program-chip `wf_asrt` would ask nothing of this answer, while each
        sender assumes `CodeRangeBus.Spec` at `+1`. The two sides line up only through Pico's
        LogUp argument, which no Lean theorem states (`SOUNDNESS.md`, A4); a composition
        theorem has to treat a multiplicity summed onto one row. Here the promise holds whatever
        the multiplicity, since every Program row carries the same preprocessed range. -/
    structure CodeRangeBusEntry where
      multiplicity : F
      code_start_0 : F
      code_start_1 : F
      code_end_0 : F
      code_end_1 : F
    deriving BEq, DecidableEq, Inhabited

    @[simp, grind]
    def CodeRangeBusEntry.deserialise
      (entry : FKB × Vector FKB 4)
    : CodeRangeBusEntry FKB :=
      {
        multiplicity := entry.1,
        code_start_0 := entry.2[0],
        code_start_1 := entry.2[1],
        code_end_0 := entry.2[2],
        code_end_1 := entry.2[3],
      }

    /-- What the Program table delivers: four 16-bit pieces.

        The Program table answers with its preprocessed columns `code_start` and `code_end`
        (`riscv_program/constraints.rs:58-66`, `columns.rs:36-40`). Pico fills them at keygen
        with `limbs(value) = [value as u16, (value >> 16) as u16]` of the program's code range,
        the same on every row (`riscv_program/traces.rs:132-136`), so each field is below
        2^16. The message being the program's own code range is not stated here: no Lean
        statement names that range yet. -/
    def CodeRangeBus.Spec (code_start_0 code_start_1 code_end_0 code_end_1 : FKB) : Prop :=
      code_start_0.val < 65536 ∧ code_start_1.val < 65536 ∧
      code_end_0.val < 65536 ∧ code_end_1.val < 65536

    @[simp, grind]
    instance CodeRangeBusEntryInstance
    : BusEntry FKB (CodeRangeBusEntry FKB) :=
    {
        multiplicity := fun entry => entry.1,

        data_length := 4,
        data := fun ⟨_, code_start_0, code_start_1, code_end_0, code_end_1⟩ =>
                  #v[code_start_0, code_start_1, code_end_0, code_end_1]

        axioms := fun _ => True

        -- A store row asserts nothing to the Program table.
        externals := fun _ => True

        wf_properties := fun ⟨_, code_start_0, code_start_1, code_end_0, code_end_1⟩ =>
          CodeRangeBus.Spec code_start_0 code_start_1 code_end_0 code_end_1

        deserialise := CodeRangeBusEntry.deserialise

        inv_deser_ser := by simp [CodeRangeBusEntry.deserialise]
        inv_ser_deser := by
          simp_all [CodeRangeBusEntry.deserialise]
          intro b; cases b
          simp_all; grind
    }

  end CodeRangeBus

  section ChipRows

    /-- A row's messages, sorted by contract. `CodeRange` is last and empty by default, so a row
        written without it, as every CPU-chip row is, has none. The five checks below
        (`bus_row_wf_asm` and its siblings) cover the other five lists only; `CodeRange` has its
        own (`bus_row_code_range_wf_asm` and the rest). The checks over the whole row, all six
        lists, are `bus_row_all_wf_asm` and its siblings: a theorem about a row that may carry
        code-range messages states its bus duties with those. -/
    structure BusRow where
      Program : List (ProgramBusEntry FKB)
      ALU : List (ALUBusEntry FKB)
      Byte : List (ByteBusEntry FKB)
      State : List (StateBusEntry FKB)
      Memory : List (MemoryBusEntry FKB)
      CodeRange : List (CodeRangeBusEntry FKB) := []

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

    /-- Concatenate two `BusRow`s pointwise on each of the six lists. A chip that embeds a gadget
        builds its row as the gadget's row followed by its own messages. -/
    def BusRow.append (r1 r2 : BusRow) : BusRow :=
      { Program   := r1.Program   ++ r2.Program
        ALU       := r1.ALU       ++ r2.ALU
        Byte      := r1.Byte      ++ r2.Byte
        State     := r1.State     ++ r2.State
        Memory    := r1.Memory    ++ r2.Memory
        CodeRange := r1.CodeRange ++ r2.CodeRange }

    instance : Append BusRow := ⟨BusRow.append⟩

    lemma BusRow.append_eq (r1 r2 : BusRow) :
      r1 ++ r2 =
        { Program   := r1.Program   ++ r2.Program
          ALU       := r1.ALU       ++ r2.ALU
          Byte      := r1.Byte      ++ r2.Byte
          State     := r1.State     ++ r2.State
          Memory    := r1.Memory    ++ r2.Memory
          CodeRange := r1.CodeRange ++ r2.CodeRange } := rfl

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
    @[simp] lemma BusRow.append_CodeRange (r1 r2 : BusRow) :
      (r1 ++ r2).CodeRange = r1.CodeRange ++ r2.CodeRange := rfl

    /-! Each of the four checks distributes over `++`, so a chip that embeds a gadget can split
        its bus duties into the gadget's and its own. -/

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

    /-! The five checks above leave out `CodeRange`; these are their counterparts for it. A row
        that sends code-range messages, as a store row of a memory chip does, takes both. They
        are kept apart because adding `CodeRange` to the five made the branch and jump
        equivalence proofs (`Equivalence/BType.lean`, `Jumps.lean`) time out, though no CPU row
        has a code-range message. -/

    def bus_row_code_range_axioms (row : BusRow) : Prop :=
      List.Forall id (row.CodeRange.map (BusEntry.axioms FKB))

    def bus_row_code_range_ext_asm (row : BusRow) : Prop :=
      List.Forall id (row.CodeRange.map (BusEntry.ext_assume FKB))

    def bus_row_code_range_ext_asrt (row : BusRow) : Prop :=
      List.Forall id (row.CodeRange.map (BusEntry.ext_assert FKB))

    def bus_row_code_range_wf_asm (row : BusRow) : Prop :=
      List.Forall id (row.CodeRange.map (BusEntry.wf_assume FKB))

    def bus_row_code_range_wf_asrt (row : BusRow) : Prop :=
      List.Forall id (row.CodeRange.map (BusEntry.wf_assert FKB))

    /-! The checks over the whole row: the five above together with their code-range
        counterparts. A theorem about a row that may carry code-range messages, as a store row
        of a memory chip does, states its bus duties with these, so none of the row's messages
        is left out. For a row with no code-range message, as every CPU-chip row is, each is the
        five-list check (`bus_row_all_wf_asm_iff` and its siblings). -/

    def bus_row_all_axioms (row : BusRow) : Prop :=
      bus_row_axioms row ∧ bus_row_code_range_axioms row

    def bus_row_all_ext_asm (row : BusRow) : Prop :=
      bus_row_ext_asm row ∧ bus_row_code_range_ext_asm row

    def bus_row_all_ext_asrt (row : BusRow) : Prop :=
      bus_row_ext_asrt row ∧ bus_row_code_range_ext_asrt row

    def bus_row_all_wf_asm (row : BusRow) : Prop :=
      bus_row_wf_asm row ∧ bus_row_code_range_wf_asm row

    def bus_row_all_wf_asrt (row : BusRow) : Prop :=
      bus_row_wf_asrt row ∧ bus_row_code_range_wf_asrt row

    theorem bus_row_all_axioms_iff {row : BusRow} (h : row.CodeRange = []) :
        bus_row_all_axioms row ↔ bus_row_axioms row := by
      simp [bus_row_all_axioms, bus_row_code_range_axioms, h]

    theorem bus_row_all_ext_asm_iff {row : BusRow} (h : row.CodeRange = []) :
        bus_row_all_ext_asm row ↔ bus_row_ext_asm row := by
      simp [bus_row_all_ext_asm, bus_row_code_range_ext_asm, h]

    theorem bus_row_all_ext_asrt_iff {row : BusRow} (h : row.CodeRange = []) :
        bus_row_all_ext_asrt row ↔ bus_row_ext_asrt row := by
      simp [bus_row_all_ext_asrt, bus_row_code_range_ext_asrt, h]

    theorem bus_row_all_wf_asm_iff {row : BusRow} (h : row.CodeRange = []) :
        bus_row_all_wf_asm row ↔ bus_row_wf_asm row := by
      simp [bus_row_all_wf_asm, bus_row_code_range_wf_asm, h]

    theorem bus_row_all_wf_asrt_iff {row : BusRow} (h : row.CodeRange = []) :
        bus_row_all_wf_asrt row ↔ bus_row_wf_asrt row := by
      simp [bus_row_all_wf_asrt, bus_row_code_range_wf_asrt, h]

    /-- Sort a raw row of messages (multiplicity, `[tag, ...data]`) into a `BusRow`. Tags are
        Pico's `LookupType` discriminants: Memory 1 (register access, 9 fields, and memory
        dispatch, 17 fields, told apart by length), Program 2 (instruction fetch, 26 fields, and
        code range, 4, told apart by length), Alu 4 (13), Byte 5 (5). Ecall 13 and every other
        tag are ignored. -/
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
            else (
              if _ : entry_data.length = 4 then
                let entry_data_vector : Vector FKB 4 := ⟨ entry_data.toArray, by simp; omega ⟩
                let bus_entry := CodeRangeBusEntry.deserialise (multiplicity, entry_data_vector)
                { result with CodeRange := result.CodeRange ++ [ bus_entry ] }
              else result
            )
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
        write per memory dispatch. Same as the 2.x `bus_operations` (`RVSail/Operations.lean` at
        `f4f9924`) except that the pc has two pieces and the access width and direction come from
        the opcode. -/
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

end RV64IM_Interactions
