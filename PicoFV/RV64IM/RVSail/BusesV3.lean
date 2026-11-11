import PicoFV.Fundamentals.Interaction

import PicoFV.RV64IM.Transpiler.TranspilerV3
import PicoFV.RV64IM.RVSail.Buses
import PicoFV.RV64IM.RVSail.Operations

set_option maxHeartbeats 1_000_000_000

/-! # Bus contracts of the Pico v3.1.1 CPU chip (draft)

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
    from the register file has four 16-bit pieces. The ALU contract gains the two comparison
    opcodes 264 and 265 (`SLT` / `SLTU` + 256) in a separate change; until then they fall into
    its `| _ => True` case.

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
        one such row (`riscv_cpu/constraints.rs:51-75`). -/
    def ProgramBusEntry.operand_properties (entry : ProgramBusEntry FKB) : Prop :=
      ∃ instruction pc data props,
        pc % 4 = 0 ∧ pc < Transpiler.V3.code_address_bound ∧
        (.some ⟨ data, props ⟩ = Transpiler.V3.transpile_op instruction entry.multiplicity pc) ∧
        (entry = ProgramBusEntry.deserialise data) ∧
        props

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
        (`riscv_memory/read_write/constraints.rs:157-191`). `a` is the value of register `a`
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
