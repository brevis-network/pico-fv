# Soundness

This document says what the proofs in this repository establish about Pico, and what a reader
has to trust on top of them. It follows the structure of EthLib's
[`SOUNDNESS.md`](https://github.com/ethereum/EthLib/blob/master/SOUNDNESS.md).

No formal verification is absolute. Each theorem links Lean definitions to a conclusion, and the
definitions are assumed to match something outside Lean: Pico's Rust constraints, the RISC-V
specification, and the way Pico's chips are composed. Each of those links is listed below.

The blocks marked *generated* are written by `scripts/fv-check/soundness_facts.py` from the
repository; CI fails when one is out of date. The rest of the text is reviewed by hand.

## What is proved

The theorems checked by `scripts/fv-check/check.sh` are listed in `scripts/fv-check/theorems.d/`,
with their statements in `signatures.txt`. They are of four kinds. Beside them, under the first, are
eighteen decoding lemmas, which show that on a real row of the class's opcode, with the immediate
flag that tells the class apart where an opcode is shared (`imm_c = 0` for `RTYPE` except `SUB` and
for `RTYPEW` except `SUBW`; `imm_c = 1` for `ITYPE`, `ADDIW` and the shift-immediate classes, with
`imm_b = 0` for `ADDI`; `imm_b = 1` for U-type), some instruction meets the decoded instruction
theorems' `h_decode` (for U-type, a `LUI` or an `AUIPC`, without saying which), listed with the
stores, the loads, the two register-register classes, the four register-immediate classes, the
multiply and divide classes, the branches, the jumps and the U-type theorems (A3). So is
`Equivalence.utype_row_cases`, which discharges the shape hypotheses of the unchecked column forms
of `LUI` and `AUIPC`, hypotheses no checked theorem takes.

- **Opcode equivalence** (`Equivalence.equivalence_<OP>`, the `equivalence_<OP>` names among those
  listed in `theorems.d/equivalence-*.txt`, one per RV64IM opcode except `ECALL`; the column forms
  `equivalence_<OP>_row` are not checked). For a CPU chip row that satisfies its extracted
  constraints, if the bus messages the row exchanges satisfy the bus assumptions below, then one
  step of the Sail RISC-V specification on that instruction gives the same post-state as the
  register and memory operations the row puts on the bus.

  <!-- generated: restored -->
  **All 62 of these theorems are checked**, in 13 files of `PicoFV/RV64IM/Equivalence/`:

  - `Addiw.lean`: `ADDIW`
  - `BType.lean`: `BEQ`, `BGE`, `BGEU`, `BLT`, `BLTU` and `BNE`
  - `DivFamily.lean`: `DIV`, `DIVU`, `DIVUW`, `DIVW`, `REM`, `REMU`, `REMUW` and `REMW`
  - `IType.lean`: `ADDI`, `ANDI`, `ORI`, `SLTI`, `SLTIU` and `XORI`
  - `Jumps.lean`: `JAL` and `JALR`
  - `Loads.lean`: `LB`, `LBU`, `LD`, `LH`, `LHU`, `LW` and `LWU`
  - `MulFamily.lean`: `MUL`, `MULH`, `MULHSU`, `MULHU` and `MULW`
  - `RTypeW.lean`: `ADDW`, `SLLW`, `SRAW`, `SRLW` and `SUBW`
  - `RType.lean`: `ADD`, `AND`, `OR`, `SLL`, `SLT`, `SLTU`, `SRA`, `SRL`, `SUB` and `XOR`
  - `ShiftIOp.lean`: `SLLI`, `SRAI` and `SRLI`
  - `ShiftIWOp.lean`: `SLLIW`, `SRAIW` and `SRLIW`
  - `Stores.lean`: `SB`, `SD`, `SH` and `SW`
  - `UType.lean`: `AUIPC` and `LUI`
  <!-- end generated -->

  The CPU chip moved to Pico v3.1.1, which is a rewrite of the chip rather than a patch: 58
  columns instead of 132, 65 constraints instead of 218 and 17 messages instead of 36. Its `Airs/`,
  `Constraints/` and interpretations files are at v3.1.1 here, and every instruction-theorem file
  is rewritten against them. Commit `353238a` is the last at which all 62 were checked against the
  2.x CPU extraction and the bus contract as it stood then (which already covered the
  branch-comparison opcodes). The 2.x interpretations file is unchanged from the tag
  `pico-v3-before-cpu` (`35259d8`) to that commit.

  `UType.lean`'s list also holds `Equivalence.utype_row_cases`, which is not an instruction
  theorem: `LUI` and `AUIPC` share a row shape at v3.1.1, and it shows that every row of that
  shape has the operand shape of one of the two column-form theorems (see A3).

  The lists of `Stores.lean`, `Loads.lean`, `RType.lean`, `RTypeW.lean`, `IType.lean`, `Addiw.lean`,
  `ShiftIOp.lean`, `ShiftIWOp.lean`, `MulFamily.lean`, `DivFamily.lean`, `BType.lean`, `Jumps.lean`
  and `UType.lean` also hold `Equivalence.store_decode_satisfiable`,
  `Equivalence.load_decode_satisfiable`, `Equivalence.rtype_decode_satisfiable`,
  `Equivalence.rtypew_decode_satisfiable`, `Equivalence.itype_decode_satisfiable`,
  `Equivalence.addiw_decode_satisfiable`, `Equivalence.shiftiop_decode_satisfiable`,
  `Equivalence.shiftiwop_decode_satisfiable`, `Equivalence.mul_decode_satisfiable`,
  `Equivalence.mulw_decode_satisfiable`, `Equivalence.div_decode_satisfiable`,
  `Equivalence.divw_decode_satisfiable`, `Equivalence.rem_decode_satisfiable`,
  `Equivalence.remw_decode_satisfiable`, `Equivalence.btype_decode_satisfiable`,
  `Equivalence.jal_decode_satisfiable`, `Equivalence.jalr_decode_satisfiable` and
  `Equivalence.utype_decode_satisfiable`, which are not instruction theorems either: the store,
  load, register-register, register-immediate, multiply, divide, branch, jump and U-type theorems
  take an instruction whose decoding is the row's Program message, and the eighteen show, from the
  row's Program promise (in `bus_row_wf_asm`), that every real row of a store, load, multiply,
  divide, remainder, branch or jump opcode, of a register-register opcode (with `imm_c = 0` where an
  immediate form shares the opcode), of a register-immediate opcode (with `imm_c = 1`, and
  `imm_b = 0` for `ADDI`), or of opcode 0 with `imm_b = 1` (U-type; an `ADD` or `ADDI` row has no
  U-type decoding), has one (see A3).

  Every v3.1.1 instruction theorem also assumes the chunk's final pc is a well-formed guest
  address (`Equivalence.pico_CpuChip_control_flow_assumptions`; see A3). Pico enforces that in
  the recursion circuit, not in a chip, so a v3.1.1 instruction theorem describes a chunk
  inside an accepted recursive proof rather than a chunk proof checked on its own.
- **Chip specifications** (`<Chip>.Spec.*`). For a row of a non-CPU chip that satisfies its
  extracted constraints, the bus messages it serves have the meaning the bus assumptions give them
  (for example, an ALU row really computes the operation it claims). Every chip that has a
  specification has it built; the checked list holds the two memory chips' at v3.2.0
  (`MemoryReadWriteChip.Spec.*`, `MemoryUnalignedChip.Spec.*`) and those of the ALU chips already
  at v3.1.1 (Add, Sub, Addw, Subw, Bitwise, Mul, Lt, DivRem, SLL, ShiftRight).

  Every chip specification is stated over the 3.x row: `RV64IM_Interactions.V3.BusRow`, its
  `deserialise_bus_row` and its checks `bus_row_ext_asm`, `bus_row_wf_asm`, `bus_row_ext_asrt` and
  `bus_row_wf_asrt` (`RVSail/BusesV3.lean`). The ALU chips (Add, Addw, Bitwise, DivRem, Lt, Mul,
  ShiftRight, SLL, Sub and Subw, with the gadgets they embed) were stated over the 2.x row
  (`RVSail/Buses.lean`) until they moved, with their statements unchanged but for the row's
  namespace. On their rows the two rows say the same. Their rows exchange only tag 4 (ALU, 13
  fields) and tag 5 (byte, 5 fields) messages: each chip receives one ALU message, its own
  operation, and sends byte messages, and DivRem also sends two ALU messages
  (`Extraction/DivRemChip.lean:871, 873`). Every entry of the interaction lists in
  `Extraction/AddChip.lean:31-39`, `AddwChip.lean:31-37`, `BitwiseChip.lean:29-45`,
  `DivRemChip.lean:715-955`, `LtChip.lean:85-91`, `MulChip.lean:121-191`,
  `ShiftRightChip.lean:149-173`, `SLLChip.lean:125-145`, `SubChip.lean:31-39` and
  `SubwChip.lean:31-37` has one of those two tags. Both deserialisers sort those two tags alike,
  into the same `ALUBusEntry` and `ByteBusEntry` lists (`RVSail/Buses.lean:1394-1405`,
  `RVSail/BusesV3.lean:1135-1146`), so on these rows Program, State, Memory and the 3.x row's
  `CodeRange` stay empty, and each check is the same condition on the ALU and byte entries in
  either row.

  The memory chips' say that a row receiving the memory dispatch meets the memory promise
  (`spec_LB` to `spec_SD`, one per opcode, and `wf_asrt`, which also gives each double word the
  row writes back 16-bit pieces: the unaligned chip writes back a second one when the access
  runs into it), and that a store row misses the code range it looks up
  (`store_misses_code_range`, through the gadget below). `aligned_address` says the double word
  the row reads and writes back is the one holding the access's first byte, and both chips' give
  its address piece by piece, its first two pieces (the third is 0) below `2^16`; the unaligned
  chip's also gives, on a row whose access crosses, the next double word's. Both chips' also say
  what a row does to memory
  (`dataFlow_of_allHold`): in a state that holds the double words the row reads from the memory
  argument, a load's value, at its width, is those double words' bytes from `b + c` on, and the
  row writes them back with a store's bytes in their place. The read/write chip reads one double
  word; the unaligned chip reads a second, the next one, on a row whose access crosses into it.
  That the double words read are the ones memory holds is the memory argument's promise, which
  stays on trust (A4).

  `DivRemChip`'s specifications are the one exception to "satisfies its extracted constraints":
  they are stated over the readable restatement `DivRemChip.ConstraintsAndBuses.AbsConstraints`
  and over `DivRemChip.Interactions.bus_row`, not over `DivRemChip.Extraction.allHold`. Two
  checked lemmas tie those to the extraction:
  `DivRemChip.ConstraintsAndBuses.allHold_iff_allHold_simplified`, which says the extracted
  constraints are exactly `AbsConstraints` plus the extracted interaction list, and
  `DivRemChip.Interactions.bus_row_equiv`, which says `bus_row` is that interaction list,
  entry for entry. All fourteen also assume `is_real = 1`, so they say nothing about a padding
  row, where the other ALU chips' specifications still hold.
- **The CPU chip's duties as a sender** (`CpuChip.Spec.ext_asrt` and
  `CpuChip.Spec.multiplicity_eq_zero_or_one`). For any row of the v3.1.1 CPU chip, real or
  padding, that satisfies its extracted constraints, and given only the Program table's promise
  about its instruction and the register file's promise about the values it reads
  (`CpuChip.Interpretations.bus_row_reads_asm`), every message the row sends with
  multiplicity 1 gives the receiver what the contract lets the receiver assume of a sender
  (`externals` in `RVSail/Buses.lean` and `RVSail/BusesV3.lean`):
  - the ALU dispatch carries a valid ALU opcode and 16-bit operand pieces;
  - the branch comparison carries opcode 264 or 265 and 16-bit operand pieces;
  - the memory dispatch carries a load or store opcode, `is_memory = 1`, 16-bit pieces for the
    base and the offset, 16-bit pieces for a store's value, and a zero value when the
    instruction's first register field is `x0`: the loaded value of a load into `x0`, the
    stored value of a store from `x0`.

  These three messages are sent 0 or 1 times (`multiplicity_eq_zero_or_one`), so the duties
  cover every one of them the receivers count. The hypothesis leaves out the promises of the
  ALU and memory chips that receive the three messages, so the theorem can be put together
  with those chips' theorems without assuming what they prove. It needs neither the
  whole-trace assumption nor the next row. The Program, byte-range and register-access
  messages ask nothing of the sender, and the Ecall message has no contract. The memory chip's
  address addition `b + c` is exact only for 16-bit pieces, which it takes from the sender, so
  the meaning of the load and store theorems rests on this theorem.
- **Gadget specifications** (`CodeRangeGadget.Spec.*`). The `code_range` gadget, which at v3.2.0
  both memory chips and the precompile chips that write memory embed (`blake2b/control.rs` and
  `keccak256/control.rs` among them, not `blake2b/round.rs`), is proven on its own:
  `gadget_spec` and `spec` say that on a store row (`is_store = 1`, `addr` two 16-bit pieces,
  `width` below 2^16) that satisfies the gadget's constraints, the write `[addr, addr + width)`
  misses the range `[code_start, code_end)` the row looks up from the Program table.
  That range is read from the row's own columns: the Program table's promise
  (`V3.CodeRangeBus.Spec`) gives only that its four pieces are below 2^16, not that they are this
  program's code range, so these theorems do not yet say that a store misses the program's code
  (see A4). `wf_asrt` and `ext_asrt` say the gadget's messages owe nothing to the tables that
  answer them.

## Pinned inputs

The proofs are about this Pico revision:

<!-- generated: pin -->
Pico v3.2.0, commit [`fcfa50462`](https://github.com/brevis-network/pico/commit/fcfa504624657d0c417c43f1233d5d891f293ff9).
<!-- end generated -->

Re-extracting the CPU chip, the ten ALU chips and their gadgets at v3.1.6 gives the same
constraints and bus messages as at v3.1.1: each extraction file differs only in its first line,
which names the Pico commit. So what this document says about those chips' own constraints at
v3.1.1 holds at v3.1.6. Pico's per-chip constraint digests (`vm/tests/riscv_constraint_dump.txt`)
cannot show this at v3.1.6, which changed every chip's digest when it rewrote how chunks are joined;
the re-extraction does.

v3.2.0 changed nothing an RV64IM chip constrains. Re-extracting every file at v3.2.0 gives the same
constraints and bus messages as at v3.1.6, each file again differing only in its first line. The
constraint digests differ only by two new precompile chips, `Blake2bControlChip` and
`Blake2bRoundChip`, and the overall digest. Under `vm/src/chips/chips`, `vm/src/chips/gadgets` and
`vm/src/machine/builder`, the one changed file is `riscv_memory/unaligned/traces.rs`, which now
fills the trace in parallel and constrains nothing. The other claims in this document that name
v3.2.0 were checked at v3.1.6, and the Pico files they cite are unchanged at v3.2.0; if the pin above
names a later version, they have not been checked there yet.

A chip's constraints also cannot show which chips receive its messages. At
the pin the CPU chip's memory dispatch has a second receiver, `MemoryUnalignedChip`, which serves
misaligned loads and stores, so the memory promise no longer says an address is aligned (see
A4), and the Program table changed after v3.1.1 (see A6).

<!-- generated: pending -->
Every extraction file is generated from the pinned Pico commit.
<!-- end generated -->

The other inputs are pinned as well:

- Lean toolchain: `leanprover/lean4:v4.28.0-rc1` (`lean-toolchain`).
- RISC-V specification: `sail-riscv-lean`
  [`bb1e7d45`](https://github.com/NethermindEth/sail-riscv-lean/tree/bb1e7d45c6a158a5598705eea12cebfee4349b03),
  built on the Sail library `lean-sail`
  [`535c13d3`](https://github.com/NethermindEth/lean-sail/tree/535c13d3026c404e283c2e1b7f46c85237382223)
  (`lake-manifest.json`). Its `LeanRV64D` files were regenerated from `riscv/sail-riscv` in
  sail-riscv-lean's commit `a318417f` (2026-02-11, "move to v4.28.0-rc1"); the next commit,
  `bb1e7d45`, sets the platform configuration by hand: the `Zicfilp` and `Zca` extensions off, no
  PMP entries, no CLINT.
- The `riscv/sail-riscv` commit those files were generated from is not recorded: `a318417f` names
  none, nor the Sail compiler commit that translated it. Their content points to
  [`5f5f02d3`](https://github.com/riscv/sail-riscv/commit/5f5f02d37f5156d8e8625622409fbb8caef2cf8f):
  they contain `canonical_NaN_BF16`, which that commit added on 2026-02-10, and it stayed the head
  of `master` until 2026-02-12, after `a318417f` was made. That has not been confirmed by
  regenerating the files, so the commit is unknown here.
- The RISC-V unprivileged ISA version: neither repository names a dated release of the
  unprivileged ISA manual. sail-riscv's `README.md` at `5f5f02d3` gives the versions of the parts
  these proofs use: the RV64I base ISA, v2.1, and the M extension, v2.0.
- Circuit framework: `LeanZKCircuit-Plonky3`
  [`d1f15357`](https://github.com/NethermindEth/LeanZKCircuit-Plonky3/tree/d1f15357a7a999618b80dd110aba955c1f111cf6)
  (branch `Dom/v4.28.0-rc1`), and Mathlib
  [`5352afcc`](https://github.com/leanprover-community/mathlib4/tree/5352afccd6866369be9de43f5b7ec47203555f44)
  (tag `v4.28.0-rc1`), both in `lake-manifest.json`.
- The extractor: Rust `nightly-2026-09-27` (`extractor/rust-toolchain.toml`); Pico and Plonky3 in
  `extractor/Cargo.toml` and `extractor/Cargo.lock`.

CI (`.github/workflows/ci.yml`) runs on every pull request and every push to `main`: its
`extractor` job regenerates every generated file from the pinned Pico and fails if
one differs from the committed file, and its `build` job rebuilds the proofs and runs `check.sh`.

## Summary of the risks

| ID | Risk | Mitigation in place |
|----|------|---------------------|
| A1 | The extracted constraints differ from Pico's | Extracted by running each chip through Pico's own symbolic builder; `extractor --check` in CI |
| A2 | The RISC-V specification is not what RISC-V means | The official Sail model, translated to Lean, pinned (source commit not recorded; platform configuration set by hand; see Pinned inputs) |
| A3 | A theorem holds only under a hypothesis | Hypotheses are part of each statement, snapshotted in `signatures.txt`; the definitions they name are fingerprinted in `definitions.txt` |
| A4 | The chips' bus messages do not compose as assumed | None yet: not proven (see A4) |
| A5 | A part of Pico is not covered | Listed in A5 |
| A6 | The Lean model of Pico's instruction decoder differs from Pico's at the pinned commit | Compared line by line in review; Pico's decoder tests restated as Lean `example`s |
| C1 | The Lean kernel or its axioms are unsound | None |
| C2 | A proof trusts compiled code | Ratchet in `check_tactics.sh`; listed in C2 |
| C3 | A declaration reached the environment unchecked | Weekly kernel replay in CI, except the modules of C2 |
| D1 | A dependency changes | Pinned in `lake-manifest.json`, `extractor/Cargo.lock` and `extractor/Cargo.toml`; a weekly job lists where Pico `dev` and `main` differ from the pin (`scripts/ci/drift.py`) |

## A. Does each definition say what it should?

### A1. Extraction

`extractor/` evaluates each RV64IM chip's `eval` with Pico's `get_symbolic_builder`, the same path
Pico's keygen takes, and prints the constraints and bus interactions as Lean. The output records
the Pico commit it came from. `extractor --check` regenerates every generated file and compares it
with the committed one, so a file that has not been regenerated from the pinned commit fails CI,
except for the files listed in `extractor/pending.txt` (see "Pinned inputs").

Gadgets are extracted through small wrapper airs that call the gadget's `eval` on a column
layout of the same width; a test checks that each wrapper uses every column it declares.

What remains trusted: the extractor's printer (`extractor/src/render.rs`); that Pico's
symbolic builder records what the prover enforces; and the circuit framework's semantics
(`LeanZKCircuit_Plonky3.Plonky3.Circuit`, `LeanZKCircuit_Plonky3.Interactions`), which say what
`allHold` and the bus lists mean.

### A2. The RISC-V specification

Opcode behaviour is the Lean translation of the official Sail RISC-V model
([`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean), pinned in
`lake-manifest.json`). That translation sets some platform configuration by hand, and the
sail-riscv commit it was generated from is not recorded (see "Pinned inputs"). It declares some
functions as axioms (floating point, random bits, reservations, platform output). They are
listed in `scripts/fv-check/spec-axioms.txt`. They appear among the equivalence theorems' axioms
because the specification's step function mentions them, but the theorems hold for every
interpretation of them. One of them, `sys_enable_experimental_extensions`, gates the unratified
`Zibi` and `Zvabd` extensions the model includes, so the theorems hold with or without them.

### A3. Hypotheses of the theorems

Each equivalence theorem assumes hypotheses from the following list; `signatures.txt` records
which:

- the CPU chip's extracted constraints hold on every row;
- the bus assumptions (`bus_row_axioms`, `bus_row_ext_asm`, `bus_row_wf_asm`, `bus_row_wf_asrt`):
  what the other chips deliver for the messages this row sends, and the well-formedness of what
  it receives;
- the hypotheses of the operations the row emits, and `RISC_V_assumptions` on the machine state;
- at v3.1.1, the whole-trace assumption described below.

A theorem in decoded form (below) takes only the hypotheses its proof uses: of the bus
assumptions only `bus_row_wf_asm`, and `RISC_V_assumptions` only where its proof reads it. The
checked instruction theorems of `Stores.lean`, `Loads.lean`, `RType.lean`, `RTypeW.lean`,
`IType.lean`, `Addiw.lean`, `ShiftIOp.lean`, `ShiftIWOp.lean`, `MulFamily.lean`,
`DivFamily.lean`, `BType.lean`, `Jumps.lean` and `UType.lean` are in decoded form.

Since v3.1.6 a row's messages fall into six lists, not five: the code-range message
(`V3.CodeRangeBusEntry`), which a store row and a precompile row send to the Program table, has
its own list, `CodeRange`, empty on every CPU-chip row. The four checks above (and
`bus_row_ext_asrt`) cover the other five lists only; the code range has its own checks
(`bus_row_code_range_wf_asm` and its siblings), kept apart because adding the list to the five
made the branch and jump equivalence proofs time out. The checks over all six lists are
`bus_row_all_axioms`, `bus_row_all_ext_asm`, `bus_row_all_ext_asrt`, `bus_row_all_wf_asm` and
`bus_row_all_wf_asrt`, each the five-list check together with its code-range counterpart. A
theorem about a row that may carry code-range messages states its bus hypotheses and duties with
these; the `CodeRangeGadget.Spec` theorems do. For a row with no code-range message each is the
five-list check (`bus_row_all_wf_asm_iff` and its siblings), so the equivalence theorems, which
use the five-list checks, leave out no message their rows send.

The instruction theorems checked at the moment (listed under "What is proved") are recorded at
v3.1.1, against the v3.1.1 CPU constraints and the v3.1.1 contracts (`RV64IM_Interactions.V3` in
`RVSail/BusesV3.lean`). The column forms of `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`, `XORI`, `ORI`,
`ANDI`, `SLTI`, `SLTIU`, `SLLI`, `SRLI` and `SRAI` do not assume `imm_b = 0`, which the v3.1.1
decoder fixes for their opcodes, and `SUBW` and `SUB` no longer assume `imm_c = 0`, which it fixes
for opcodes 41 and 1. `ADDI`'s column form assumes `imm_b = 0`: its opcode 0 with `imm_c = 1` is
also `LUI` or `AUIPC`, which set `imm_b = 1`. `ADD` does not assume it, although the decoder does
not fix it for opcode 0: on a row with `imm_c = 0` the flag is 0 whatever the opcode
(`imm_b_eq_zero_of_imm_c_eq_zero`). The decoder does not fix `imm_c` for an opcode that an immediate
form shares with a register-register one: 40 (`ADDIW` and `ADDW`), 42 to 44 (`SLLIW`, `SRLIW`,
`SRAIW` and `SLLW`, `SRLW`, `SRAW`), 5 to 7 (`SLLI`, `SRLI`, `SRAI` and `SLL`, `SRL`, `SRA`), and 0,
2, 3, 4, 8 and 9 (the six `ITYPE` theorems and `ADD`, `XOR`, `OR`, `AND`, `SLT`, `SLTU`). Neither
those thirteen immediate-form theorems nor those thirteen register-register theorems assume an
immediate flag: they take their instruction in decoded form (below), whose decoding fixes both
flags; their column forms still assume `imm_c = 1` (and `ADDI`'s `imm_b = 0`) or `imm_c = 0`. The
multiply, divide and remainder theorems take no immediate flag, as at `353238a`: the decoder fixes
both to 0 for opcodes 30 to 37 and 48 to 52. They take no opcode either: they take their instruction
in decoded form (below); their column forms take the opcode alone. The divide and remainder theorems
assume nothing about the divisor: the ALU chip's promise for their opcodes already gives Sail's
result on division by zero and on signed overflow. `JAL` and `JALR` take no opcode: the decoding
fixes it (below). Their `_row` forms take it alone: they assume neither immediate flag, nor the
row's `is_jal` / `is_jalr` selector, all three of which their 2.x statements took, because opcodes
24 and 25 are the two jumps alone and the decoder fixes every one of them. The six branch theorems
take no opcode either; their `_row` forms take it alone, as the branch theorems did at `353238a`:
opcodes 18 to 23 are the six branches alone. Their comparison is not made in the CPU chip. The row
sends it on the ALU bus — opcode 264 for `BLT` and `BGE`, signed, and 265 for the other four,
unsigned — so the two comparison bits are what `ALUBus.Spec` promises for those opcodes, which
`LtChip.Spec.spec_CMP_SLT` and `spec_CMP_SLTU` discharge on the serving chip's side, and the branch
theorems assume nothing about the operands themselves.

The column forms of the thirteen register-immediate theorems (the six shifts, `ADDI`, `XORI`,
`ORI`, `ANDI`, `SLTI`, `SLTIU` and `ADDIW`) read their immediate from the row's encoded `op_c_0`,
as they read `rd` and `rs1`, instead of from the `op_c` value the row sends to the ALU chip. The
proofs link the two through the CPU constraint that, on a row whose third operand is an
immediate, copies `op_c_0` into the first 16-bit piece of the `op_c` value
(`op_c_value_setWidth_eq_op_c_0`, through `imm_c_eq_1_constraints`). A shift's amount is
`op_c_0`'s low 6 bits (5 for the 32-bit shifts), that is `op_c_0` modulo 64 (or 32); the other
seven take `op_c_0`'s low 12 bits. The decoder sign-extends the seven 12-bit immediates and
zero-extends the six shift amounts (`Transpiler.V3.imm_operand` with its sign flag `true` or
`false`), and writes the low 16 bits of the result into `op_c_0`, the next 16 into `op_c_1` and
the sign into `op_c_sign`. So on a row the program decoded those bits are the program's shift
amount or 12-bit immediate; the column forms do not state that link.

The four store, the seven load and the thirteen register-immediate theorems state it. So do the
theorems of the four register classes: the fifteen register-register theorems (`RType.lean`,
`RTypeW.lean`), the five multiply theorems (`MulFamily.lean`) and the eight divide and remainder
theorems (`DivFamily.lean`), which have no immediate but whose registers the decoding fixes in the
same way. So do the six branch theorems (`BType.lean`), `JAL` and `JALR` (`Jumps.lean`), and `LUI`
and `AUIPC` (`UType.lean`). Each takes the instruction itself, written in the statement
(`instruction.STORE (imm, rs2, rs1, 8)` for `SD`, `instruction.ITYPE (imm, rs1, rd, iop.ADDI)` for
`ADDI`, `instruction.RTYPE (rs2, rs1, rd, rop.ADD)` for `ADD`,
`instruction.BTYPE (imm, rs2, rs1, bop.BEQ)` for `BEQ`, `instruction.JAL (imm, rd)`,
`instruction.UTYPE (imm, rd, uop.LUI)`), with the hypothesis `h_decode` that the decoder
(`Transpiler.V3.transpile_op`, at multiplicity 1 and some address `addr`) turns it into the row's
Program message, and concludes that Sail's step on that instruction equals the row's effect. The
decoding fixes `is_real = 1`, the opcode, the immediate flags, the register columns and the offset
or immediate (for `LUI` and `AUIPC`, the operand shape), so these theorems take none of them as
hypotheses. It fixes `addr` only modulo `2 ^ 32`, through the row's two 16-bit pc pieces. Given the
row's Program promise, the decoding hypothesis is no stronger than the hypotheses it replaces:
`Equivalence.store_decode_satisfiable`, `Equivalence.load_decode_satisfiable`,
`Equivalence.rtype_decode_satisfiable`, `Equivalence.rtypew_decode_satisfiable`,
`Equivalence.itype_decode_satisfiable`, `Equivalence.addiw_decode_satisfiable`,
`Equivalence.shiftiop_decode_satisfiable`, `Equivalence.shiftiwop_decode_satisfiable`,
`Equivalence.mul_decode_satisfiable`, `Equivalence.mulw_decode_satisfiable`,
`Equivalence.div_decode_satisfiable`, `Equivalence.divw_decode_satisfiable`,
`Equivalence.rem_decode_satisfiable`, `Equivalence.remw_decode_satisfiable`,
`Equivalence.btype_decode_satisfiable`, `Equivalence.jal_decode_satisfiable` and
`Equivalence.jalr_decode_satisfiable` (checked, listed with their classes) derive it, for some
instruction fields and a 4-aligned address below `Transpiler.V3.code_address_bound`, from
`is_real = 1`, the opcode of each store or load width, register-register, register-immediate,
multiply, divide or remainder operation, branch or jump (with `imm_c = 0` for a register-register
opcode an immediate form shares, as its column form takes it, and on the opcodes of `SUB` and `SUBW`
the promise gives it; with `imm_c = 1` for a register-immediate opcode, and `imm_b = 0` for
`ADDI`'s, as their column forms take them), and that promise (in `bus_row_wf_asm`, which the
instruction theorems take for every row as `h_all_wf`). For opcode 30 (`MUL`) it holds at every
signedness with `result_part := .Low`, which the decoder does not read.
`Equivalence.utype_decode_satisfiable` derives it from `is_real = 1`, opcode 0, `imm_b = 1` and the
promise, for a `LUI` or an `AUIPC`: the opcode and the flags do not say which; the operand shapes
tell them apart except where they overlap, and there both hold (below). Each decoded theorem is
proved from a column-form theorem of the same name with `_row` appended (`equivalence_SD_row`),
which reads `rs1`, `rs2` or `rd` (and the offset or immediate) off the row and is not checked.
`equivalence_LUI_row` and `equivalence_AUIPC_row` read `rd` off the row but take the immediate as a
parameter, pinned by their shape hypotheses `h_op_b` and `h_op_c` (below).

The four store theorems take no opcode: the decoding fixes it (their `_row` forms take it alone,
as the store theorems did at `353238a`). They gain the whole-trace assumption, which their 2.x
statements did not take. Like every restored theorem they
rest on the Program table's promise (A4, A5). Of the Memory message's promise (`MemoryBus.Spec` in
`RVSail/BusesV3.lean`) a store uses one clause: the address `op_b + op_c` is below `2 ^ 32`, so the
whole access lies in the memory region `RISC_V_assumptions` gives Sail (at least `2 ^ 48` bytes);
Sail traps instead of storing outside it. The promise says nothing about alignment and the theorems
do not assume it. At an address that is not a multiple of the width, Sail splits the store into
naturally aligned pieces and writes the same bytes, which the Sail lemmas of `SH`, `SW` and `SD`
prove (`RVSail/Misaligned.lean`). That case rests on the Sail model allowing misaligned access
(`plat_enable_misaligned_access`, `true` in the model). The proofs also use the clause
`misaligned_fault = NoFault` of `RISC_V_assumptions`, as the aligned case does. **The Memory
promise is discharged by both chips that take the dispatch.** `MemoryReadWriteChip.Spec` proves it
at the pinned commit for every dispatch that chip receives (`spec_SB`, `spec_SH`, `spec_SW` and
`spec_SD` for the stores, and `wf_asrt`); that chip takes only accesses aligned to their width.
`MemoryUnalignedChip.Spec` proves it, under the same names, for every dispatch the unaligned chip
receives, which may be any access, aligned or not (`riscv_memory/unaligned/mod.rs:3-6` at v3.2.0).
The two sides of the link a store theorem assumes are not yet composed, as A4 describes for chip
composition generally.

The seven load theorems take no opcode either: the decoding fixes it (their `_row` forms take it
alone, as the load theorems did at `353238a`). They gain the whole-trace assumption, which their 2.x
statements did not take. They rest on the same promise, and on one more part of it. Besides the
address bound, `MemoryBus.Spec` says what extension the loaded word carries when the destination is
not `x0`: sign for `LB`, `LH` and `LW`, zero for `LBU`, `LHU` and `LWU`, none for `LD`. That is the
whole content of what a load writes to `rd`, so a load theorem says that the CPU row writes back
whatever the memory chip promised, and, like the stores, it assumes that promise rather than resting
on a proof of it; both memory chips prove the promise for the loads they take (`spec_LB` to
`spec_LD` in `MemoryReadWriteChip.Spec` and in `MemoryUnalignedChip.Spec`). The CPU constraints
alone do not tie the loaded word to memory. A load whose destination is `x0` needs only the address
bound: the row writes zero to `x0`, and Sail's write to `x0` changes nothing. The loads hold at a
misaligned address as the stores do: Sail splits the load into aligned pieces and reads the same
bytes, which the Sail lemmas of `LH`, `LHU`, `LW`, `LWU` and `LD` prove (`RVSail/Misaligned.lean`).

The two U-type theorems share a row shape: the v3.1.1 decoder gives `LUI` and `AUIPC` alike opcode 0
with both immediate flags (`ProgramBusEntry.decoded_from`), and the chip has no `AUIPC` opcode and
no `is_auipc` selector. The decoded theorems take the instruction, and its decoding puts the row in
the instruction's operand shape: for `LUI`, the `op_b` value is zero and the `op_c` value is
`signExtend 64 (imm ++ 0#12)`; for `AUIPC`, the `op_b` value is that immediate and the `op_c` value
is the row's pc. Their column forms, `equivalence_LUI_row` and `equivalence_AUIPC_row`, take
opcode 0, both flags and that shape as hypotheses, with the 20-bit immediate `imm` as a parameter.
Neither form takes `RISC_V_assumptions`, which neither proof reads. At `353238a` `LUI` was opcode 0
with both flags and read its immediate out of the `op_c` value, and `AUIPC` was opcode 27 with
`is_auipc = 1`; neither took the whole-trace assumption, which both now do.
`Equivalence.utype_decode_satisfiable` shows every real row of opcode 0 with `imm_b = 1` decodes
from a `LUI` or an `AUIPC`, so the two decoded theorems cover the opcode. For the column forms,
`Equivalence.utype_row_cases`, checked, proves that every real row of opcode 0 with both flags has
one of the two shapes. It takes two of the instruction theorems' own hypotheses: every row's
extracted CPU constraints, and every row's `bus_row_wf_asm`, the whole bus assumption with the ALU
and Memory promises in it, although its proof reads only the row's Program message (the Program
table's promise). The shapes overlap
exactly when the `op_b` value is zero and the `op_c` value is the row's pc: the row is `AUIPC 0`
and also the `LUI` of the pc's upper bits, which needs the pc to be a multiple of `2 ^ 12` but is
not implied by it (`LUI 5` at pc `0x1000` has the `op_c` value `0x5000`). There both theorems hold,
because both instructions write the pc. `op_b = 0` alone would not identify a `LUI` row: an `AUIPC`
row whose immediate is 0 has it, and writes the pc. Both theorems rest on the ALU chip's promise for
opcode 0 (`op_a = op_b + op_c`), as `ADD` and `ADDI` do. The row reads no source register: its
operations are `JAL`'s, the pc read, the read of `rd`'s old value and the write of `rd`, and the
next pc.

The 2.x statements were last recorded at `353238a`, against the 2.x constraints and the contracts
of `RVSail/Buses.lean`. Two definitions every instruction
theorem names were rewritten at v3.1.1 behind unchanged names: `Equivalence.CPU_bus_operations`, the
operations the theorem compares the Sail step against (now a two-piece pc, with the memory width and
direction taken from the opcode), and `CpuChip.Interpretations.bus_row`, which sorts the row's
messages (now with the v3.1.1 deserialiser). A third was rewritten against v3.1.6:
`V3.MemoryBus.Spec`, the memory chips' promise, which every checked 3.x instruction theorem
assumes through its `bus_row_wf_asm` hypothesis. It lost its three alignment clauses (see the
composition section below), so that hypothesis now assumes less, and each theorem says more.

The whole-trace assumption, `pico_CpuChip_control_flow_assumptions`, bounds the chunk's final pc
(public values 43 and 44): two 16-bit pieces, a multiple of 4 and below `0x7800_0000`. The chip does
not check this itself; Pico's recursion circuit makes it hold for every chunk of an accepted
recursive proof ("The whole-trace assumption" below). That circuit was read again at v3.1.6, which
rewrote it: the three checks the argument uses (the pc carried from chunk to chunk, a chunk with no
CPU keeping its pc, the last chunk ending at pc zero) are still there. The file is unchanged at
v3.2.0 (`git diff v3.1.6 v3.2.0` over it is empty). So the instruction theorems cover a chunk inside
an accepted recursive proof, not a chunk proof checked on its own. The eight branch and jump
theorems already name the assumption, whose definition grew, so it is not what changes their
recorded statements: all eight are recorded at v3.1.1 now, and changed for the other reasons above.
What they assume did change, behind the unchanged name. The other 54 gain it as a new hypothesis, as
those recorded at v3.1.1 have.

A change that weakens or strengthens a hypothesis changes `signatures.txt`, and `check.sh` fails
until the change is reviewed and recorded. A change to the definition behind a hypothesis's name
leaves `signatures.txt` as it is, but changes the definition's fingerprint in `definitions.txt`,
and `check.sh` fails on it, naming the definition and every definition that uses it, until the
change is reviewed and recorded with `check.sh --update`. A fingerprint covers every definition of
this repository that a checked statement reaches, through definition bodies; it stops at Lean,
which `lean-toolchain` pins, and at Mathlib, the Sail model and the circuit framework, which
`lake-manifest.json` pins. It depends on no name of this repository except a constructor's own (a
renamed constructor is drift), so a rename listed in `definition-renames.txt` passes the check
without drift, unless the new name already belongs to another definition (a 2.x definition that a
3.x one replaces): that name then reports drift.

#### The whole-trace assumption

Public values 43 and 44 are the two pieces of the chunk's final pc; the chip pins 45 to zero
itself. On the last real row the chip sets its `next_pc` to them (extracted constraints 41-43,
`riscv_cpu/public_values/constraints.rs:35-50` at v3.2.0), and nothing in the chip range-checks
them. The proofs need each part: the 16-bit pieces and the alignment for the JALR addition, its
cleared low bit and BEQ's aligned target, and a bound on the value to read the `pc + 4` and
branch-target field equations as integer equations. The weakest bound those readings need is
`p - 4096` (`p` the KoalaBear prime, `4096` the largest backward branch); `0x7800_0000` is
slightly stronger, is the guest address bound Pico itself uses, and also covers JAL's 21-bit
offsets, which need `p - 2^20`.

Pico enforces it outside the chips, in the recursion circuit
(`vm/src/mle/compiler/recursion/lowering.rs` at v3.2.0): each chunk's final pc equals the next
chunk's first pc (`assert_child_continuity`, `recursion/lowering.rs:1194-1199`); a chunk that runs
no CPU passes its pc through unchanged (`recursion/lowering.rs:1559-1563`); the root requires the
last chunk's final pc to be zero (`assert_root_complete`, `recursion/lowering.rs:1776-1779`). The
circuit has other checks (a CPU chunk's first pc is not zero, `recursion/lowering.rs:1510-1516`; a
chunk with no CPU is not chunk 1, `recursion/lowering.rs:1522-1527`) that only narrow what is
accepted. A chunk's first pc is its row 0's pc (`riscv_cpu/public_values/constraints.rs:26-33` at
v3.2.0), row 0 is real (`riscv_cpu/constraints.rs:340-341` at v3.2.0) and its fetch matches the
Program table, whose pcs are 4-aligned and below `0x7800_0000` (`riscv_program/traces.rs:86-113` at
v3.2.0). So in an accepted proof the final pc is either zero or a Program-table pc, which satisfies
the assumption. No check of its own on the public value was found outside the chips (no range or
alignment check in the recursion circuit or the verifiers).

### A4. Composition of the chips (not proven)

Each chip is verified on its own, against the bus assumptions. That the assumptions one chip
makes are discharged by what the other chips prove relies on Pico's LogUp argument balancing
every bus, and on each message being served by a chip whose specification is proven. Neither is
proven here.

One side of each CPU link is proven: what a chip serving the CPU may assume of the CPU as a
sender (`bus_row_ext_asm` in the ALU chips' specifications) is what `CpuChip.Spec.ext_asrt`
proves the v3.1.1 CPU chip sends, at whatever multiplicity it sends it (each message that
carries a duty is sent 0 or 1 times, `CpuChip.Spec.multiplicity_eq_zero_or_one`). The theorem
assumes only the Program table's and the register file's promises, not those of the ALU and
memory chips it sends to, so the CPU's side of each of those links does not rest on the
receiving chip's theorem. Both memory chips' specifications assume of the CPU what the 3.x
contract states (`MemoryBus.externals` in `RVSail/BusesV3.lean`), the duty the CPU is proven to
meet.

At v3.2.0, the pin, the memory dispatch has two receivers. Since v3.1.2 Pico has
`MemoryUnalignedChip` (`vm/src/chips/chips/riscv_memory/unaligned/`), which takes the same
17-field message on the same bus as `MemoryReadWriteChip` and serves loads and stores whose
address is not a multiple of their width. The CPU chip's constraints did not change, so either
chip may take any load or store. The promise the CPU chip assumes of the dispatch
(`MemoryBus.Spec` in `RVSail/BusesV3.lean`) therefore states only what holds whichever chip takes
the message: a load's value has 16-bit pieces, the address `b + c` is at least `2^16` and below
`2^32`, and, unless the destination is `x0`, a load's value is the sign or zero extension its
opcode names. The address bound and the extensions follow from each chip's constraints at v3.2.0
together with the CPU's duty that `b` and `c` have 16-bit pieces (`MemoryBus.externals`) and the
byte table's promise for the range checks the row sends (`ByteBus.Spec`, assumed through
`bus_row_all_wf_asm`). The 16-bit pieces need more: in `MemoryReadWriteChip` they are pieces of
the previous memory value, which the memory argument's promise bounds; in `MemoryUnalignedChip`
each is two bytes of its byte splits, which the byte table's promise bounds; and for a load into
`x0` neither chip constrains the value, so there the clause holds because the CPU sends zero
(`MemoryBus.externals`). Its doc comment cites the constraint of each chip behind each clause.
It no longer says that a halfword, word or doubleword address is a multiple of the width, as it did
when drafted against v3.1.1, where `MemoryReadWriteChip` was the only receiver. It says nothing
about which memory a load reads, or about the message's `chunk` and `clk` fields. That a store
misses the program's code is not the memory promise's business: the store row proves it itself,
through the `code_range` gadget, against the code-range contract below. Both chips prove the
promise for every dispatch they receive (`spec_LB` to `spec_SD` and `wf_asrt`, in
`MemoryReadWriteChip.Spec` and in `MemoryUnalignedChip.Spec`). Which memory a load reads and a
store writes the promise does not ask; both chips prove it apart, for every row
(`MemoryReadWriteChip.Spec.dataFlow_of_allHold`, `MemoryUnalignedChip.Spec.dataFlow_of_allHold`):
in a Sail state that holds the double words the row reads from the memory argument, the
dispatch's read holds, and the row's write backs leave the state the dispatch's operation leaves.
The read/write chip reads one double word; the unaligned chip reads the one holding the access's
first byte and, on a row whose access crosses, the next one. A load's value, at its width, is
therefore the bytes from `b + c` on of the double words read; the sign or zero fill above that
width is the promise's (`spec_LB` to `spec_LWU`). A store writes those double words back with its
bytes in their place. What stays on trust is the memory argument: that each double word a row
reads is the last one written at that address. That rests on the memory bus balancing, as above;
on the timestamp ordering, since no checked theorem states `clk > prev_clk` and neither chip's
`DataFlow` reads the clocks; and on the memory initialisation and finalisation chips (A5). The
load and store theorems hold for a misaligned address too (A3).

The contract now covers the merged branch-comparison rows. `ALUBus.validOpcode` contains the two
opcodes 264 / 265 (`SLT` / `SLTU` + `LT_CMP_OPCODE_TAG`) that Pico's CPU sends for every branch,
`ALUBus.Spec` gives them their meaning — piece 0 is `[b < c]`, piece 1 is `[c < b]`, pieces 2 and
3 are zero — and `LtChip.Spec.spec_CMP_SLT` / `spec_CMP_SLTU` prove that `LtChip` serves them.
What the CPU does with the two bits is the CPU chip's side, and the six branch theorems in
`Equivalence/BType.lean` prove it: `branch_compare_spec` turns the promise into the meaning of
the two bits, `branch_taken` builds the taken condition from them, and the next-pc constraints
send the row to `pc + offset` or `pc + 4` as Sail does.

The code-range message rests on a chip that is not covered. A store row of either memory chip,
and every precompile chip for what it writes, looks up the code's range `[code_start, code_end)`
from the Program table (`gadgets/code_range.rs:1-11` at v3.2.0), and the
`CodeRangeGadget.Spec` theorems assume what the table answers: four pieces below 2^16
(`V3.CodeRangeBus.Spec`). The Program chip has no proof here (A5), so that promise is trusted.
It is also weaker than what Pico intends: it does not say the four pieces are this program's
code range, which the Program table's preprocessed columns hold
(`riscv_program/columns.rs:36-40`, `traces.rs:132-136`) and `program_commit` fixes, so no theorem
here yet says that a store misses the program's code.

How the table answers it does not fit the framework's conditions either. Trace generation puts
the chunk's whole count of code-range lookups, one per store and one per precompile event
(`code_range.rs:71-73`), on Program row 0 (`riscv_program/columns.rs:48-51`,
`traces.rs:178-180`). With `N` lookups in a chunk the table answers once, at multiplicity `-N`.
A contract's promise binds a receiver only at multiplicity `-1` (`wf_assert_cond` in
`Fundamentals/Interaction.lean`), so for `N ≠ 1` a Program-chip theorem stated with
`bus_row_all_wf_asrt` would ask nothing of that answer, while each sender assumes the promise at
`+1`. The two sides meet only through the LogUp balance, which is not proven; a composition
theorem has to treat a multiplicity summed onto one row. The promise itself holds whatever the
multiplicity, since every Program row carries the same preprocessed range.

Messages a chip serves but the contract does not specify are still not covered in general; there
are none among the RV64IM ALU chips at v3.2.0.

### A5. What is not covered

`ECALL` and syscalls, the precompile chips, the program, global memory and memory
initialisation chips, the recursion layers, and Pico's proof system itself. The
`CodeRangeGadget.Spec` theorems assume the Program chip's code-range promise
(`V3.CodeRangeBus.Spec`), which rests on the Program chip and so is trusted (see A4).
The precompile chips also send the code-range message; no theorem here covers their side of it.

Deferred by decision of 2026-11-23:

- composing the chips into the execution of a whole chunk: that every bus balances across the
  chips, so that the assumptions each chip makes are met by the promises the others prove (A4);
- the precompile chips, including `Blake2bControlChip` and `Blake2bRoundChip`, which v3.2.0 adds;
- the recursion layers;
- completeness, the converse direction: the theorems say that, under their hypotheses, rows
  which satisfy the constraints behave as the Sail specification says, not that every Sail
  execution has such rows.

### A6. The instruction decoder

The Program contract (`RV64IM_Interactions.V3.ProgramBusEntry.operand_properties` in
`PicoFV/RV64IM/RVSail/BusesV3.lean`; the 2.x contract of the same short name is in `Buses.lean`)
says that a fetched instruction is the row the Lean decoder `Transpiler.V3.transpile_op`
(`PicoFV/RV64IM/Transpiler/TranspilerV3.lean`) gives some Sail instruction at a 4-aligned address
below `0x7800_0000`. That decoder models Pico's decoder
(`vm/src/compiler/riscv/disassembler/rrs.rs`) and Program table builder
(`vm/src/chips/chips/riscv_program/traces.rs`). It was written against v3.1.1. Only review compares
the Lean decoder with the Rust one; Pico's own decoder tests are restated as `example`s at the end
of `TranspilerV3.lean`. The decoder starts from an already-decoded Sail instruction, not from the
32-bit word: that a word decodes to the same instruction in Sail and in Pico is not modelled.

The contract was read again against v3.1.5, and again against v3.1.6. The decoder
(`rrs.rs`), the opcodes and the instruction type did not change. The Program table builds each
instruction's row as before, at the same addresses under the same asserts; since v3.1.2 the table
adds the program's code range to every row in four new columns, `code_start` and `code_end`. The
Program chip still receives the CPU's 26-field instruction message, and it now also serves a 4-field
message giving that range, which store rows look up to prove that they do not write into the code.
Pico's LogUp fingerprint includes a message's length (`eval_interaction` in
`mle-core/src/prover/logup_zerocheck/evaluator.rs`), so the two messages never match each other. The
Lean reader of the CPU row's messages (`deserialise_bus_row` in `RVSail/BusesV3.lean`) takes only
26-field messages as instructions. The ELF loader (`vm/src/compiler/riscv/disassembler/elf.rs`)
rejects more files than at v3.1.1 (32-bit ELFs, segments that are both writable and executable, an
entry point outside the code) and builds the instructions in the same way. From v3.1.5 to v3.1.6
none of the decoder, the Program chip's files or the ELF loader changed. So the Program contract
holds at v3.1.6 as written. The files cited here are unchanged at v3.2.0 (`git diff v3.1.6 v3.2.0`
over them is empty).

The fences have no row of their own. Pico runs every fence word (`fence`, `fence.tso` and
`pause`) as the no-op `ADD x0, x0, 0`, the row of `ADDI x0, x0, 0`. Sail decodes them as three
other instructions, `FENCE`, `FENCE_TSO` and `PAUSE`, and `PicoFV/RV64IM/RVSail/Opcodes/fence.lean`
proves that each executes exactly as `ADDI x0, x0, 0`: `PAUSE` and `FENCE_TSO` in every state,
`FENCE` in machine mode (`execute_instruction_fence_eq_nop` takes `cur_privilege = Machine`,
assumption A1.1 of `RISC_V_assumptions`). A fence's row is `ADDI x0, x0, 0`'s, so covering a
`FENCE` row takes `equivalence_ADDI` and, beside it, that machine-mode assumption, whether or not
`equivalence_ADDI` itself takes `RISC_V_assumptions`.

## C. Is each proof sound?

### C1. Kernel and axioms

Proofs are checked by the Lean kernel. An axiom is a statement Lean accepts without proof. The
axioms each top-level theorem depends on are
collected by `check.sh` and must come from Lean's core axioms (including the compiler axioms of
C2) or the specification axioms of A2.

<!-- generated: axioms -->
| Axioms the theorem depends on | Theorems |
|---|---:|
| kernel + compiler | 115 |
| kernel + compiler + RISC-V spec axioms | 62 |
| kernel only | 1 |
<!-- end generated -->

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` evaluate a decision procedure with compiled
code instead of the kernel, which adds the axiom `Lean.ofReduceBool` (and `Lean.trustCompiler`).
A proof that uses them also trusts the Lean compiler and runtime.
`scripts/fv-check/check_tactics.sh` fails when a file uses them more often than
`tactic-baseline.txt` records, and on a pull request when the baseline rises above the base
branch's, so the uses only go down.

<!-- generated: tactics -->
52 uses of `native_decide`, `bv_decide` or `decide +native` in 6 files:

- `PicoFV/Fundamentals/Core.lean`: 7
- `PicoFV/Fundamentals/KoalaBear.lean`: 1
- `PicoFV/Fundamentals/Word.lean`: 39
- `PicoFV/RV64IM/RVSail/Execution.lean`: 3
- `PicoFV/RV64IM/Spec/BitwiseChip.lean`: 1
- `PicoFV/RV64IM/Spec/DivRemChip.lean`: 1
<!-- end generated -->

### C3. Declarations the kernel did not check

A CI job (`.github/workflows/replay.yml`, Mondays at 04:00 UTC and on demand) replays into the
kernel, with `leanchecker`, the declarations of every module `scripts/ci/imported_modules.py`
lists: the modules `PicoFV64.lean` imports, directly or through other PicoFV modules. It skips
the modules listed in C2, because the kernel cannot replay what those tactics computed. The job
fails when the listing fails or is empty, or when fewer modules replay than were listed.

It ran green on 2026-11-26, dispatched by hand on a branch whose Lean files are those of `main` at
`47d64f7`: [run 45839928832](https://github.com/brevis-network/pico-fv/actions/runs/45839928832)
replayed 204 of 204 modules in 28 minutes. At that commit:

- `imported_modules.py` lists 210 modules: every `.lean` file under `PicoFV/`, so none is left out
  for want of a build.
- Skipped: the modules C2 lists, six at that commit.
- Replayed: the other 204, the count the run's log reports as `listed` and `replayed`.
- Not replayed: every declaration outside `PicoFV/`, that is Lean's own library and every package
  in `lake-manifest.json`. Without `--fresh`, `leanchecker` replays only a module's own
  declarations, into the environment its imports built, and takes the imported declarations as
  loaded.

`Equivalence/Common`, `Jumps` and `BType` used to fail with "(kernel) deep recursion detected":
one `simp` sorted all 17 messages of a CPU row at once, and the proof term it built was deeper
than `leanchecker`'s kernel stack (`lake build` runs Lean with `--tstack=400000` in the
lakefile). The parts of a sorted row are now separate lemmas checked by evaluation
(`deserialise_raw_bus_row_Program`, `_State` and `_Memory` in `Equivalence/Common.lean`), and
the lemmas that compute a row's bus operations rewrite with them.

## D. Does the use of the results hold together?

### D1. Dependencies

The Lean dependencies are pinned in `lake-manifest.json`; the extractor's Pico and Plonky3
dependencies in `extractor/Cargo.toml` and `extractor/Cargo.lock`. A proof says nothing about a
Pico build from another commit.
