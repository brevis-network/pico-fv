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
with their statements in `signatures.txt`. They are of two kinds.

- **Opcode equivalence** (`Equivalence.equivalence_*`, one per RV64IM opcode except `ECALL`). For
  a CPU chip row that satisfies its extracted constraints, if the bus messages the row exchanges
  satisfy the bus assumptions below, then one step of the Sail RISC-V specification on that
  instruction gives the same post-state as the register and memory operations the row puts on the
  bus.

  **None of these 62 theorems is checked at the moment.** The CPU chip is moving to Pico
  v3.1.1, which is a rewrite of the chip rather than a patch: 58 columns instead of 132, 65
  constraints instead of 218 and 17 messages instead of 36. Its `Airs/` and `Constraints/`
  files are at v3.1.1 here; the interpretations file and the 13 instruction-theorem files that
  read the 2.x layout are out of the build until they are rewritten against it, one instruction
  class at a time, and their 13 lists are parked in `scripts/fv-check/theorems.d/parked/`.
  Until they return, this repository says nothing about any RV64IM opcode. Commit `353238a`
  is the last at which all 62 were checked, against the 2.x CPU extraction and the bus contract
  as it stood then (which already covered the branch-comparison opcodes). The 2.x
  interpretations file is unchanged from the tag `pico-v3-before-cpu` (`35259d8`) to that commit.
- **Chip specifications** (`<Chip>.Spec.*`). For a row of a non-CPU chip that satisfies its
  extracted constraints, the bus messages it serves have the meaning the bus assumptions give them
  (for example, an ALU row really computes the operation it claims). Every chip's specification
  is built; the checked list holds the memory chip's (`MemoryReadWriteChip.Spec.*`) and those of
  the ALU chips already at v3.1.1 (Add, Sub, Addw, Subw, Bitwise, Mul, Lt, DivRem, SLL,
  ShiftRight) today.

  `DivRemChip`'s specifications are the one exception to "satisfies its extracted constraints":
  they are stated over the readable restatement `DivRemChip.ConstraintsAndBuses.AbsConstraints`
  and over `DivRemChip.Interactions.bus_row`, not over `DivRemChip.Extraction.allHold`. Two
  checked lemmas tie those to the extraction:
  `DivRemChip.ConstraintsAndBuses.allHold_iff_allHold_simplified`, which says the extracted
  constraints are exactly `AbsConstraints` plus the extracted interaction list, and
  `DivRemChip.Interactions.bus_row_equiv`, which says `bus_row` is that interaction list,
  entry for entry. All fourteen also assume `is_real = 1`, so they say nothing about a padding
  row, where the other ALU chips' specifications still hold.

The proofs are about this Pico revision:

<!-- generated: pin -->
Pico commit [`2acc7c182`](https://github.com/brevis-network/pico/commit/2acc7c1828fb4ec1bed5963511bb370870c5b608).
<!-- end generated -->

<!-- generated: pending -->
1 extraction file(s) still predate the pinned commit and are verified against the Pico revision named in their first line: `MemoryReadWriteChip.lean`.
<!-- end generated -->

## Summary of the risks

| ID | Risk | Mitigation in place |
|----|------|---------------------|
| A1 | The extracted constraints differ from Pico's | Extracted by running each chip through Pico's own symbolic builder; `extractor --check` in CI |
| A2 | The RISC-V specification is not what RISC-V means | The official Sail model, translated to Lean, pinned |
| A3 | A theorem holds only under a hypothesis | Hypotheses are part of each statement, snapshotted in `signatures.txt` |
| A4 | The chips' bus messages do not compose as assumed | None yet: not proven (see A4) |
| A5 | A part of Pico is not covered | Listed in A5 |
| A6 | The Lean model of Pico's v3.1.1 instruction decoder differs from Pico's | Compared line by line in review; Pico's decoder tests restated as Lean `example`s |
| C1 | The Lean kernel or its axioms are unsound | None |
| C2 | A proof trusts compiled code | Ratchet in `check_tactics.sh`; listed in C2 |
| C3 | A declaration reached the environment unchecked | Weekly kernel replay in CI, except the modules of C2 |
| D1 | A dependency changes | Pinned in `lake-manifest.json`, `extractor/Cargo.lock` and `extractor/Cargo.toml` |

## A. Does each definition say what it should?

### A1. Extraction

`extractor/` evaluates each RV64IM chip's `eval` with Pico's `get_symbolic_builder`, the same path
Pico's keygen takes, and prints the constraints and bus interactions as Lean. The output records
the Pico commit it came from. `extractor --check` regenerates every file and compares it with the
committed one, so a file that has not been regenerated from the pinned commit fails CI, except
for the files listed in `extractor/pending.txt` (see "What is proved").

Gadgets are extracted through small wrapper airs that call the gadget's `eval` on a column
layout of the same width; a test checks that each wrapper uses every column it declares.

What remains trusted: the extractor's printer (`extractor/src/render.rs`), and that Pico's
symbolic builder records what the prover enforces.

### A2. The RISC-V specification

Opcode behaviour is the Lean translation of the official Sail RISC-V model
([`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean), pinned in
`lake-manifest.json`). It declares some functions as axioms (floating point, random bits,
reservations, platform output). They are listed in `scripts/fv-check/spec-axioms.txt`. They
appear among the equivalence theorems' axioms because the specification's step function mentions
them, but the theorems hold for every interpretation of them.

### A3. Hypotheses of the theorems

Each equivalence theorem assumes the following, as last recorded at `353238a`. None is checked
while the CPU chip moves, and all three items change at v3.1.1: the constraints become the
v3.1.1 CPU chip's, the bus assumptions move to the v3.1.1 contracts
(`RV64IM_Interactions.V3` in `RVSail/BusesV3.lean`), and the theorems gain a whole-trace
assumption, described after the list:

- the CPU chip's extracted constraints hold on every row;
- the bus assumptions (`bus_row_axioms`, `bus_row_ext_asm`, `bus_row_wf_asm`, `bus_row_wf_asrt`
  in `PicoFV/RV64IM/RVSail/Buses.lean`): what the other chips deliver for the messages this row
  sends, and the well-formedness of what it receives;
- the hypotheses of the operations the row emits, and `RISC_V_assumptions` on the machine state.

The whole-trace assumption, `pico_CpuChip_control_flow_assumptions`, bounds the chunk's final
pc (public values 43 and 44): two 16-bit pieces, a multiple of 4 and below `0x7800_0000`. The
v3.1.1 chip does not check this itself; Pico's recursion circuit makes it hold for every chunk
of an accepted recursive proof (`docs/cpu-chip-pico-v3-design.md`, "The whole-trace
assumption"). So at v3.1.1 the instruction theorems cover a chunk inside an accepted recursive
proof, not a chunk proof checked on its own. The eight branch and jump theorems already name the
assumption, whose definition grows, so their recorded statements keep their text; the other 54
gain it as a new hypothesis.

A change that weakens or strengthens a hypothesis changes `signatures.txt`, and `check.sh` fails
until the change is reviewed and recorded. A change to the definition behind a hypothesis's name
does not, so it has to be listed in the pull request that makes it.

### A4. Composition of the chips (not proven)

Each chip is verified on its own, against the bus assumptions. That the assumptions one chip
makes are discharged by what the other chips prove relies on Pico's LogUp argument balancing
every bus, and on each message being served by a chip whose specification is proven. Neither is
proven here.

The contract now covers the merged branch-comparison rows. `ALUBus.validOpcode` contains the two
opcodes 264 / 265 (`SLT` / `SLTU` + `LT_CMP_OPCODE_TAG`) that Pico's CPU sends for every branch,
`ALUBus.Spec` gives them their meaning — piece 0 is `[b < c]`, piece 1 is `[c < b]`, pieces 2 and
3 are zero — and `LtChip.Spec.spec_CMP_SLT` / `spec_CMP_SLTU` prove that `LtChip` serves them.
What the CPU does with the two bits is not proven here: that is the CPU chip's side. Its
v3.1.1 constraints, including the comparison message and the taken-branch condition, are
restated in `Constraints/CpuChip.lean`, but the branch theorems that use them are parked while
the CPU chip moves.

Messages a chip serves but the contract does not specify are still not covered in general; there
are none among the RV64IM ALU chips at the pinned commit.

### A5. What is not covered

`ECALL` and syscalls, the precompile chips, the program, global memory and memory
initialisation chips, the recursion layers, and Pico's proof system itself.

### A6. The instruction decoder (Pico v3.1.1)

The Pico v3.1.1 Program contract
(`RV64IM_Interactions.V3.ProgramBusEntry.operand_properties` in
`PicoFV/RV64IM/RVSail/BusesV3.lean`; the 2.x contract of the same short name is in `Buses.lean`)
says that a fetched instruction is the row the Lean decoder `Transpiler.V3.transpile_op`
(`PicoFV/RV64IM/Transpiler/TranspilerV3.lean`) gives some Sail instruction at a 4-aligned
address below `0x7800_0000`. That decoder models Pico's decoder
(`vm/src/compiler/riscv/disassembler/rrs.rs`) and Program table builder
(`vm/src/chips/chips/riscv_program/traces.rs`) at the pinned commit. Only review compares the
Lean decoder with the Rust one; Pico's own decoder tests are restated as `example`s at the end
of `TranspilerV3.lean`. The decoder starts from an already-decoded Sail instruction, not from
the 32-bit word: that a word decodes to the same instruction in Sail and in Pico is not
modelled.

The fences have no row of their own. Pico runs every fence word (`fence`, `fence.tso` and
`pause`) as the no-op `ADD x0, x0, 0`, the row of `ADDI x0, x0, 0`. Sail decodes them as three
other instructions, `FENCE`, `FENCE_TSO` and `PAUSE`, and `PicoFV/RV64IM/RVSail/Opcodes/fence.lean`
proves that each executes exactly as `ADDI x0, x0, 0`: `PAUSE` and `FENCE_TSO` in every state,
`FENCE` in machine mode (assumption A1.1 of `RISC_V_assumptions`, which every instruction
theorem already makes).

## C. Is each proof sound?

### C1. Kernel and axioms

Proofs are checked by the Lean kernel. An axiom is a statement Lean accepts without proof. The
axioms each top-level theorem depends on are
collected by `check.sh` and must come from Lean's core axioms (including the compiler axioms of
C2) or the specification axioms of A2.

<!-- generated: axioms -->
| Axioms the theorem depends on | Theorems |
|---|---:|
| kernel + compiler | 78 |
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
165 uses of `native_decide`, `bv_decide` or `decide +native` in 16 files:

- `PicoFV/Fundamentals/Core.lean`: 7
- `PicoFV/Fundamentals/KoalaBear.lean`: 1
- `PicoFV/Fundamentals/Word.lean`: 39
- `PicoFV/RV64IM/Equivalence/Addiw.lean`: 1
- `PicoFV/RV64IM/Equivalence/BType.lean`: 6
- `PicoFV/RV64IM/Equivalence/IType.lean`: 6
- `PicoFV/RV64IM/Equivalence/Jumps.lean`: 8
- `PicoFV/RV64IM/Equivalence/Loads.lean`: 7
- `PicoFV/RV64IM/Equivalence/ShiftIOp.lean`: 3
- `PicoFV/RV64IM/Equivalence/ShiftIWOp.lean`: 3
- `PicoFV/RV64IM/Equivalence/Stores.lean`: 4
- `PicoFV/RV64IM/Equivalence/UType.lean`: 2
- `PicoFV/RV64IM/RVSail/Execution.lean`: 3
- `PicoFV/RV64IM/Spec/BitwiseChip.lean`: 1
- `PicoFV/RV64IM/Spec/DivRemChip.lean`: 1
- `PicoFV/RV64IM/Spec/MemoryReadWriteChip.lean`: 73
<!-- end generated -->

### C3. Declarations the kernel did not check

A weekly CI job (`.github/workflows/replay.yml`) replays the declarations of every module the
build imports into the kernel with `leanchecker`, except the modules listed in C2: the kernel
cannot replay what those tactics computed. Today that excludes `Fundamentals/Core`,
`Fundamentals/KoalaBear`, `Fundamentals/Word`, `RVSail/Execution` and the specifications of the
Bitwise, DivRem and memory chips; the replay covers the remaining modules, including the other
ALU chips' specifications. Modules the build does not import, such as the parked equivalence
files, are not replayed.

## D. Does the use of the results hold together?

### D1. Dependencies

The Lean dependencies are pinned in `lake-manifest.json`; the extractor's Pico and Plonky3
dependencies in `extractor/Cargo.toml` and `extractor/Cargo.lock`. A proof says nothing about a
Pico build from another commit.
