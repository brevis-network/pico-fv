# Formal verification of the Brevis Pico RISC-V zkVM

This repository contains an infrastructure for formal verification of the Brevis Pico RISC-V chips in Lean (v4.28.0-rc1), together with Lean proofs that the Pico implementations of all 45 of the RISC-V RV32IM opcodes satisfy their RISC-V specifications, as per the [Official Lean RISC-V specification](https://github.com/NethermindEth/sail-riscv-lean/tree/v4.28.0-rc1). These are, specifically:
- all 27 opcodes related to the functionalities of the ALU: `ADD`, `ADDI`, `SUB`, `XOR`, `XORI`, `OR`, `ORI`, `AND`, `ANDI`, `SLT`, `SLTI`, `SLTU`, `SLTUI`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI`, `MUL`, `MULH`, `MULHU`, `MULHSU`, `DIV`, `DIVU`, `REM`, and `REMU`;
- all 10 opcodes related to handling of control flow: `AUIPC`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `JAL`, `JALR`, and `LUI`; and
- all 8 opcodes related to memory manipulation: `LW`, `LH`, `LHU`, `LB`, `LBU`, `SW`, `SH`, and `SB`.

## Repository structure

This repository is structured as follows:
- the [`PicoFV/Fundamentals`](PicoFV/Fundamentals) folder contains a number of files that underpin the infrastructure:
  - [`Core.lean`](PicoFV/Fundamentals/Core.lean), which contains useful lemmas about Lean lists, bit-vectors, and integers;
  - [`Execution.lean`](PicoFV/Fundamentals/Execution.lean), for simplifying reasoning about the Lean RISC-V specification;
  - [`Interaction.lean`](PicoFV/Fundamentals/Interaction.lean), for formalising general bus interactions;
  - [`KoalaBear.lean`](PicoFV/Fundamentals/KoalaBear.lean), for reasoning about the `KoalaBear` finite field, which is used by Pico;
  - [`U32.lean`](PicoFV/Fundamentals/U32.lean), for reasoning about 32-bit words.
- the [`PicoFV/RV32D`](PicoFV/RV32D) folder contains a number of auxiliary functions that ease the reasoning about the Lean RISC-V specification, as well as the pure and effectful specifications for all of the RV32IM opcodes.

## Building the repository

Assuming that an installation of Lean's `lake` package manager is present on the system,
the infrastructure and all of the proofs can be built using:
```
lake update
lake exe cache get!
lake build
```
in the root folder of the repository, where the first two lines are in principle superfluous but allow
for a faster initial build.
