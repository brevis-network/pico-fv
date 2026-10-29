# Formal verification of the Brevis Pico RISC-V zkVM

This repository contains a Lean 4 (v4.28.0-rc1) formalisation of the Brevis Pico
RISC-V zkVM and end-to-end equivalence proofs between every Pico chip's
constraint system and the corresponding [Official Lean RISC-V
specification](https://github.com/NethermindEth/sail-riscv-lean/tree/v4.28.0-rc1).

The development covers both the **RV32IM** and **RV64IM** variants of Pico:

- **RV32IM** — all 45 opcodes in the RV32IM base ISA are equivalence-proven:
  - 27 ALU opcodes: `ADD`, `ADDI`, `SUB`, `XOR`, `XORI`, `OR`, `ORI`, `AND`,
    `ANDI`, `SLT`, `SLTI`, `SLTU`, `SLTIU`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`,
    `SRAI`, `MUL`, `MULH`, `MULHU`, `MULHSU`, `DIV`, `DIVU`, `REM`, `REMU`;
  - 10 control-flow opcodes: `AUIPC`, `LUI`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`,
    `BGEU`, `JAL`, `JALR`;
  - 8 memory opcodes: `LW`, `LH`, `LHU`, `LB`, `LBU`, `SW`, `SH`, `SB`.

- **RV64IM** — all 62 opcodes in the RV64IM ISA are equivalence-proven:
  - the 45 RV32IM opcodes above (with `LW` now signed-extended per the
    RV64 spec);
  - 5 word-variant ALU opcodes: `ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`;
  - 4 word-variant immediate opcodes: `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`;
  - 5 word-variant MUL/DIV opcodes: `MULW`, `DIVW`, `DIVUW`, `REMW`, `REMUW`;
  - 3 new memory opcodes: `LWU`, `LD`, `SD`.

`ECALL` is intentionally out of scope.

For each opcode, the equivalence theorem states: under the chip's row
constraints, bus assumptions, and program well-formedness, executing one Sail
step of the corresponding instruction produces the same post-state as
applying the chip's emitted CPU-bus operations.

In the course of this development, several chip-side soundness gaps
were surfaced in the Pico implementation:

- **RV64IM** — 13 gaps across `LtChip`, `ShiftRightChip`, `SLLChip`,
  `JalrChip`, `DivRemChip`, and `MemoryReadWriteChip`. **All 13 closed
  upstream** by Pico PR #101.
- **RV32IM** — 1 gap remains in `MemoryReadWriteAir`: the chip does
  not enforce `addr_aligned ≥ 32` (the analogue of the RV64
  `addr_aligned` gap that PR #101 closed for RV64). The
  `bus_equiv` lemma in `RV32IM/Spec/MemoryReadWriteAir.lean` takes
  it as an explicit hypothesis pending an upstream fix.

## Repository structure

```
PicoFV/
├── Fundamentals/        — shared infrastructure
│   ├── Core.lean        — lemmas about lists, bit-vectors, integers, hash maps
│   ├── Interaction.lean — generic bus interactions (typeclass-driven)
│   ├── KoalaBear.lean   — the KoalaBear finite field (FKB = Fin 2 130 706 433)
│   └── Word.lean        — u32/u64 byte- and limb-level representations
├── RV32IM/              — RV32IM development (mirrors RV64IM)
│   ├── Airs/            — chip column / row layouts
│   ├── Constraints/     — extracted constraint definitions per chip
│   ├── Extraction/      — auto-extracted chip data from Pico
│   ├── RVSail/          — Sail-side glue + per-opcode pure / effectful specs
│   ├── Spec/            — hand-written chip specifications & bus equivalences
│   ├── Transpiler/      — instruction → chip-row encoding
│   └── Equivalence/     — per-opcode equivalence theorems
└── RV64IM/              — RV64IM development (same layout as RV32IM)
```

Within `RV{32,64}IM/Spec/` (and `Constraints/`), each chip used by Pico
has its own file: ALU chips (`AddChip`, `SubChip`, `BitwiseChip`, `LtChip`,
`SLLChip`, `ShiftRightChip`, `MulChip`, `DivRemChip`), the CPU chip
(`CpuChip` / `CpuAir`), the memory chip (`MemoryReadWriteChip`), and any
chip-local gadgets (`AddGadget`, `SubGadget`, `MulGadget`,
`IsZeroGadget`, `LtSignedGadget`, …).

Within `RV{32,64}IM/RVSail/Opcodes/`, every opcode has its own file
containing the pure functional spec and the effectful Sail spec, along
with the bridge lemmas between them.

## Building the repository

Assuming Lean's `lake` package manager is installed:

```
lake update
lake exe cache get!
lake build
```

The first two commands are optional but speed up the initial build by
fetching mathlib's binary cache.

## Checking the theorems

After `lake build`, `scripts/fv-check/check.sh` checks the top-level theorems
listed in `scripts/fv-check/theorems.txt` (the 62 opcode equivalence theorems
and the memory chip's `spec_*` / `bus_equiv*` theorems). It fails if a theorem
is missing, depends on an axiom outside two lists, or its axioms or statement
differ from the snapshots in `axioms.txt` and `signatures.txt`:

- Lean's core axioms: `propext`, `Classical.choice`, `Quot.sound`, and
  `Lean.ofReduceBool` / `Lean.trustCompiler`, which `native_decide` and
  `bv_decide` rely on (they trust Lean's compiler to evaluate decidable
  propositions);
- `spec-axioms.txt`: functions the Lean RISC-V specification declares as
  axioms (floating point, random bits, reservations, platform output). The
  equivalence theorems hold for any interpretation of them.

So a `sorry`, or an axiom of our own, fails the check. A change to a theorem's
statement shows up as a diff of `signatures.txt` for review; once reviewed,
`check.sh --update` records it.

## Soundness audit

The 13 RV64IM soundness bugs found during the formalisation —
chip name, constraint reference, fix commit, and the shape of the
failure — are documented inline in the relevant `Spec/` file headers
(see e.g. `RV64IM/Spec/ShiftRightChip.lean`,
`RV64IM/Spec/DivRemChip.lean`,
`RV64IM/Spec/MemoryReadWriteChip.lean`); all 13 are closed
upstream by Pico PR #101.

The remaining open RV32IM `MemoryReadWriteAir` gap is flagged
in-source via the `FIXME` on the explicit `ASSUMPTION` parameter
to `bus_equiv`.
