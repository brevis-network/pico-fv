# Formal verification of the Brevis Pico RISC-V zkVM

This repository contains a Lean 4 (v4.28.0-rc1) formalisation of the Brevis Pico
RISC-V zkVM and end-to-end equivalence proofs between every Pico chip's
constraint system and the corresponding [Official Lean RISC-V
specification](https://github.com/NethermindEth/sail-riscv-lean/tree/v4.28.0-rc1).

The development covers the **RV64IM** variant of Pico. All 62 opcodes in the
RV64IM ISA are equivalence-proven:
  - 27 ALU opcodes: `ADD`, `ADDI`, `SUB`, `XOR`, `XORI`, `OR`, `ORI`, `AND`,
    `ANDI`, `SLT`, `SLTI`, `SLTU`, `SLTIU`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`,
    `SRAI`, `MUL`, `MULH`, `MULHU`, `MULHSU`, `DIV`, `DIVU`, `REM`, `REMU`;
  - 10 control-flow opcodes: `AUIPC`, `LUI`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`,
    `BGEU`, `JAL`, `JALR`;
  - 11 memory opcodes: `LW`, `LH`, `LHU`, `LB`, `LBU`, `SW`, `SH`, `SB`, and
    the RV64 additions `LWU`, `LD`, `SD` (`LW` sign-extends per the RV64 spec);
  - 5 word-variant ALU opcodes: `ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`;
  - 4 word-variant immediate opcodes: `ADDIW`, `SLLIW`, `SRLIW`, `SRAIW`;
  - 5 word-variant MUL/DIV opcodes: `MULW`, `DIVW`, `DIVUW`, `REMW`, `REMUW`.

`ECALL` is intentionally out of scope.

The extraction tool in `extractor/` is pinned to Pico v3.1.1. Each proof is about the Pico
revision named in the first line of the `PicoFV/RV64IM/Extraction/` file it uses; the files
listed in `extractor/pending.txt` still predate v3.1.1 and are being moved chip by chip.
[SOUNDNESS.md](SOUNDNESS.md) says what the proofs establish and what they trust.

For each opcode, the equivalence theorem states: under the chip's row
constraints, bus assumptions, and program well-formedness, executing one Sail
step of the corresponding instruction produces the same post-state as
applying the chip's emitted CPU-bus operations.

In the course of this development, 13 chip-side soundness gaps were found in
the Pico implementation, across `LtChip`, `ShiftRightChip`, `SLLChip`,
`JalrChip`, `DivRemChip`, and `MemoryReadWriteChip` (see `Report.pdf`). Which
Pico 3.x constraint closes each of them is being recorded as the chips move to
v3.1.1.

### RV32IM (historical)

An RV32IM development of all 45 RV32IM base opcodes used to live alongside
RV64IM. It matches Pico v1.x only and is no longer maintained here; it is
preserved upstream at
[NethermindEth/pico-fv@a7f9a09](https://github.com/NethermindEth/pico-fv/tree/a7f9a0976e245aeef89c3f02c51ae85023207b53).

## Repository structure

```
PicoFV/
├── Fundamentals/        — shared infrastructure
│   ├── Core.lean        — lemmas about lists, bit-vectors, integers, hash maps
│   ├── Interaction.lean — generic bus interactions (typeclass-driven)
│   ├── KoalaBear.lean   — the KoalaBear finite field (FKB = Fin 2 130 706 433)
│   └── Word.lean        — u32/u64 byte- and limb-level representations
└── RV64IM/              — RV64IM development
    ├── Airs/            — chip column / row layouts
    ├── Constraints/     — extracted constraint definitions per chip
    ├── Extraction/      — auto-extracted chip data from Pico
    ├── RVSail/          — Sail-side glue + per-opcode pure / effectful specs
    ├── Spec/            — hand-written chip specifications & bus equivalences
    ├── Transpiler/      — instruction → chip-row encoding
    └── Equivalence/     — per-opcode equivalence theorems, one file per instruction class
Extensions/              — reserved for syscalls and precompiles (empty)
extractor/               — regenerates RV64IM/Extraction/ from Pico's source
scripts/fv-check/        — theorem, layer, tactic and SOUNDNESS checks
```

Within `RV64IM/Spec/` (and `Constraints/`), each chip used by Pico
has its own file: ALU chips (`AddChip`, `SubChip`, `BitwiseChip`, `LtChip`,
`SLLChip`, `ShiftRightChip`, `MulChip`, `DivRemChip`), the CPU chip
(`CpuChip`), the memory chip (`MemoryReadWriteChip`), and any
chip-local gadgets (`AddGadget`, `SubGadget`, `MulGadget`,
`IsZeroGadget`, `LtSignedGadget`, …).

Within `RV64IM/RVSail/Opcodes/`, every opcode has its own file
containing the pure functional spec and the effectful Sail spec, along
with the bridge lemmas between them.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md) (and [AGENTS.md](AGENTS.md) for AI agents) first. Each
chip's files are independent of the other chips', so a chip can be moved or extended in its own
pull request; shared files and tooling change in separate ones.

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
listed in `scripts/fv-check/theorems.d/` (the 62 opcode equivalence theorems,
one file per instruction class, and the memory chip's `spec_*` / `bus_equiv*`
theorems). It fails if a theorem
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

More checks run in CI: `check_layers.sh` (no chip imports another chip),
`check_tactics.sh` (uses of `native_decide` / `bv_decide` / `decide +native` only go down),
`soundness_facts.py --check` (the generated facts in `SOUNDNESS.md` are current), and
`extractor --check` (the extraction files match the pinned Pico).

## Soundness audit

The 13 RV64IM soundness gaps found during the formalisation are described in
`Report.pdf` and, for the memory chip, in
[`RV64_MemoryReadWriteChip_soundness_gaps.md`](RV64_MemoryReadWriteChip_soundness_gaps.md).
