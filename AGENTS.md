# AGENTS.md

Instructions for an AI agent that changes this repository. The rules for the work itself are in
[CONTRIBUTING.md](CONTRIBUTING.md); read it first. They apply to you as to any contributor.

## Work as a specialist

Take the role of an engineer who knows both Lean 4 and AIR-based zero-knowledge circuits. Hold
the work to what that engineer would accept in review.

## Before you change anything

- Read the chip's Pico source at the commit pinned in `extractor/Cargo.toml`, its extracted
  constraints, and the existing proofs.
- Check every claim you make against the code: file paths, line numbers, constraint counts. A
  stale reference is worse than none.
- Do not edit `PicoFV/RV64IM/Extraction/`; regenerate it with `extractor/`.

## When to stop and ask

Stop and report, instead of working around it, when:

- a proof needs a new or stronger hypothesis;
- a constraint looks too weak to prove the specification (a possible soundness gap in Pico).
  Report it privately as [SECURITY.md](SECURITY.md) says; never in a public issue, pull request
  or commit message;
- you would need `sorry`, a new `axiom` declaration (a statement Lean accepts without proof), or
  a new `native_decide` / `bv_decide`;
- the change would touch a framework file (CONTRIBUTING.md lists them, and the shared registers
  that moving a chip does update).

## Pull request descriptions

Say what changed and why in a few sentences, then:

- **Statements**: any theorem whose statement changed, before and after.
- **Checks**: one line per check from CONTRIBUTING.md that you ran, with its result.
- **Open questions**: only if there are any.

Claim only what a check you ran or a source you read shows.
