# Reporting a soundness gap

A gap found here is usually a gap in Pico itself: a constraint too weak for a chip to compute what
it claims, which a malicious prover could exploit. The pinned Pico revision is a release, so treat
a suspected gap as a vulnerability.

- Report it privately with GitHub's
  [private vulnerability reporting](https://github.com/brevis-network/pico-fv/security/advisories/new)
  for this repository. Do not open a public issue or pull request about it, and do not push a
  branch that shows it.
- Include the chip, the Pico file and line at the pinned commit, the constraint you expected, and
  what you tried in the proof.

## Is it a gap or a proof problem?

A proof that fails is not yet a gap. It is a gap when the extracted constraints admit a row whose
bus messages break the bus contract. To decide:

- Check whether the same reasoning worked before the move (`git log` the chip's `Spec/` file) and
  what changed in the extraction.
- Try to write the counterexample: concrete column values that satisfy every extracted constraint
  but violate the statement being proved. If you can, it is a gap; report it with the values.
- If the proof only needs a hypothesis the contract does not give, that is a contract question,
  not necessarily a gap. Raise it in the chip's issue.

A gap that Pico has not fixed is recorded in [`docs/rv64-bug-mapping.md`](docs/rv64-bug-mapping.md)
only after it has been fixed or disclosed.
