# Verification record

Toolchain: Lean v4.35.0-rc3; Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

Run `./scripts/check.sh` to reproduce:

- `lake build --wfail`: strict solution compilation.
- `lake build Audit --wfail`: eight-result axiom audit and boundary checks.
- `lake build Challenge`: independent statements; eight expected placeholder warnings.
- `lake comparator --config comparator.json`: eight matching theorem types, three
  matching definitions, and acceptance by NanoDa and Lean's default kernel.

Every selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Challenge imports only Mathlib and repeats all three custom definitions. Its eight
intentional theorem placeholders occur in no definition. Proof modules have no
placeholders, no custom axioms, and no import of Challenge.

The four previous RCW contracts and proofs remain unchanged. The new main theorem
assumes a prime p, a residue set L with |L| ≤ k, uniformity, exclusion of k mod p
from L, and the distinct-pair intersection condition. Integer and rational
determinant nonvanishing, rational independence, degree membership, and the sharp
dimension bound are all proved internally. No condition k mod p ≥ |L| is imposed.

New audit cases:

- Six two-subsets of four points, p = 3, L = {0,1}, attaining the bound.
- Triples of four points, p = 3, L = {1,2}, with k mod p = 0 < |L|.
- A singleton empty block on an empty ground set at zero degree.
- A counterexample if the necessary condition |L| ≤ k is removed.
- Disjoint blocks of sizes two and three, modulo five, for the nonuniform theorem.
- The coloring theorem rules out a one-color assignment to all pairs of four points.

All previous RCW checks remain. Calculations use proof tactics and kernel-reduced
`decide`; `native_decide` is not used. Successful local checks are recorded in
`verification/local-checks.log`.

Remote workflows use strict Lean CI and the official full Palomar pipeline pinned
at `c02bbeaed888df45c4e28c4e99dba540ad21552a`, profile `palomar-standard-v1`,
request identifier `franklwilson`. Consult published run results for remote status.
Preflight is not registry registration or independent human review.
