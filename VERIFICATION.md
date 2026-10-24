# Verification record

Toolchain: Lean v4.35.0-rc3; Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`.

Run `./scripts/check.sh` to reproduce:

- `lake build --wfail`: strict solution compilation.
- `lake build Audit --wfail`: the four-result axiom audit and boundary checks.
- `lake build Challenge`: independent statements; four expected placeholder warnings.
- `lake comparator --config comparator.json`: four matching theorem types, three matching
  definitions, and acceptance by NanoDa and Lean's default kernel.

The solution has no placeholders or custom axioms. Every selected theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`. Challenge imports only Mathlib and repeats
the complete definitions of uniformity, restricted intersections, and the actual
intersection spectrum. Its four theorem placeholders are intentional and occur in no
definition. No library proof imports Challenge.

The main result's hypotheses are only finite sets, uniformity, allowed intersection sizes
strictly below k, and the distinct-pair intersection condition. Linear independence,
nonzero diagonal values, the homogeneous-spanning identity, and the dimension bound are
proved internally. The spectrum formulation removes the need to specify L manually.

The audit checks k = 0 on an empty ground set, all two-subsets of four points (six
members, attaining the bound), and a five-member nonuniform counterexample on four
points with intersection spectrum {0}. Finite calculations use kernel-reduced `decide`;
`native_decide` is not used.

Successful local logs are stored in `verification/`. The prepared remote workflows use
strict Lean CI and the official full Palomar pipeline pinned at
`c02bbeaed888df45c4e28c4e99dba540ad21552a`, profile `palomar-standard-v1`. A prepared
workflow is not a completed remote check. Consult the published run results for that
evidence. Preflight is not registry registration or independent human review.
