# Ray-Chaudhuri–Wilson: uniform families with restricted intersections

Lean 4 formalization of **Theorem 3** of D. K. Ray-Chaudhuri and R. M. Wilson,
*On t-designs*, Osaka Journal of Mathematics 12 (1975), 737–744.
The [open paper](https://www.i-repository.net/contents/osakacu/sugaku/111F0000002-01203-15.pdf)
and its [institutional record](https://doi.org/10.18910/7296) were consulted.

Let F be a family of k-element subsets of an n-element ground set. Let L be a finite
set of integers in {0, …, k−1}. If every intersection of two distinct members has
cardinality in L, then

\[
|F|\leq\binom{n}{|L|}.
\]

Zero is an allowed intersection size. Empty families, empty ground sets, and k = 0
are included. No additional dimension, nonsingularity, or polynomial hypothesis is
assumed. The condition |L| ≤ k follows from L ⊆ {0, …, k−1}.

## Selected statements

All statements are in namespace `IntersectionBounds`.

| Theorem | Scope |
| --- | --- |
| `rayChaudhuriWilson` | The sharp uniform L-intersection bound above |
| `card_le_choose_spectrum` | The same bound using exactly the intersection cardinalities that occur |
| `uniform_fisher` | If every distinct pair intersects in the same l < k points, then |F| ≤ n |
| `sharp_example` | All s-subsets, with L = {0, …, s−1}, attain \(\binom ns\) |

`Uniform F k` explicitly means that every member has cardinality k. `IntersectionsIn F L`
quantifies over distinct members. `intersectionSpectrum F` takes the image of the
off-diagonal pairs. These definitions are repeated independently in `Challenge.lean`.
Members are finite subsets of a finite type; a family has no repeated blocks.

This covers the intersection theorem and the stated consequences. The paper's lower
bounds on the number of blocks of t-designs, tight-design classification, and arithmetic
conditions are outside this scope. The one-intersection corollary here is a bound on
uniform set families, rather than a formalization of the entire theory of Fisher inequalities.

## Proof and reuse

The proof uses Mathlib finite sets, spans, linear independence, finite-dimensional
linear algebra, and rational arithmetic. The project defines evaluations of squarefree
monomials, `indicator T B = 1` when T ⊆ B and 0 otherwise. Multiplication corresponds
to taking the union of monomial supports. Their span up to degree d contains the
separating products

\[
f_A(B)=\prod_{l\in L}(|A\cap B|-l).
\]

Off the diagonal these evaluations vanish; on the diagonal they are nonzero. Thus
the separating functions are linearly independent. Uniformity supplies the identity

\[
(k-|T|)\,\mathrm{indicator}_T
=\sum_{a\notin T}\mathrm{indicator}_{T\cup\{a\}}.
\]

Over the rationals, it expresses every lower-degree evaluation as a combination of
degree-exactly-|L| evaluations. At most \(\binom n{|L|}\) such monomials exist, giving
the dimension bound and the theorem. This evaluation-space proof differs from the
original paper's matrix argument.

`EvaluationSpace.lean` and `Separation.lean` work over an arbitrary field, including
positive characteristic. The uniform homogenization step additionally uses characteristic
zero. This isolates reusable infrastructure for future modular intersection theorems;
Frankl–Wilson is not assumed or claimed by this package.

## Verification

Pinned toolchain: Lean `v4.35.0-rc3`; Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. Run:

```sh
./scripts/check.sh
```

Strict compilation, an axiom/boundary audit, and sandboxed Comparator pass locally.
Comparator checks four theorem types and three explicit definitions against an
independent Challenge. Both Lean's default kernel and NanoDa accept the solution.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Challenge contains four intentional theorem placeholders; definitions and proof modules
contain none. No custom axioms are used.

`Audit.lean` includes the empty-set case, equality with all six pairs of four points,
and a nonuniform counterexample: the empty set and four singletons have all pairwise
intersection sizes zero but five members, exceeding \(\binom41\). Thus uniformity is
a material hypothesis. Calculations use kernel-checked `decide` and proof tactics.

See [formalization.yaml](formalization.yaml), [VERIFICATION.md](VERIFICATION.md), and
[MATHLIB_DEFINITIONS.md](MATHLIB_DEFINITIONS.md). The prepared GitHub workflows run strict
CI and the official full Palomar mechanical preflight; their run results determine
remote verification status. Preflight does not itself submit or register an entry.

Author and responsible maintainer: Juan Pablo Traverso Gianini. New proofs and packaging
were produced with OpenAI Codex using Mathlib infrastructure. No independent human
mathematical review or mathematical novelty is claimed. License: Apache-2.0.
