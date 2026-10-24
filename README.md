# Frankl–Wilson and Ray-Chaudhuri–Wilson intersection bounds

Lean 4 formalizations of two classical restricted-intersection results:

- P. Frankl and R. M. Wilson, *Intersection theorems with geometric consequences*,
  Combinatorica 1 (1981), 357–368, [DOI](https://doi.org/10.1007/BF02579457).
- D. K. Ray-Chaudhuri and R. M. Wilson, *On t-designs*, Osaka Journal of Mathematics
  12 (1975), 737–744, Theorem 3, [open paper](https://www.i-repository.net/contents/osakacu/sugaku/111F0000002-01203-15.pdf),
  [institutional archival DOI](https://doi.org/10.18910/7296).

## Sharp prime-modular bound

Let F be a family of k-element subsets of an n-element ground set, p a prime, and
L a set of s residues modulo p, with s ≤ k and k mod p outside L. If every distinct
pair of blocks has its intersection cardinality modulo p in L, then

**|F| ≤ binomial(n,s).**

The theorem `IntersectionBounds.franklWilson` uses `L : Finset (ZMod p)` and
`[Fact p.Prime]`. Its only hypotheses are uniformity, s ≤ k, diagonal residue
exclusion, and the distinct-pair intersection condition. It imposes no assumption
that k < p or that k mod p ≥ s. All rank and nonvanishing assertions are proved.

The condition s ≤ k is necessary with the usual convention that a binomial
coefficient vanishes above n. On an empty ground set, F = {∅}, p = 2, k = 0,
and L = {1} satisfy the other conditions but 1 > binomial(0,1).
The kernel-checked audit includes this counterexample.

## Selected statements

All eight statements are in namespace `IntersectionBounds`. The four RCW results
from the preceding version retain their definitions, statements, and proofs.

| Theorem | Scope |
| --- | --- |
| `franklWilson` | Sharp uniform prime-modular intersection bound |
| `franklWilson_nonuniform` | Without uniformity, with every block-size residue outside L: cardinality at most the sum of binomial(n,i) for 0 ≤ i ≤ s |
| `franklWilson_forbidden_residue` | If p−1 ≤ k and no distinct intersection has residue k mod p, cardinality at most binomial(n,p−1) |
| `franklWilson_coloring_bound` | An r-color assignment to all k-subsets whose monochromatic pairs exclude that residue satisfies binomial(n,k) ≤ r · binomial(n,p−1) |
| `rayChaudhuriWilson` | Uniform nonmodular L-intersection bound, with every l in L below k |
| `card_le_choose_spectrum` | RCW using exactly the intersection cardinalities that occur |
| `uniform_fisher` | Uniform one-intersection consequence: cardinality at most n |
| `sharp_example` | All s-subsets attain the RCW bound |

The coloring statement is a finite modular intersection graph consequence. The
paper's Euclidean distance graph bounds, asymptotic constants, and remaining
geometric applications are outside this delivery. Prime-power/composite moduli
and the unrestricted nonmodular nonuniform theorem are also outside scope.
`franklWilson_nonuniform` explicitly requires diagonal residue exclusion.
The RCW entry covers Theorem 3 and the displayed consequences, not the paper's
t-design lower bounds or classification of tight designs.

## Proof and reuse

The existing `EvaluationSpace`, `Separation`, and `UniformSpace` modules are reused
unchanged. They implement squarefree monomials as evaluation functions: the
indicator of T at B is 1 if T is a subset of B and 0 otherwise. Their degree-bounded
span contains products of intersection-size factors. For uniform families,
over the rationals, the identity

(k−|T|) · indicator(T) = sum over a outside T of indicator(T ∪ {a})

expresses lower-degree evaluations using degree-s monomials. There are binomial(n,s)
such monomials.

The new proof avoids dividing modulo p. It forms an **integer** matrix

M(A,B) = product over l in L of (|A ∩ B| − val(l)).

Modulo p this matrix is diagonal with nonzero diagonal entries. Its integer
determinant is therefore nonzero, as is its rational determinant. Thus the rational
lifted separator functions are linearly independent. They lie in the existing
degree-s evaluation space, and the rational homogenization gives the sharp bound.
No modular invertibility premise is added to the mathematical theorem.

`DegreeDimension.lean` additionally counts all squarefree supports of size at most
s. Together with the previous arbitrary-field separation lemma, this proves the
modular nonuniform bound. Residue complementation and counting color classes give
the remaining consequences.

The [primary publisher abstract](https://doi.org/10.1007/BF02579457) supplies the
main uniform modular assertion. A [public scan](https://www.cs.umd.edu/~gasarch/TOPICS/CRT/FW.pdf)
is available, but its pages are image-only in the available reader. Statements
and the polynomial-method context were cross-checked with Alon–Babai–Suzuki,
[*Multilinear polynomials and Frankl–Ray-Chaudhuri–Wilson type intersection theorems*](https://web.math.princeton.edu/~nalon/PDFS/suzuki1.pdf),
Theorems 1.2 and 3.1. No Lean code was copied from that exposition, and no theorem
number from the unreadable primary scan is asserted.

## Verification

Pinned Lean: `v4.35.0-rc3`. Pinned Mathlib:
`c55e6e786f49471c72fbddbec5415808896aec1e`.

```sh
./scripts/check.sh
```

Strict solution and audit compilation, eight independent theorem contracts,
three independent definitions, and sandboxed Comparator with Lean and NanoDa
are checked. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Challenge has eight intentional theorem placeholders;
definitions and proof modules have none. No proof module imports Challenge.

The audit checks the six-pair sharp modular example, k mod p below s, zero degree,
the necessity of s ≤ k, different block sizes, and an impossible one-color instance.
It retains all previous RCW boundary checks. Calculations use proof tactics and
kernel-reduced `decide`.

See [formalization.yaml](formalization.yaml), [VERIFICATION.md](VERIFICATION.md), and
[MATHLIB_DEFINITIONS.md](MATHLIB_DEFINITIONS.md). Workflows run strict Lean CI and the
official full Palomar preflight. Their published results determine remote status.
**Preflight does not submit or register an entry.**

Author and responsible maintainer: Juan Pablo Traverso Gianini. New proofs and
packaging produced with OpenAI Codex. No independent human mathematical review or
mathematical novelty is claimed. License: Apache-2.0.
