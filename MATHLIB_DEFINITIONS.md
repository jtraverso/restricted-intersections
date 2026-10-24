# Mathlib definitions used by the independent Challenge

The three custom definitions are explicitly repeated in `Challenge.lean`. These
verbatim excerpts identify the imported finite-set and counting notions at Mathlib
commit `c55e6e786f49471c72fbddbec5415808896aec1e` (Apache-2.0). Line numbers refer
to that revision. Functions, natural numbers, propositions, and finite-type instances
have their standard Lean meanings.

## Mathlib/Data/Finset/Defs.lean:75

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Finset/Defs.lean#L75)

```lean
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α
  /-- `val` contains no duplicates -/
  nodup : Nodup val
```

## Mathlib/Data/Finset/Card.lean:47

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Finset/Card.lean#L47)

```lean
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Mathlib/Data/Finset/Prod.lean:254

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Finset/Prod.lean#L254)

```lean
def offDiag : Finset (α × α) :=
  .mk (Quotient.map List.offDiag (fun _ _ ↦ List.Perm.offDiag) s.1) <| by
    rcases s with ⟨⟨s⟩, hs⟩
    exact hs.offDiag
```

## Mathlib/Data/Finset/Image.lean:279

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Finset/Image.lean#L279)

```lean
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset
```

## Mathlib/Data/Finset/Powerset.lean:198

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Finset/Powerset.lean#L198)

```lean
def powersetCard (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩
```

## Mathlib/Data/Nat/Choose/Basic.lean:50

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Nat/Choose/Basic.lean#L50)

```lean
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)
```

## Mathlib/Data/Fintype/Card.lean:39

[Source](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Data/Fintype/Card.lean#L39)

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```

Finite-set membership means membership in the underlying multiset; its no-duplicate
condition makes cardinality a count of distinct elements. Subset is pointwise
inclusion, and membership in A ∩ B means membership in both A and B. The finite
set `univ` contains every element of a Fintype. `range s` contains 0 through s−1.
`offDiag` consists exactly of pairs of distinct elements of its input family.
`powersetCard s univ` consists of every s-subset of the finite ground type.
