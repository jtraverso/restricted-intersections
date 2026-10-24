/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace IntersectionBounds

universe u
variable {V : Type u}

/-- Every member of F has cardinality k. -/
def Uniform (F : Finset (Finset V)) (k : ℕ) : Prop := ∀ A ∈ F, A.card = k

open Classical in
/-- Distinct members have intersection cardinality in L. -/
def IntersectionsIn (F : Finset (Finset V)) (L : Finset ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ∈ L

open Classical in
/-- The actual intersection cardinalities of distinct members. -/
noncomputable def intersectionSpectrum (F : Finset (Finset V)) : Finset ℕ :=
  F.offDiag.image (fun p => (p.1 ∩ p.2).card)

variable [Fintype V]

open Classical in
/-- Ray-Chaudhuri–Wilson (1975), Theorem 3. -/
theorem rayChaudhuriWilson (F : Finset (Finset V)) (L : Finset ℕ) (k : ℕ)
    (huni : Uniform F k) (hL : ∀ l ∈ L, l < k) (hinter : IntersectionsIn F L) :
    F.card ≤ (Fintype.card V).choose L.card := by sorry

/-- The bound in terms of exactly the intersection sizes that occur. -/
theorem card_le_choose_spectrum (F : Finset (Finset V)) (k : ℕ) (huni : Uniform F k) :
    F.card ≤ (Fintype.card V).choose (intersectionSpectrum F).card := by sorry

open Classical in
/-- The uniform one-intersection corollary. -/
theorem uniform_fisher (F : Finset (Finset V)) (k l : ℕ)
    (huni : Uniform F k) (hl : l < k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card = l) :
    F.card ≤ Fintype.card V := by sorry

open Classical in
/-- The full family of s-subsets attains the bound. -/
theorem sharp_example (s : ℕ) :
    let F := (Finset.univ : Finset V).powersetCard s
    Uniform F s ∧ IntersectionsIn F (Finset.range s) ∧
      F.card = (Fintype.card V).choose s := by sorry

open Classical in
theorem franklWilson (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (L : Finset (ZMod p)) (k : ℕ)
    (huni : Uniform F k) (hs : L.card ≤ k) (hk : (k : ZMod p) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L) :
    F.card ≤ (Fintype.card V).choose L.card := by sorry

open Classical in
theorem franklWilson_nonuniform (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (L : Finset (ZMod p))
    (hself : ∀ A ∈ F, (A.card : ZMod p) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L) :
    F.card ≤ ∑ i ∈ Finset.range (L.card + 1), (Fintype.card V).choose i := by sorry

open Classical in
theorem franklWilson_forbidden_residue (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (k : ℕ) (huni : Uniform F k) (hpk : p - 1 ≤ k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B →
      ((A ∩ B).card : ZMod p) ≠ (k : ZMod p)) :
    F.card ≤ (Fintype.card V).choose (p - 1) := by sorry

open Classical in
theorem franklWilson_coloring_bound (p : ℕ) [Fact p.Prime] (k r : ℕ)
    (hpk : p - 1 ≤ k) (c : Finset V → Fin r)
    (hcolor : ∀ A B : Finset V, A.card = k → B.card = k → A ≠ B → c A = c B →
      ((A ∩ B).card : ZMod p) ≠ (k : ZMod p)) :
    (Fintype.card V).choose k ≤ r * (Fintype.card V).choose (p - 1) := by sorry

end IntersectionBounds
