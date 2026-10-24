/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod

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

end IntersectionBounds
