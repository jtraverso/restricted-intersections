/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

import Solution

open Finset IntersectionBounds

#print axioms IntersectionBounds.rayChaudhuriWilson
#print axioms IntersectionBounds.card_le_choose_spectrum
#print axioms IntersectionBounds.uniform_fisher
#print axioms IntersectionBounds.sharp_example

namespace Audit

-- The zero-degree case is included: one empty block on an empty ground set.
example : Uniform ({∅} : Finset (Finset (Fin 0))) 0 := by simp [Uniform]

example : IntersectionsIn ({∅} : Finset (Finset (Fin 0))) ∅ := by
  simp [IntersectionsIn]

example : ({∅} : Finset (Finset (Fin 0))).card ≤ (Fintype.card (Fin 0)).choose 0 := by
  exact rayChaudhuriWilson ({∅} : Finset (Finset (Fin 0))) ∅ 0
    (by simp [Uniform]) (by simp) (by simp [IntersectionsIn])

-- Zero is an allowed intersection size, and all two-subsets of four points attain six.
example : ((univ : Finset (Fin 4)).powersetCard 2).card = 6 := by decide

example : IntersectionsIn ((univ : Finset (Fin 4)).powersetCard 2) (range 2) :=
  (sharp_example (V := Fin 4) 2).2.1

example : ((univ : Finset (Fin 4)).powersetCard 2).card ≤ 6 := by
  have h := rayChaudhuriWilson ((univ : Finset (Fin 4)).powersetCard 2) (range 2) 2
    (sharp_example (V := Fin 4) 2).1 (by simp) (sharp_example (V := Fin 4) 2).2.1
  simpa only [Finset.card_range, Fintype.card_fin, show Nat.choose 4 2 = 6 by decide] using h

-- Uniformity is necessary: the empty set and all four singletons violate the n bound.
def nonuniform : Finset (Finset (Fin 4)) := {∅, {0}, {1}, {2}, {3}}

example : nonuniform.card = 5 := by decide

example : IntersectionsIn nonuniform {0} := by
  simp [nonuniform, IntersectionsIn]

example : ¬ Uniform nonuniform 1 := by
  simp [nonuniform, Uniform]

example : nonuniform.card > (Fintype.card (Fin 4)).choose ({0} : Finset ℕ).card := by decide

end Audit
