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

#print axioms IntersectionBounds.franklWilson
#print axioms IntersectionBounds.franklWilson_nonuniform
#print axioms IntersectionBounds.franklWilson_forbidden_residue
#print axioms IntersectionBounds.franklWilson_coloring_bound

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

noncomputable local instance : DecidableEq (Fin 4) := Classical.decEq _
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Sharp modular example: all pairs on four points, p = 3, L = {0,1}.
open Classical in
example : ((univ : Finset (Fin 4)).powersetCard 2).card ≤ 6 := by
  classical
  have h := franklWilson 3 ((univ : Finset (Fin 4)).powersetCard 2) {0, 1} 2
    (sharp_example (V := Fin 4) 2).1 (by decide) (by decide) (by
      intro A hA B hB hne
      have hi := intersection_lt_of_uniform _ 2 (sharp_example (V := Fin 4) 2).1 A B hA hB hne
      have hz : (A ∩ B).card = 0 ∨ (A ∩ B).card = 1 := by omega
      rcases hz with hz | hz <;> simp [hz])
  simpa only [show ({0, 1} : Finset (ZMod 3)).card = 2 by decide,
    Fintype.card_fin, show Nat.choose 4 2 = 6 by decide] using h

-- k mod p is zero and below |L|: no extra modular homogenization condition.
open Classical in
example : ((univ : Finset (Fin 4)).powersetCard 3).card ≤ 6 := by
  classical
  have h := franklWilson 3 ((univ : Finset (Fin 4)).powersetCard 3) {1, 2} 3
    (sharp_example (V := Fin 4) 3).1 (by decide) (by decide) (by
      intro A hA B hB hne
      have hi := intersection_lt_of_uniform _ 3 (sharp_example (V := Fin 4) 3).1 A B hA hB hne
      have hAc := (Finset.mem_powersetCard.mp hA).2
      have hBc := (Finset.mem_powersetCard.mp hB).2
      have hu : (A ∪ B).card ≤ 4 := Finset.card_le_univ _
      have hid := Finset.card_union_add_card_inter A B
      have hz : (A ∩ B).card = 2 := by omega
      simp [hz])
  simpa only [show ({1, 2} : Finset (ZMod 3)).card = 2 by decide,
    Fintype.card_fin, show Nat.choose 4 2 = 6 by decide] using h

-- Zero degree, empty ground set, and a nonempty singleton family.
example : ({∅} : Finset (Finset (Fin 0))).card ≤ 1 := by
  classical
  have h := franklWilson 2 ({∅} : Finset (Finset (Fin 0))) ∅ 0
    (by simp [Uniform]) (by simp) (by simp) (by simp)
  simpa only [Finset.card_empty, Nat.choose_zero_right] using h

-- Without |L| ≤ k the main claim is false, even for a singleton family.
open Classical in
example : Uniform ({∅} : Finset (Finset (Fin 0))) 0 ∧
    (0 : ZMod 2) ∉ ({1} : Finset (ZMod 2)) ∧
    (∀ A ∈ ({∅} : Finset (Finset (Fin 0))), ∀ B ∈ ({∅} : Finset (Finset (Fin 0))),
      A ≠ B → ((A ∩ B).card : ZMod 2) ∈ ({1} : Finset (ZMod 2))) ∧
    ¬ (({∅} : Finset (Finset (Fin 0))).card ≤
      (Fintype.card (Fin 0)).choose ({1} : Finset (ZMod 2)).card) := by simp [Uniform]

-- Disjoint blocks of sizes two and three: a genuinely nonuniform application.
open Classical in
example {W : Type} [Fintype W] (A B : Finset W)
    (hA : A.card = 2) (hB : B.card = 3) (hd : Disjoint A B) :
    ({A, B} : Finset (Finset W)).card ≤
      ∑ i ∈ range 2, (Fintype.card W).choose i := by
  classical
  apply franklWilson_nonuniform 5 _ ({0} : Finset (ZMod 5))
  · intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · rw [hA]; decide
    · rw [hB]; decide
  · intro C hC D hD hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC hD
    rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
    · exact (hne rfl).elim
    · simp [Finset.disjoint_iff_inter_eq_empty.mp hd]
    · simp [Finset.disjoint_iff_inter_eq_empty.mp hd.symm]
    · exact (hne rfl).elim

-- A single color cannot color all pairs of a four-point set with the required exclusion.
open Classical in
example (c : Finset (Fin 4) → Fin 1)
    (hc : ∀ A B : Finset (Fin 4), A.card = 2 → B.card = 2 → A ≠ B → c A = c B →
      ((A ∩ B).card : ZMod 2) ≠ (2 : ZMod 2)) : False := by
  have h := franklWilson_coloring_bound 2 2 1 (by decide) c hc
  norm_num [Nat.choose] at h

end Audit
