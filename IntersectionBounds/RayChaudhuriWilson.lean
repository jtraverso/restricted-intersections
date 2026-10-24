/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import IntersectionBounds.UniformSpace
public import IntersectionBounds.Separation
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

namespace IntersectionBounds

open Finset Submodule

universe u v
variable {V : Type u} [Fintype V]

open Classical in
theorem uniform_separation_bound {K : Type v} [Field K] [CharZero K]
    (F : Finset (Finset V)) (L : Finset K) (k : ℕ)
    (huni : Uniform F k) (hs : L.card ≤ k)
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ (Fintype.card V).choose L.card := by
  calc
    _ ≤ Module.finrank K (degreeSpace (K := K) F L.card) := card_le_finrank_degree F L hself hinter
    _ ≤ Module.finrank K (exactSpace (K := K) F L.card) :=
      Submodule.finrank_mono (degreeSpace_le_exact_of_uniform F k L.card huni hs)
    _ ≤ _ := finrank_exactSpace_le F L.card

open Classical in
/-- Ray-Chaudhuri–Wilson (1975), Theorem 3: the sharp bound for a uniform
family whose distinct intersections have sizes in L ⊆ {0, ..., k-1}. -/
theorem rayChaudhuriWilson (F : Finset (Finset V)) (L : Finset ℕ) (k : ℕ)
    (huni : Uniform F k) (hL : ∀ l ∈ L, l < k) (hinter : IntersectionsIn F L) :
    F.card ≤ (Fintype.card V).choose L.card := by
  classical
  let LR : Finset ℚ := L.image (fun l : ℕ => (l : ℚ))
  have hcard : LR.card = L.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hs : LR.card ≤ k := by
    rw [hcard]
    calc
      _ ≤ (Finset.range k).card := Finset.card_le_card (by
        intro l hl
        exact Finset.mem_range.mpr (hL l hl))
      _ = k := Finset.card_range k
  have hself : ∀ A ∈ F, (A.card : ℚ) ∉ LR := by
    intro A hA ha
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp ha
    have heq' : l = A.card := Nat.cast_injective heq
    have := hL l hl
    rw [heq', huni A hA] at this
    omega
  have hcross : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ℚ) ∈ LR := by
    intro A hA B hB hne
    exact Finset.mem_image.mpr ⟨_, hinter A hA B hB hne, rfl⟩
  simpa only [hcard] using uniform_separation_bound F LR k huni hs hself hcross

open Classical in
omit [Fintype V] in
theorem intersection_lt_of_uniform (F : Finset (Finset V)) (k : ℕ)
    (huni : Uniform F k) (A B : Finset V) (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B) :
    (A ∩ B).card < k := by
  have hle : (A ∩ B).card ≤ k := (Finset.card_le_card inter_subset_left).trans_eq (huni A hA)
  by_contra hnot
  have heq : A ∩ B = A := Finset.eq_of_subset_of_card_le inter_subset_left (by
    rw [huni A hA]
    omega)
  have hsub : A ⊆ B := by rw [← heq]; exact inter_subset_right
  exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [huni A hA, huni B hB]))

/-- A canonical form using exactly the intersection sizes that actually occur. -/
theorem card_le_choose_spectrum (F : Finset (Finset V)) (k : ℕ) (huni : Uniform F k) :
    F.card ≤ (Fintype.card V).choose (intersectionSpectrum F).card := by
  classical
  apply rayChaudhuriWilson F (intersectionSpectrum F) k huni
  · intro l hl
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hA, hB, hne⟩ := Finset.mem_offDiag.mp hAB
    exact intersection_lt_of_uniform F k huni A B hA hB hne
  · intro A hA B hB hne
    exact Finset.mem_image.mpr ⟨(A, B), Finset.mem_offDiag.mpr ⟨hA, hB, hne⟩, rfl⟩

open Classical in
/-- The one-intersection case is the uniform Fisher bound. -/
theorem uniform_fisher (F : Finset (Finset V)) (k l : ℕ)
    (huni : Uniform F k) (hl : l < k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card = l) :
    F.card ≤ Fintype.card V := by
  have h := rayChaudhuriWilson F {l} k huni (by simpa)
    (by intro A hA B hB hne; simpa using hinter A hA B hB hne)
  simpa using h

open Classical in
/-- Every s-subset is an equality example, with intersection sizes in {0,...,s-1}. -/
theorem sharp_example (s : ℕ) :
    let F := (univ : Finset V).powersetCard s
    Uniform F s ∧ IntersectionsIn F (range s) ∧ F.card = (Fintype.card V).choose s := by
  classical
  dsimp
  have huni : Uniform ((univ : Finset V).powersetCard s) s := by
    intro A hA
    exact (Finset.mem_powersetCard.mp hA).2
  refine ⟨huni, ?_, by simp⟩
  intro A hA B hB hne
  exact Finset.mem_range.mpr (intersection_lt_of_uniform _ s huni A B hA hB hne)

end IntersectionBounds
