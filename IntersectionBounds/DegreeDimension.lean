/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import IntersectionBounds.EvaluationSpace

@[expose] public section

namespace IntersectionBounds

open Finset Submodule

universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]

open Classical in
theorem card_small_subsets (s : ℕ) :
    (univ.filter (fun T : Finset V => T.card ≤ s)).card =
      ∑ i ∈ range (s + 1), (Fintype.card V).choose i := by
  classical
  have hf := Finset.sum_card_fiberwise_eq_card_filter
    (univ : Finset (Finset V)) (range (s + 1)) Finset.card
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hf
  rw [← hf]
  apply Finset.sum_congr rfl
  intro i _
  have heq : univ.filter (fun T : Finset V => T.card = i) =
      (univ : Finset V).powersetCard i := by ext T; simp
  rw [heq, Finset.card_powersetCard, Finset.card_univ]

theorem finrank_degreeSpace_le (F : Finset (Finset V)) (s : ℕ) :
    Module.finrank K (degreeSpace (K := K) F s) ≤
      ∑ i ∈ range (s + 1), (Fintype.card V).choose i := by
  classical
  let I := {T : Finset V // T.card ≤ s}
  let gen : I → (F → K) := fun T => indicator F T.val
  have heq : degreeSpace F s = span K (Set.range gen) := by
    apply congrArg (span K)
    ext f
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨⟨T, hT⟩, rfl⟩
    · rintro ⟨T, rfl⟩
      exact ⟨T.val, T.property, rfl⟩
  rw [heq]
  calc
    _ ≤ Fintype.card I := finrank_range_le_card gen
    _ = _ := by rw [Fintype.card_subtype]; exact card_small_subsets s

end IntersectionBounds
