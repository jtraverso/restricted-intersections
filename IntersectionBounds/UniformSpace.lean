/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import IntersectionBounds.EvaluationSpace
public import IntersectionBounds.Definitions

@[expose] public section

namespace IntersectionBounds

open Finset Submodule

universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))

open Classical in
theorem extension_identity (k : ℕ) (huni : Uniform F k) (T : Finset V) :
    ((k : K) - T.card) • (indicator F T : F → K) =
      ∑ a ∈ (univ \ T), indicator F (insert a T) := by
  classical
  funext B
  by_cases hT : T ⊆ B.val
  · simp only [Pi.smul_apply, indicator, ite_eq_left hT, smul_eq_mul, mul_one, Finset.sum_apply]
    have hsets : (univ \ T).filter (fun a => insert a T ⊆ B.val) = B.val \ T := by
      ext a
      simp [Finset.insert_subset_iff, hT, and_comm]
    rw [Finset.sum_boole, hsets, Finset.card_sdiff_of_subset hT,
      Nat.cast_sub (Finset.card_le_card hT), huni B.val B.property]
  · have hall (a : V) : ¬ insert a T ⊆ B.val :=
      fun h => hT ((Finset.subset_insert a T).trans h)
    simp [indicator, hT, hall]

theorem indicator_mem_exact_of_uniform [CharZero K] (k s : ℕ)
    (huni : Uniform F k) (hs : s ≤ k) (T : Finset V) (hT : T.card ≤ s) :
    (indicator F T : F → K) ∈ exactSpace F s := by
  classical
  have aux : ∀ d : ℕ, ∀ T : Finset V, T.card ≤ s → s - T.card = d →
      (indicator F T : F → K) ∈ exactSpace F s := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro T hT hd
      by_cases heq : T.card = s
      · exact indicator_mem_exact F T s heq
      have hlt : T.card < s := by omega
      have hcoef : (k : K) - T.card ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show k ≠ T.card by omega)
      have hsum : (∑ a ∈ (univ \ T), indicator F (insert a T) : F → K) ∈
          exactSpace F s := by
        apply Submodule.sum_mem
        intro a ha
        have hnot := (Finset.mem_sdiff.mp ha).2
        have hcard := Finset.card_insert_of_notMem hnot
        apply ih (s - (insert a T).card) (by omega) (insert a T) (by omega) rfl
      rw [← extension_identity F k huni T] at hsum
      have h := (exactSpace F s).smul_mem ((k : K) - T.card)⁻¹ hsum
      simpa [smul_smul, hcoef] using h
  exact aux _ T hT rfl

theorem degreeSpace_le_exact_of_uniform [CharZero K] (k s : ℕ)
    (huni : Uniform F k) (hs : s ≤ k) :
    degreeSpace F s ≤ (exactSpace F s : Submodule K (F → K)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T, hT, rfl⟩
  exact indicator_mem_exact_of_uniform F k s huni hs T hT

theorem finrank_exactSpace_le (s : ℕ) :
    Module.finrank K (exactSpace F s : Submodule K (F → K)) ≤ (Fintype.card V).choose s := by
  classical
  let I := {T : Finset V // T.card = s}
  let gen : I → (F → K) := fun T => indicator F T.val
  have heq : exactSpace F s = span K (Set.range gen) := by
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
    _ = (Fintype.card V).choose s := by
      rw [Fintype.card_subtype]
      have hsets : univ.filter (fun T : Finset V => T.card = s) =
          (univ : Finset V).powersetCard s := by
        ext T
        simp
      rw [hsets, Finset.card_powersetCard, Finset.card_univ]

end IntersectionBounds
