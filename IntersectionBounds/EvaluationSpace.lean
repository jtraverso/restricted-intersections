/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace IntersectionBounds

open Finset Submodule

universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V))

open Classical in
/-- A squarefree monomial evaluated at the characteristic vectors of the family. -/
noncomputable def indicator (T : Finset V) : F → K := fun B => if T ⊆ B.val then 1 else 0

/-- Evaluations of multilinear polynomials of total degree at most d. -/
noncomputable def degreeSpace (d : ℕ) : Submodule K (F → K) :=
  span K ((indicator F) '' {T : Finset V | T.card ≤ d})

/-- Evaluations of homogeneous squarefree polynomials of degree exactly d. -/
noncomputable def exactSpace (d : ℕ) : Submodule K (F → K) :=
  span K ((indicator F) '' {T : Finset V | T.card = d})

theorem indicator_mem_degree (T : Finset V) (d : ℕ) (h : T.card ≤ d) :
    (indicator F T : F → K) ∈ degreeSpace F d := subset_span ⟨T, h, rfl⟩

theorem indicator_mem_exact (T : Finset V) (d : ℕ) (h : T.card = d) :
    (indicator F T : F → K) ∈ exactSpace F d := subset_span ⟨T, h, rfl⟩

open Classical in
theorem indicator_mul (S T : Finset V) :
    indicator F S * indicator F T = (indicator F (S ∪ T) : F → K) := by
  classical
  funext B
  by_cases hs : S ⊆ B.val <;> by_cases ht : T ⊆ B.val <;> simp [indicator, Finset.union_subset_iff, hs, ht]

theorem degreeSpace_mul {a b : ℕ} {f g : F → K}
    (hf : f ∈ degreeSpace F a) (hg : g ∈ degreeSpace F b) :
    f * g ∈ degreeSpace F (a + b) := by
  classical
  change f ∈ span K _ at hf
  change g ∈ span K _ at hg
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
    obtain ⟨S, hS, rfl⟩ := hf
    obtain ⟨T, hT, rfl⟩ := hg
    rw [indicator_mul]
    exact indicator_mem_degree F _ _ ((Finset.card_union_le _ _).trans (add_le_add hS hT))
  | zero_left g _ => simp
  | zero_right f _ => simp
  | add_left f₁ f₂ g _ _ _ h₁ h₂ =>
    simpa [add_mul] using (degreeSpace F (a + b)).add_mem h₁ h₂
  | add_right f g₁ g₂ _ _ _ h₁ h₂ =>
    simpa [mul_add] using (degreeSpace F (a + b)).add_mem h₁ h₂
  | smul_left c f g _ _ h =>
    simpa [smul_mul_assoc] using (degreeSpace F (a + b)).smul_mem c h
  | smul_right c f g _ _ h =>
    simpa [mul_smul_comm] using (degreeSpace F (a + b)).smul_mem c h

@[simp] theorem indicator_empty : (indicator F ∅ : F → K) = 1 := by
  classical
  funext B
  simp [indicator]

theorem one_mem_degree : (1 : F → K) ∈ degreeSpace F 0 := by
  have h := indicator_mem_degree (K := K) F ∅ 0 (by simp)
  simpa only [indicator_empty] using h

open Classical in
theorem intersection_as_sum (A : Finset V) :
    (fun B : F => ((A ∩ B.val).card : K)) = ∑ a ∈ A, indicator F {a} := by
  classical
  funext B
  simp [indicator, Finset.sum_apply]

open Classical in
theorem factor_mem_degree (A : Finset V) (l : K) :
    (fun B : F => ((A ∩ B.val).card : K) - l) ∈ degreeSpace F 1 := by
  classical
  have hi : (fun B : F => ((A ∩ B.val).card : K)) ∈ degreeSpace F 1 := by
    rw [intersection_as_sum]
    apply Submodule.sum_mem
    intro a _
    exact indicator_mem_degree F {a} 1 (by simp)
  have hl : (fun _ : F => l) ∈ degreeSpace F 1 := by
    have h := (degreeSpace F 1).smul_mem l (indicator_mem_degree F ∅ 1 (by simp))
    simpa only [indicator_empty, Pi.smul_def, Pi.one_apply, smul_eq_mul, mul_one] using h
  exact (degreeSpace (K := K) F 1).sub_mem hi hl

open Classical in
/-- The separating polynomial, evaluated at every member of the family. -/
noncomputable def separator (L : Finset K) (A : Finset V) : F → K :=
  ∏ l ∈ L, (fun B => ((A ∩ B.val).card : K) - l)

theorem separator_mem_degree (L : Finset K) (A : Finset V) :
    separator F L A ∈ degreeSpace F L.card := by
  classical
  induction L using Finset.induction with
  | empty => simpa [separator] using (one_mem_degree (K := K) F)
  | @insert l L hl ih =>
    have h := degreeSpace_mul F (factor_mem_degree F A l) ih
    simpa [separator, Finset.prod_insert hl, Finset.card_insert_of_notMem hl, Nat.add_comm] using h

end IntersectionBounds
