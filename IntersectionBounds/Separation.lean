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
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V)) (L : Finset K)

theorem separator_self (A : F) :
    separator F L A.val A = ∏ l ∈ L, ((A.val.card : K) - l) := by
  classical
  simp [separator]

open Classical in
theorem separator_off_diagonal (A B : F) (h : ((A.val ∩ B.val).card : K) ∈ L) :
    separator F L A.val B = 0 := by
  classical
  simp only [separator, Finset.prod_apply]
  apply Finset.prod_eq_zero h
  simp

open Classical in
theorem separator_linearIndependent
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    LinearIndependent K (fun A : F => separator F L A.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc A
  have h := congrFun hc A
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have hz (B : F) (hBA : B ≠ A) : separator F L B.val A = 0 :=
    separator_off_diagonal F L B A
      (hinter B.val B.property A.val A.property (fun heq => hBA (Subtype.ext heq)))
  rw [Finset.sum_eq_single A (fun B _ hBA => by rw [hz B hBA, mul_zero]) (by simp)] at h
  have hdiag : separator F L A.val A ≠ 0 := by
    rw [separator_self]
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    apply sub_ne_zero.mpr
    intro heq
    exact hself A.val A.property (heq ▸ hl)
  exact (mul_eq_zero.mp h).resolve_right hdiag

open Classical in
theorem card_le_finrank_degree
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ Module.finrank K (degreeSpace (K := K) F L.card) := by
  classical
  let f : F → (F → K) := fun A => separator F L A.val
  have hli : LinearIndependent K f := separator_linearIndependent F L hself hinter
  have hspan : span K (Set.range f) ≤ degreeSpace F L.card := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, rfl⟩
    exact separator_mem_degree F L A.val
  calc
    _ = Module.finrank K (span K (Set.range f)) := by
      rw [finrank_span_eq_card hli, Fintype.card_coe]
    _ ≤ _ := Submodule.finrank_mono hspan

end IntersectionBounds
