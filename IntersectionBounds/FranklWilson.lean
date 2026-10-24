/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import IntersectionBounds.RayChaudhuriWilson
public import IntersectionBounds.DegreeDimension
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace IntersectionBounds

open Finset Submodule

universe u
variable {V : Type u}

open Classical in
/-- Lift the residue representatives to rational separating polynomials. -/
noncomputable def liftedSeparator (p : ℕ) (F : Finset (Finset V))
    (L : Finset (ZMod p)) (A : Finset V) : F → ℚ :=
  ∏ l ∈ L, (fun B => ((A ∩ B.val).card : ℚ) - l.val)

theorem liftedSeparator_mem_degree (p : ℕ) (F : Finset (Finset V))
    (L : Finset (ZMod p)) (A : Finset V) :
    liftedSeparator p F L A ∈ degreeSpace F L.card := by
  classical
  induction L using Finset.induction with
  | empty => simpa [liftedSeparator] using (one_mem_degree (K := ℚ) F)
  | @insert l L hl ih =>
    have h := degreeSpace_mul F (factor_mem_degree F A (l.val : ℚ)) ih
    simpa [liftedSeparator, Finset.prod_insert hl, Finset.card_insert_of_notMem hl,
      Nat.add_comm] using h

open Classical in
/-- Modular diagonal separation implies independence of the rational lifts.
The determinant is first reduced modulo p, and then lifted to characteristic zero. -/
theorem liftedSeparator_linearIndependent (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (L : Finset (ZMod p))
    (hself : ∀ A ∈ F, (A.card : ZMod p) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L) :
    LinearIndependent ℚ (fun A : F => liftedSeparator p F L A.val) := by
  classical
  let M : Matrix F F ℤ := fun A B => ∏ l ∈ L, ((A.val ∩ B.val).card - (l.val : ℤ))
  have hmod : M.map (Int.castRingHom (ZMod p)) =
      Matrix.diagonal (fun A : F => ∏ l ∈ L, ((A.val.card : ZMod p) - l)) := by
    ext A B
    by_cases h : A = B
    · subst B
      change ((∏ l ∈ L, ((A.val ∩ A.val).card - (l.val : ℤ)) : ℤ) : ZMod p) = _
      simp
    · have hx := hinter A.val A.property B.val B.property (fun heq => h (Subtype.ext heq))
      have hz : (∏ l ∈ L, (((A.val ∩ B.val).card : ZMod p) - l)) = 0 :=
        Finset.prod_eq_zero hx (by simp)
      change ((∏ l ∈ L, ((A.val ∩ B.val).card - (l.val : ℤ)) : ℤ) : ZMod p) = _
      simpa [Matrix.diagonal_apply, h] using hz
  have hdetmod : (M.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    rw [hmod, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro A _
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    exact sub_ne_zero.mpr (fun heq => hself A.val A.property (heq ▸ hl))
  have hdet : M.det ≠ 0 := by
    intro hz
    apply hdetmod
    change (M.map (fun z : ℤ => (z : ZMod p))).det = 0
    rw [← Int.cast_det, hz, Int.cast_zero]
  have hdetQ : (M.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change (M.map (fun z : ℤ => (z : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hdet
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdetQ
  have heq : (fun A : F => (M.map (Int.castRingHom ℚ)) A) =
      (fun A : F => liftedSeparator p F L A.val) := by
    funext A B
    change ((∏ l ∈ L, ((A.val ∩ B.val).card - (l.val : ℤ)) : ℤ) : ℚ) = _
    simp [liftedSeparator, Finset.prod_apply]
  rw [heq] at hli
  exact hli

variable [Fintype V]

open Classical in
/-- Frankl–Wilson (1981): the sharp modular intersection bound for uniform families. -/
theorem franklWilson (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (L : Finset (ZMod p)) (k : ℕ)
    (huni : Uniform F k) (hs : L.card ≤ k) (hk : (k : ZMod p) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L) :
    F.card ≤ (Fintype.card V).choose L.card := by
  classical
  let f : F → (F → ℚ) := fun A => liftedSeparator p F L A.val
  have hli : LinearIndependent ℚ f := liftedSeparator_linearIndependent p F L
    (by intro A hA; simpa only [huni A hA] using hk) hinter
  have hspan : span ℚ (Set.range f) ≤ degreeSpace F L.card := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, rfl⟩
    exact liftedSeparator_mem_degree p F L A.val
  calc
    F.card = Module.finrank ℚ (span ℚ (Set.range f)) := by
      rw [finrank_span_eq_card hli, Fintype.card_coe]
    _ ≤ Module.finrank ℚ (degreeSpace (K := ℚ) F L.card) := Submodule.finrank_mono hspan
    _ ≤ Module.finrank ℚ (exactSpace (K := ℚ) F L.card) :=
      Submodule.finrank_mono (degreeSpace_le_exact_of_uniform F k L.card huni hs)
    _ ≤ _ := finrank_exactSpace_le F L.card

open Classical in
/-- The modular nonuniform polynomial-method bound. -/
theorem franklWilson_nonuniform (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (L : Finset (ZMod p))
    (hself : ∀ A ∈ F, (A.card : ZMod p) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L) :
    F.card ≤ ∑ i ∈ range (L.card + 1), (Fintype.card V).choose i := by
  exact (card_le_finrank_degree F L hself hinter).trans
    (finrank_degreeSpace_le (K := ZMod p) F L.card)

open Classical in
/-- In particular, excluding the block-size residue gives the p−1 bound. -/
theorem franklWilson_forbidden_residue (p : ℕ) [Fact p.Prime]
    (F : Finset (Finset V)) (k : ℕ) (huni : Uniform F k) (hpk : p - 1 ≤ k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B →
      ((A ∩ B).card : ZMod p) ≠ (k : ZMod p)) :
    F.card ≤ (Fintype.card V).choose (p - 1) := by
  classical
  have hcard : (univ.erase (k : ZMod p)).card = p - 1 := by simp
  have h := franklWilson p F (univ.erase (k : ZMod p)) k huni
    (by simpa only [hcard] using hpk) (by simp)
    (by intro A hA B hB hne; simpa using hinter A hA B hB hne)
  simpa only [hcard] using h

open Classical in
/-- A finite coloring consequence: each color class excludes the block-size residue.
Applied to the modular intersection graph, this gives its chromatic lower bound. -/
theorem franklWilson_coloring_bound (p : ℕ) [Fact p.Prime] (k r : ℕ)
    (hpk : p - 1 ≤ k) (c : Finset V → Fin r)
    (hcolor : ∀ A B : Finset V, A.card = k → B.card = k → A ≠ B → c A = c B →
      ((A ∩ B).card : ZMod p) ≠ (k : ZMod p)) :
    (Fintype.card V).choose k ≤ r * (Fintype.card V).choose (p - 1) := by
  classical
  let F := (univ : Finset V).powersetCard k
  have hbound (i : Fin r) : (F.filter (fun A => c A = i)).card ≤
      (Fintype.card V).choose (p - 1) := by
    apply franklWilson_forbidden_residue p _ k
    · intro A hA
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
    · exact hpk
    · intro A hA B hB hne
      obtain ⟨hAF, hcA⟩ := Finset.mem_filter.mp hA
      obtain ⟨hBF, hcB⟩ := Finset.mem_filter.mp hB
      exact hcolor A B (Finset.mem_powersetCard.mp hAF).2
        (Finset.mem_powersetCard.mp hBF).2 hne (hcA.trans hcB.symm)
  calc
    _ = F.card := by simp [F]
    _ = ∑ i : Fin r, (F.filter (fun A => c A = i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : Fin r, (Fintype.card V).choose (p - 1) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by simp

end IntersectionBounds
