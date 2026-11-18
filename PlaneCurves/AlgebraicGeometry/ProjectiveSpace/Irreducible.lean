/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# Projective varieties and irreducible components

A set `V ⊆ ℙⁿ` is algebraic when it is the zero locus of its homogeneous ideal,
`zeroLocus (vanishingIdeal V) = V`; it is a projective variety when, moreover,
`(vanishingIdeal V).toIdeal` is prime (so `V ≠ ∅`). There is no Zariski
topology on `ℙⁿ` and no predicate for either notion: hypotheses are written out.

This file proves that a nonempty algebraic set is irreducible in Fulton's sense (it is not the
union of two algebraic sets other than itself) exactly when its ideal is prime, and that every
algebraic set is, uniquely, a finite irredundant union of projective varieties, its irreducible
components. The proofs are algebraic: Problem 4.4 (the prime test on forms) and the Noetherian
induction of Theorem 2 of §1.5, run on homogeneous ideals. Everything holds over any field.

## Main results

* `zeroLocus_vanishingIdeal_inter`, `zeroLocus_vanishingIdeal_union`: algebraic sets are closed
  under finite intersections and unions.
* `vanishingIdeal_le_vanishingIdeal_iff`, `vanishingIdeal_lt_vanishingIdeal_iff`: on algebraic
  sets, `I` reverses (strict) inclusions.
* `exists_subset_of_subset_sUnion`: a set with prime ideal that lies in a finite union of
  algebraic sets lies in one of them.
* `isPrime_vanishingIdeal_iff`: a nonempty algebraic set is irreducible iff its ideal is prime.
* `nonempty_of_isPrime_vanishingIdeal`, `isPrime_vanishingIdeal_univ`: a projective variety is
  nonempty, and `ℙⁿ` is one over an infinite field.
* `existsUnique_irreducibleDecomposition`: every algebraic set is, uniquely, a finite union of
  projective varieties none of which lies in another.
* `zeroLocus_vanishingIdeal_and_irreducibleDecomposition`: Fulton's description of projective
  algebraic sets, their ideals and affine cones, (a)–(d).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ} {V W W₁ W₂ : Set (ℙ k (Fin (n + 1) → k))}

/-! ### Algebraic sets -/

/-- A set is algebraic, `V(I(V)) = V`, exactly when it is the zero locus of a homogeneous
ideal. -/
theorem zeroLocus_vanishingIdeal_eq_iff :
    zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V ↔
      ∃ I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k),
        zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = V := by
  refine ⟨fun h ↦ ⟨_, h⟩, ?_⟩
  rintro ⟨I, rfl⟩
  exact zeroLocus_vanishingIdeal_zeroLocus I

/-- The zero locus of a set of forms is algebraic. -/
theorem zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous
    {S : Set (MvPolynomial (Fin (n + 1)) k)} (hS : ∀ f ∈ S, ∃ d, f.IsHomogeneous d) :
    zeroLocus (vanishingIdeal (zeroLocus S) : Set (MvPolynomial (Fin (n + 1)) k)) =
      zeroLocus S := by
  refine (zeroLocus_anti_mono fun f hf ↦ ?_).antisymm (subset_zeroLocus_vanishingIdeal _)
  obtain ⟨d, hd⟩ := hS f hf
  exact (mem_vanishingIdeal_iff_of_isHomogeneous hd).2 fun P hP ↦
    (mem_zeroLocus_iff_eval_rep hS).1 hP f hf

/-- Over an infinite field, every zero locus is algebraic. -/
theorem zeroLocus_vanishingIdeal_zeroLocus_set [Infinite k]
    (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (vanishingIdeal (zeroLocus S) : Set (MvPolynomial (Fin (n + 1)) k)) =
      zeroLocus S :=
  (zeroLocus_anti_mono (subset_zeroLocus_iff_subset_vanishingIdeal.1 subset_rfl)).antisymm
    (subset_zeroLocus_vanishingIdeal _)

@[simp]
theorem zeroLocus_vanishingIdeal_empty :
    zeroLocus (vanishingIdeal (∅ : Set (ℙ k (Fin (n + 1) → k))) :
      Set (MvPolynomial (Fin (n + 1)) k)) = ∅ := by
  rw [vanishingIdeal_empty]
  exact zeroLocus_eq_empty_of_one_mem (by simp)

@[simp]
theorem zeroLocus_vanishingIdeal_univ :
    zeroLocus (vanishingIdeal (Set.univ : Set (ℙ k (Fin (n + 1) → k))) :
      Set (MvPolynomial (Fin (n + 1)) k)) = Set.univ :=
  Set.eq_univ_of_univ_subset (subset_zeroLocus_vanishingIdeal _)

/-- The intersection of two algebraic sets is algebraic. -/
theorem zeroLocus_vanishingIdeal_inter
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V)
    (hW : zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W) :
    zeroLocus (vanishingIdeal (V ∩ W) : Set (MvPolynomial (Fin (n + 1)) k)) = V ∩ W := by
  refine (Set.subset_inter ?_ ?_).antisymm (subset_zeroLocus_vanishingIdeal _)
  · exact (zeroLocus_anti_mono fun _ hf ↦ vanishingIdeal_anti_mono Set.inter_subset_left hf).trans
      hV.subset
  · exact (zeroLocus_anti_mono fun _ hf ↦ vanishingIdeal_anti_mono Set.inter_subset_right hf).trans
      hW.subset

/-- The union of two algebraic sets is algebraic. -/
theorem zeroLocus_vanishingIdeal_union
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V)
    (hW : zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W) :
    zeroLocus (vanishingIdeal (V ∪ W) : Set (MvPolynomial (Fin (n + 1)) k)) = V ∪ W := by
  rw [vanishingIdeal_union]
  exact (zeroLocus_inf (vanishingIdeal V).isHomogeneous (vanishingIdeal W).isHomogeneous).trans
    (congrArg₂ (· ∪ ·) hV hW)

/-- For an algebraic set `W`, `I(W) ≤ I(V)` exactly when `V ⊆ W`. -/
theorem vanishingIdeal_le_vanishingIdeal_iff
    (hW : zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W) :
    vanishingIdeal W ≤ vanishingIdeal V ↔ V ⊆ W :=
  ⟨fun h ↦ (subset_zeroLocus_vanishingIdeal V).trans
    ((zeroLocus_anti_mono fun _ hf ↦ h hf).trans hW.subset), vanishingIdeal_anti_mono⟩

/-- For algebraic sets, `I(W) < I(V)` exactly when `V ⊂ W`. -/
theorem vanishingIdeal_lt_vanishingIdeal_iff
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V)
    (hW : zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W) :
    vanishingIdeal W < vanishingIdeal V ↔ V ⊂ W := by
  rw [lt_iff_le_not_ge, Set.ssubset_def, vanishingIdeal_le_vanishingIdeal_iff hW,
    vanishingIdeal_le_vanishingIdeal_iff hV]

/-- Algebraic sets with the same ideal are equal. -/
theorem eq_of_vanishingIdeal_eq
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V)
    (hW : zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W)
    (h : vanishingIdeal V = vanishingIdeal W) : V = W :=
  ((vanishingIdeal_le_vanishingIdeal_iff hW).1 h.ge).antisymm
    ((vanishingIdeal_le_vanishingIdeal_iff hV).1 h.le)

/-! ### Irreducibility -/

/-- The ideal of a nonempty set is proper. -/
theorem vanishingIdeal_ne_top (hV : V.Nonempty) : (vanishingIdeal V).toIdeal ≠ ⊤ := by
  intro h
  obtain ⟨P, hP⟩ := hV
  have h1 : (1 : MvPolynomial (Fin (n + 1)) k) ∈ vanishingIdeal V := by
    rw [← HomogeneousIdeal.mem_iff, h]
    exact Submodule.mem_top
  simpa using (mem_vanishingIdeal_iff_of_isHomogeneous (isHomogeneous_one _ _)).1 h1 P hP

/-- A set whose ideal is prime is nonempty. -/
theorem nonempty_of_isPrime_vanishingIdeal (hV : (vanishingIdeal V).toIdeal.IsPrime) :
    V.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦ hV.ne_top (by
    rw [h, vanishingIdeal_empty, HomogeneousIdeal.toIdeal_top])

/-- In `ℙ⁰`, a single point, every set with prime ideal is the whole space. -/
theorem eq_univ_of_isPrime_vanishingIdeal_of_eq_zero (hn : n = 0)
    (hV : (vanishingIdeal V).toIdeal.IsPrime) : V = Set.univ := by
  subst hn
  have : Subsingleton (ℙ k (Fin (0 + 1) → k)) :=
    Projectivization.subsingleton_of_rank_le_one (by simp)
  exact (nonempty_of_isPrime_vanishingIdeal hV).eq_univ

/-- Over an infinite field, `ℙⁿ` is a projective variety: its ideal is `0`, which is prime. -/
theorem isPrime_vanishingIdeal_univ [Infinite k] :
    (vanishingIdeal (Set.univ : Set (ℙ k (Fin (n + 1) → k)))).toIdeal.IsPrime := by
  rw [vanishingIdeal_univ, HomogeneousIdeal.toIdeal_bot]
  exact Ideal.isPrime_bot

/-- A set whose ideal is prime and which lies in a finite union of algebraic sets lies in one of
them. -/
theorem exists_subset_of_subset_sUnion (hV : (vanishingIdeal V).toIdeal.IsPrime)
    {C : Set (Set (ℙ k (Fin (n + 1) → k)))} (hC : C.Finite)
    (hW : ∀ W ∈ C, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W)
    (h : V ⊆ ⋃₀ C) : ∃ W ∈ C, V ⊆ W := by
  have hle : hC.toFinset.inf (fun W ↦ (vanishingIdeal W).toIdeal) ≤ (vanishingIdeal V).toIdeal :=
    fun f hf ↦ by
      rw [Submodule.mem_finsetInf] at hf
      refine mem_vanishingIdeal_iff.2 fun d P hP ↦ ?_
      obtain ⟨W, hWC, hPW⟩ := h hP
      exact mem_vanishingIdeal_iff.1 (hf W (hC.mem_toFinset.2 hWC)) d P hPW
  obtain ⟨W, hWC, hWV⟩ := hV.inf_le'.1 hle
  rw [Set.Finite.mem_toFinset] at hWC
  exact ⟨W, hWC, (vanishingIdeal_le_vanishingIdeal_iff (hW W hWC)).1 hWV⟩

/-- A set whose ideal is prime and which lies in the union of two algebraic sets lies in one of
them. -/
theorem subset_or_subset_of_subset_union (hV : (vanishingIdeal V).toIdeal.IsPrime)
    (hW₁ : zeroLocus (vanishingIdeal W₁ : Set (MvPolynomial (Fin (n + 1)) k)) = W₁)
    (hW₂ : zeroLocus (vanishingIdeal W₂ : Set (MvPolynomial (Fin (n + 1)) k)) = W₂)
    (h : V ⊆ W₁ ∪ W₂) : V ⊆ W₁ ∨ V ⊆ W₂ := by
  have hle : (vanishingIdeal W₁).toIdeal ⊓ (vanishingIdeal W₂).toIdeal ≤
      (vanishingIdeal V).toIdeal := by
    rw [← HomogeneousIdeal.toIdeal_inf, ← vanishingIdeal_union]
    exact vanishingIdeal_anti_mono h
  exact (hV.inf_le.1 hle).imp (vanishingIdeal_le_vanishingIdeal_iff hW₁).1
    (vanishingIdeal_le_vanishingIdeal_iff hW₂).1

/-- **Irreducible algebraic sets.** A nonempty algebraic set `V ⊆ ℙⁿ` is irreducible, that is,
not the union of two algebraic sets other than itself, exactly when `I(V)` is prime
(Fulton, §4.2, with Problem 4.4). -/
theorem isPrime_vanishingIdeal_iff
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V)
    (hne : V.Nonempty) :
    (vanishingIdeal V).toIdeal.IsPrime ↔
      ∀ W₁ W₂ : Set (ℙ k (Fin (n + 1) → k)),
        zeroLocus (vanishingIdeal W₁ : Set (MvPolynomial (Fin (n + 1)) k)) = W₁ →
        zeroLocus (vanishingIdeal W₂ : Set (MvPolynomial (Fin (n + 1)) k)) = W₂ →
        V = W₁ ∪ W₂ → V = W₁ ∨ V = W₂ := by
  refine ⟨fun hp W₁ W₂ hW₁ hW₂ hU ↦ ?_, fun h ↦ ?_⟩
  · refine (subset_or_subset_of_subset_union hp hW₁ hW₂ hU.subset).imp
      (fun h₁ ↦ h₁.antisymm ?_) fun h₂ ↦ h₂.antisymm ?_
    · exact hU ▸ Set.subset_union_left
    · exact hU ▸ Set.subset_union_right
  refine (vanishingIdeal V).isHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (vanishingIdeal_ne_top hne) fun {F G} hF hG hFG ↦ ?_
  obtain ⟨d, hF⟩ := hF
  obtain ⟨e, hG⟩ := hG
  rw [mem_homogeneousSubmodule] at hF hG
  have hS : ∀ {H : MvPolynomial (Fin (n + 1)) k} {m : ℕ}, H.IsHomogeneous m →
      ∀ f ∈ ({H} : Set (MvPolynomial (Fin (n + 1)) k)), ∃ d, f.IsHomogeneous d := by
    rintro H m hH f rfl
    exact ⟨m, hH⟩
  have hsub : V ⊆ zeroLocus {F} ∪ zeroLocus {G} := fun P hP ↦ by
    have := (mem_vanishingIdeal_iff_of_isHomogeneous (hF.mul hG)).1 hFG P hP
    rw [map_mul, mul_eq_zero] at this
    simpa [mem_zeroLocus_iff_eval_rep (hS hF), mem_zeroLocus_iff_eval_rep (hS hG)] using this
  have hU : V = V ∩ zeroLocus {F} ∪ V ∩ zeroLocus {G} := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hsub]
  have hmem : ∀ {H : MvPolynomial (Fin (n + 1)) k} {m : ℕ}, H.IsHomogeneous m →
      V = V ∩ zeroLocus {H} → H ∈ (vanishingIdeal V).toIdeal := fun hH hVH ↦
    (mem_vanishingIdeal_iff_of_isHomogeneous hH).2 fun P hP ↦
      (mem_zeroLocus_iff_eval_rep (hS hH)).1 (hVH ▸ hP).2 _ rfl
  exact (h _ _ (zeroLocus_vanishingIdeal_inter hV
      (zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous (hS hF)))
    (zeroLocus_vanishingIdeal_inter hV
      (zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous (hS hG))) hU).imp
    (hmem hF) (hmem hG)

/-! ### Irreducible components -/

/-- Every algebraic set is a finite union of projective varieties (Noetherian induction on its
ideal). -/
theorem exists_finite_sUnion_eq
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V) :
    ∃ C : Set (Set (ℙ k (Fin (n + 1) → k))), C.Finite ∧
      (∀ W ∈ C, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
        (vanishingIdeal W).toIdeal.IsPrime) ∧ ⋃₀ C = V := by
  generalize hJ : (vanishingIdeal V).toIdeal = J
  induction J using WellFoundedGT.induction generalizing V with
  | ind J ih =>
  by_cases hne : V.Nonempty
  swap
  · exact ⟨∅, Set.finite_empty, by simp,
      by rw [Set.sUnion_empty, Set.not_nonempty_iff_eq_empty.1 hne]⟩
  by_cases hp : (vanishingIdeal V).toIdeal.IsPrime
  · exact ⟨{V}, Set.finite_singleton V, by simpa using ⟨hV, hp⟩, by simp⟩
  obtain ⟨W₁, W₂, hW₁, hW₂, hU, h₁, h₂⟩ : ∃ W₁ W₂ : Set (ℙ k (Fin (n + 1) → k)),
      zeroLocus (vanishingIdeal W₁ : Set (MvPolynomial (Fin (n + 1)) k)) = W₁ ∧
      zeroLocus (vanishingIdeal W₂ : Set (MvPolynomial (Fin (n + 1)) k)) = W₂ ∧
      V = W₁ ∪ W₂ ∧ V ≠ W₁ ∧ V ≠ W₂ := by
    by_contra! hc
    exact hp ((isPrime_vanishingIdeal_iff hV hne).2 fun W₁ W₂ hW₁ hW₂ hU ↦
      or_iff_not_imp_left.2 (hc W₁ W₂ hW₁ hW₂ hU))
  have hlt : ∀ W, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W →
      W ⊆ V → V ≠ W → J < (vanishingIdeal W).toIdeal := fun W hW hWV hVW ↦ by
    subst hJ
    exact (vanishingIdeal_lt_vanishingIdeal_iff hW hV).2
      (Set.ssubset_iff_subset_ne.2 ⟨hWV, Ne.symm hVW⟩)
  obtain ⟨C₁, hC₁, hC₁W, hC₁U⟩ :=
    ih _ (hlt W₁ hW₁ (hU ▸ Set.subset_union_left) h₁) hW₁ rfl
  obtain ⟨C₂, hC₂, hC₂W, hC₂U⟩ :=
    ih _ (hlt W₂ hW₂ (hU ▸ Set.subset_union_right) h₂) hW₂ rfl
  refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun W hW ↦ hW.elim (hC₁W W) (hC₂W W), ?_⟩
  rw [Set.sUnion_union, hC₁U, hC₂U, hU]

/-- Two finite families of projective varieties, none of whose members lies in another member,
with the same union, are equal. -/
theorem eq_of_sUnion_eq {C D : Set (Set (ℙ k (Fin (n + 1) → k)))} (hC : C.Finite)
    (hD : D.Finite)
    (hCW : ∀ W ∈ C, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
      (vanishingIdeal W).toIdeal.IsPrime)
    (hDW : ∀ W ∈ D, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
      (vanishingIdeal W).toIdeal.IsPrime)
    (hCi : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' → W = W') (hDi : ∀ W ∈ D, ∀ W' ∈ D, W ⊆ W' → W = W')
    (h : ⋃₀ C = ⋃₀ D) : C = D := by
  have key : ∀ {C D : Set (Set (ℙ k (Fin (n + 1) → k)))}, C.Finite → D.Finite →
      (∀ W ∈ C, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
        (vanishingIdeal W).toIdeal.IsPrime) →
      (∀ W ∈ D, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
        (vanishingIdeal W).toIdeal.IsPrime) →
      (∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' → W = W') → ⋃₀ C = ⋃₀ D → C ⊆ D := by
    intro C D hC hD hCW hDW hCi h W hW
    obtain ⟨W', hW'D, hWW'⟩ := exists_subset_of_subset_sUnion (hCW W hW).2 hD
      (fun W' hW' ↦ (hDW W' hW').1) (h ▸ Set.subset_sUnion_of_mem hW)
    obtain ⟨W'', hW''C, hW'W''⟩ := exists_subset_of_subset_sUnion (hDW W' hW'D).2 hC
      (fun W'' hW'' ↦ (hCW W'' hW'').1) (h.symm ▸ Set.subset_sUnion_of_mem hW'D)
    obtain rfl := hCi W hW W'' hW''C (hWW'.trans hW'W'')
    exact (hWW'.antisymm hW'W'') ▸ hW'D
  exact (key hC hD hCW hDW hCi h).antisymm (key hD hC hDW hCW hDi h.symm)

/-- **Irreducible components.** Every algebraic set `V ⊆ ℙⁿ` is, uniquely, a finite union of
projective varieties none of which lies in another: its irreducible components. -/
theorem existsUnique_irreducibleDecomposition
    (hV : zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V) :
    ∃! C : Set (Set (ℙ k (Fin (n + 1) → k))), C.Finite ∧
      (∀ W ∈ C, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
        (vanishingIdeal W).toIdeal.IsPrime) ∧ ⋃₀ C = V ∧
      ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' → W = W' := by
  obtain ⟨C, hC, hCW, hCU⟩ := exists_finite_sUnion_eq hV
  let M := {W | Maximal (· ∈ C) W}
  have hMC : M ⊆ C := fun _ hW ↦ hW.prop
  have hMU : ⋃₀ M = V := by
    refine (Set.sUnion_mono hMC).trans hCU.subset |>.antisymm ?_
    rw [← hCU]
    rintro P ⟨W, hW, hPW⟩
    obtain ⟨W', hWW', hW'⟩ := hC.exists_le_maximal hW
    exact ⟨W', hW', hWW' hPW⟩
  have hMW : ∀ W ∈ M, _ := fun W hW ↦ hCW W (hMC hW)
  have hMi : ∀ W ∈ M, ∀ W' ∈ M, W ⊆ W' → W = W' := fun W hW W' hW' h ↦
    hW.eq_of_le hW'.prop h
  refine ⟨M, ⟨hC.subset hMC, hMW, hMU, hMi⟩, fun D ⟨hD, hDW, hDU, hDi⟩ ↦ ?_⟩
  exact eq_of_sUnion_eq hD (hC.subset hMC) hDW hMW hDi hMi (hDU.trans hMU.symm)

/-! ### Projective algebraic sets -/

/-- **Projective algebraic sets, their ideals and affine cones.** Let `k` be an infinite field
and `R = k[X₀, …, Xₙ]`. A point of `ℙⁿ` is a zero of `F ∈ R` when `F` vanishes at every set of
homogeneous coordinates of the point; `V(S)` is the set of common zeros of `S ⊆ R` and `I(X)`
the homogeneous ideal of `X ⊆ ℙⁿ`. A set `V ⊆ ℙⁿ` is algebraic when `V(I(V)) = V`, which by (b)
means that `V = V(S)` for some `S`.

* (a) `V(S)` is the zero locus of the homogeneous components of the elements of `S`, of the
  ideal spanned by `S`, and of finitely many forms.
* (b) `I(X)` is a homogeneous radical ideal; `V` and `I` reverse inclusions;
  `V(∑ Iᵢ) = ⋂ V(Iᵢ)`; `V(I) ∪ V(J) = V(IJ) = V(I ∩ J)` for homogeneous `I`, `J`;
  `V(0) = ℙⁿ`, `V(1) = ∅`, `I(∅) = R`, `I(ℙⁿ) = 0`; the point `[a]` is the zero locus of the
  linear forms `aᵢXⱼ - aⱼXᵢ`, which span its ideal; `V(I(X))` is the smallest zero locus
  containing `X`, and `V(I(V(S))) = V(S)`.
* (c) The affine ideal of the cone over a nonempty `X` is `I(X)`; for a homogeneous ideal `I`
  with `V(I) ≠ ∅`, the cone over `V(I)` is the affine zero locus of `I`.
* (d) A nonempty algebraic set is irreducible (not the union of two algebraic sets other than
  itself) if and only if its ideal is prime; every algebraic set is, uniquely, a finite union of
  projective varieties none of which lies in another.

Milestone: *Projective algebraic sets, their ideals and affine cones*. -/
theorem zeroLocus_vanishingIdeal_and_irreducibleDecomposition [Infinite k] :
    -- (a)
    (∀ S : Set (MvPolynomial (Fin (n + 1)) k),
      zeroLocus (⋃ d, homogeneousComponent d '' S) = zeroLocus S ∧
      zeroLocus (Ideal.span S : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus S ∧
      ∃ s : Finset (MvPolynomial (Fin (n + 1)) k), (∀ f ∈ s, ∃ d, f.IsHomogeneous d) ∧
        zeroLocus (s : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus S) ∧
    -- (b)
    (∀ X : Set (ℙ k (Fin (n + 1) → k)), (vanishingIdeal X).toIdeal.IsRadical) ∧
    (∀ S T : Set (MvPolynomial (Fin (n + 1)) k), S ⊆ T → zeroLocus T ⊆ zeroLocus S) ∧
    (∀ X Y : Set (ℙ k (Fin (n + 1) → k)), X ⊆ Y → vanishingIdeal Y ≤ vanishingIdeal X) ∧
    (∀ (ι : Type u) (I : ι → Ideal (MvPolynomial (Fin (n + 1)) k)),
      zeroLocus (↑(⨆ i, I i) : Set (MvPolynomial (Fin (n + 1)) k)) = ⋂ i, zeroLocus (I i)) ∧
    (∀ I J : Ideal (MvPolynomial (Fin (n + 1)) k),
      I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) →
      J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) →
      zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) ∪ zeroLocus J =
        zeroLocus (↑(I * J) : Set (MvPolynomial (Fin (n + 1)) k)) ∧
      zeroLocus (↑(I * J) : Set (MvPolynomial (Fin (n + 1)) k)) =
        zeroLocus (↑(I ⊓ J) : Set (MvPolynomial (Fin (n + 1)) k))) ∧
    zeroLocus ({0} : Set (MvPolynomial (Fin (n + 1)) k)) = Set.univ ∧
    zeroLocus ({1} : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ ∧
    vanishingIdeal (∅ : Set (ℙ k (Fin (n + 1) → k))) = ⊤ ∧
    vanishingIdeal (Set.univ : Set (ℙ k (Fin (n + 1) → k))) = ⊥ ∧
    (∀ (a : Fin (n + 1) → k) (ha : a ≠ 0),
      zeroLocus (Set.range fun ij : Fin (n + 1) × Fin (n + 1) ↦
        C (a ij.1) * X ij.2 - C (a ij.2) * X ij.1) = {Projectivization.mk k a ha} ∧
      (vanishingIdeal {Projectivization.mk k a ha}).toIdeal = Ideal.span (Set.range
        fun ij : Fin (n + 1) × Fin (n + 1) ↦ C (a ij.1) * X ij.2 - C (a ij.2) * X ij.1)) ∧
    (∀ (X : Set (ℙ k (Fin (n + 1) → k))) (S : Set (MvPolynomial (Fin (n + 1)) k)),
      X ⊆ zeroLocus (vanishingIdeal X : Set (MvPolynomial (Fin (n + 1)) k)) ∧
      (X ⊆ zeroLocus S →
        zeroLocus (vanishingIdeal X : Set (MvPolynomial (Fin (n + 1)) k)) ⊆ zeroLocus S)) ∧
    (∀ S : Set (MvPolynomial (Fin (n + 1)) k),
      zeroLocus (vanishingIdeal (zeroLocus S) : Set (MvPolynomial (Fin (n + 1)) k)) =
        zeroLocus S) ∧
    -- (c)
    (∀ X : Set (ℙ k (Fin (n + 1) → k)), X.Nonempty →
      MvPolynomial.vanishingIdeal k (cone X) = (vanishingIdeal X).toIdeal) ∧
    (∀ I : Ideal (MvPolynomial (Fin (n + 1)) k),
      I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) →
      (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
      cone (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) = MvPolynomial.zeroLocus k I) ∧
    -- (d)
    (∀ V : Set (ℙ k (Fin (n + 1) → k)),
      zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V → V.Nonempty →
      ((vanishingIdeal V).toIdeal.IsPrime ↔
        ∀ W₁ W₂ : Set (ℙ k (Fin (n + 1) → k)),
          zeroLocus (vanishingIdeal W₁ : Set (MvPolynomial (Fin (n + 1)) k)) = W₁ →
          zeroLocus (vanishingIdeal W₂ : Set (MvPolynomial (Fin (n + 1)) k)) = W₂ →
          V = W₁ ∪ W₂ → V = W₁ ∨ V = W₂)) ∧
    ∀ V : Set (ℙ k (Fin (n + 1) → k)),
      zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V →
      ∃! C : Set (Set (ℙ k (Fin (n + 1) → k))), C.Finite ∧
        (∀ W ∈ C, zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
          (vanishingIdeal W).toIdeal.IsPrime) ∧ ⋃₀ C = V ∧
        ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' → W = W' :=
  ⟨fun S ↦ ⟨zeroLocus_homogeneousComponent S, zeroLocus_span S, exists_finset_zeroLocus_eq S⟩,
    isRadical_vanishingIdeal, fun _ _ ↦ zeroLocus_anti_mono, fun _ _ ↦ vanishingIdeal_anti_mono,
    fun _ ↦ zeroLocus_iSup, fun _ _ hI hJ ↦ ⟨(zeroLocus_mul hI hJ).symm,
      (zeroLocus_mul hI hJ).trans (zeroLocus_inf hI hJ).symm⟩,
    zeroLocus_singleton_zero, zeroLocus_eq_empty_of_one_mem rfl, vanishingIdeal_empty,
    vanishingIdeal_univ, fun a ha ↦ ⟨zeroLocus_range_linearForms a ha,
      vanishingIdeal_singleton a ha⟩,
    fun X _ ↦ ⟨subset_zeroLocus_vanishingIdeal X, fun h ↦
      zeroLocus_anti_mono (subset_zeroLocus_iff_subset_vanishingIdeal.1 h)⟩,
    zeroLocus_vanishingIdeal_zeroLocus_set, fun _ ↦ vanishingIdeal_cone,
    fun _ hI h ↦ cone_zeroLocus hI h, fun _ hV hne ↦ isPrime_vanishingIdeal_iff hV hne,
    fun _ hV ↦ existsUnique_irreducibleDecomposition hV⟩

end PlaneCurves.ProjectiveSpace

end
