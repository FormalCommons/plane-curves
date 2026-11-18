/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import PlaneCurves.RingTheory.UniqueFactorizationDomain.Radical
public import TauCeti.RingTheory.MvPolynomial.ZariskiClosure
public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal

/-!
# Affine hypersurfaces: reduced equations and irreducible components

Let `k` be a field and `F ∈ k[X₁, …, Xₙ] = MvPolynomial σ k`. We describe the ideal
`I(V(F))` of the hypersurface `V(F)` and its irreducible components, as in §1.6 and §1.7 of
Fulton. Irreducibility of an algebraic set `V` is primality of its ideal `I(V)`; there is no
Zariski topology on `σ → k`.

Over an algebraically closed field, in finitely many variables, if `F ≠ 0` and `G` is
squarefree with the same irreducible factors as `F`, then `I(V(F)) = (G) = Rad(F)`; in Fulton's
form, if `F = μ ∏ Fᵢ^{eᵢ}` with pairwise non-associated irreducible `Fᵢ`, then
`I(V(F)) = (F₁ ⋯ F_r)`. The `V(Fᵢ)` are the irreducible components of `V(F)`. Two nonzero
polynomials have the same zero locus if and only if they have the same irreducible factors, and
irreducible polynomials up to associates correspond to irreducible hypersurfaces.

In the plane, over any field, an irreducible `F` with `V(F)` infinite has `I(V(F)) = (F)`; this
uses that relatively prime plane polynomials have finitely many common zeros. Over an infinite
field the irreducible algebraic subsets of `𝔸²` are `𝔸²`, the points, and these `V(F)`.

## Main results

* `MvPolynomial.vanishingIdeal_zeroLocus_span_singleton`: `I(V(F)) = (G)` for a squarefree `G`
  with the irreducible factors of `F`.
* `MvPolynomial.zeroLocus_span_singleton_eq_iff`: `V(F) = V(G)` if and only if `F` and `G`
  have the same irreducible factors.
* `MvPolynomial.vanishingIdeal_zeroLocus_span_singleton_of_irreducible`: `I(V(F)) = (F)` for
  irreducible `F`, over an algebraically closed field.
* `MvPolynomial.exists_irreducible_eq_zeroLocus_iff`: the irreducible hypersurfaces are the
  `V(F)` with `F` irreducible.
* `MvPolynomial.zeroLocus_span_singleton_eq_iff_associated`: irreducible `F` and `G` have the
  same zero locus if and only if they are associated.
* `PlaneCurves.vanishingIdeal_zeroLocus_eq_span_of_infinite`: in the plane, `I(V(F)) = (F)` for
  irreducible `F` with `V(F)` infinite, over any field.
* `PlaneCurves.isPrime_vanishingIdeal_plane_iff`, `PlaneCurves.isPrime_vanishingIdeal_line_iff`:
  the irreducible algebraic subsets of the plane and of the line over an infinite field.
* `MvPolynomial.finite_zeroLocus_span_singleton_of_unique`: in one variable, a nonzero polynomial
  has finitely many zeros.
* `PlaneCurves.vanishingIdeal_zeroLocus_and_components`: all of the above, in Fulton's form.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §1.6, Corollaries 1–3, and §1.7, Corollary 3.
-/

public section

open Ideal

namespace MvPolynomial

variable {k σ : Type*} [Field k]

/-- The zero locus of `μ ∏ fᵢ^{eᵢ}`, for `μ ≠ 0` and exponents `eᵢ ≠ 0`, is the union of the
zero loci of the `fᵢ`. -/
theorem zeroLocus_span_singleton_C_mul_prod_pow {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ k) {e : ι → ℕ} (he : ∀ i ∈ s, e i ≠ 0) {μ : k} (hμ : μ ≠ 0) :
    zeroLocus k (span {C μ * ∏ i ∈ s, f i ^ e i}) = ⋃ i ∈ s, zeroLocus k (span {f i}) := by
  ext x
  simp only [zeroLocus_span, Set.mem_singleton_iff, forall_eq, Set.mem_ofPred_eq,
    Set.mem_iUnion, map_mul, map_prod, map_pow, aeval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
    pow_eq_zero_iff', exists_prop]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, hμ, false_or]
  exact exists_congr fun i => and_congr_right fun hi => and_iff_left (he i hi)

/-- The irreducible components of `V(F)`: every subset of `V(F)` with prime ideal lies in
`V(p)` for an irreducible factor `p` of `F`. -/
theorem exists_irreducible_dvd_subset_zeroLocus {V : Set (σ → k)} {F : MvPolynomial σ k}
    (hV : (vanishingIdeal k V).IsPrime) (hF : F ≠ 0) (hVF : V ⊆ zeroLocus k (span {F})) :
    ∃ p, Irreducible p ∧ p ∣ F ∧ V ⊆ zeroLocus k (span {p}) := by
  have hFV : F ∈ vanishingIdeal k V :=
    vanishingIdeal_anti_mono hVF (le_vanishingIdeal_zeroLocus _ (mem_span_singleton_self F))
  obtain ⟨p, hp, hpF, hpV⟩ := hV.exists_irreducible_dvd_mem hF hFV
  refine ⟨p, hp, hpF, (zeroLocus_vanishingIdeal_le V).trans (zeroLocus_anti_mono ?_)⟩
  exact (span_singleton_le_iff_mem _).2 hpV

/-- In one variable, over any field, a nonzero polynomial has finitely many zeros. -/
theorem finite_zeroLocus_span_singleton_of_unique [Unique σ] {F : MvPolynomial σ k}
    (hF : F ≠ 0) : (zeroLocus k (span {F})).Finite := by
  have hF' : uniqueAlgEquiv k σ F ≠ 0 :=
    (map_ne_zero_iff _ (uniqueAlgEquiv k σ).injective).2 hF
  refine ((Polynomial.finite_setOfPred_isRoot hF').preimage
    (f := fun a : σ → k ↦ a default)
    (Function.Injective.injOn fun a b h ↦ funext fun i ↦ ?_)).subset fun a ha ↦ ?_
  · rwa [Unique.eq_default i]
  · rw [zeroLocus_span, Set.mem_ofPred_eq] at ha
    have := ha F rfl
    rw [aeval_def, Algebra.algebraMap_self, ← eval₂_uniqueAlgEquiv] at this
    exact this

section IsAlgClosed

variable [IsAlgClosed k] [Finite σ] {F G : MvPolynomial σ k}

/-- **Reduced equation of a hypersurface.** Over an algebraically closed field, if `F ≠ 0` and
`G` is squarefree with the same irreducible factors as `F`, then `I(V(F)) = (G)`. -/
theorem vanishingIdeal_zeroLocus_span_singleton (hF : F ≠ 0) (hG : Squarefree G)
    (h : ∀ p, Irreducible p → (p ∣ F ↔ p ∣ G)) :
    vanishingIdeal k (zeroLocus k (span {F})) = span {G} := by
  rw [vanishingIdeal_zeroLocus_eq_radical (K := k), radical_span_singleton_eq_span hF hG h]

/-- Over an algebraically closed field, `I(V(F)) = (F)` for irreducible `F`. -/
theorem vanishingIdeal_zeroLocus_span_singleton_of_irreducible (hF : Irreducible F) :
    vanishingIdeal k (zeroLocus k (span {F})) = span {F} :=
  vanishingIdeal_zeroLocus_span_singleton hF.ne_zero hF.squarefree fun _ _ => Iff.rfl

/-- Over an algebraically closed field, `V(F)` is irreducible for irreducible `F`: its ideal is
prime. -/
theorem isPrime_vanishingIdeal_zeroLocus_of_irreducible (hF : Irreducible F) :
    (vanishingIdeal k (zeroLocus k (span {F}))).IsPrime := by
  rw [vanishingIdeal_zeroLocus_span_singleton_of_irreducible hF,
    span_singleton_prime hF.ne_zero]
  exact hF.prime

/-- Over an algebraically closed field, for irreducible `F`, `V(F) ⊆ V(G)` if and only if
`F ∣ G`. -/
theorem zeroLocus_span_singleton_subset_iff (hF : Irreducible F) :
    zeroLocus k (span {F}) ⊆ zeroLocus k (span {G}) ↔ F ∣ G := by
  refine ⟨fun h => ?_, fun h => zeroLocus_anti_mono (span_singleton_le_span_singleton.2 h)⟩
  rw [← mem_span_singleton, ← vanishingIdeal_zeroLocus_span_singleton_of_irreducible hF (k := k)]
  exact vanishingIdeal_anti_mono h (le_vanishingIdeal_zeroLocus _ (mem_span_singleton_self G))

/-- Over an algebraically closed field, nonzero `F` and `G` have the same zero locus if and
only if they have the same irreducible factors. -/
theorem zeroLocus_span_singleton_eq_iff (hF : F ≠ 0) (hG : G ≠ 0) :
    zeroLocus k (span {F}) = zeroLocus k (span {G}) ↔
      ∀ p, Irreducible p → (p ∣ F ↔ p ∣ G) := by
  rw [← radical_span_singleton_eq_iff hF hG, ← vanishingIdeal_zeroLocus_eq_radical (K := k),
    ← vanishingIdeal_zeroLocus_eq_radical (K := k)]
  refine ⟨congrArg _, fun h => ?_⟩
  rw [← zariskiClosure_zeroLocus (k := k), zariskiClosure_apply, h, ← zariskiClosure_apply,
    zariskiClosure_zeroLocus]

/-- Over an algebraically closed field, irreducible `F` and `G` have the same zero locus if and
only if they are associated. -/
theorem zeroLocus_span_singleton_eq_iff_associated (hF : Irreducible F) (hG : Irreducible G) :
    zeroLocus k (span {F}) = zeroLocus k (span {G}) ↔ Associated F G := by
  refine ⟨fun h => ?_, fun h => by rw [span_singleton_eq_span_singleton.2 h]⟩
  exact hF.associated_of_dvd hG ((zeroLocus_span_singleton_subset_iff hF).1 h.subset)

/-- **Irreducible hypersurfaces.** Over an algebraically closed field, a set is an irreducible
hypersurface, `V(F)` for a nonconstant `F`, with prime ideal, if and only if it is `V(F)` for an
irreducible `F`. -/
theorem exists_irreducible_eq_zeroLocus_iff (V : Set (σ → k)) :
    ((∃ F : MvPolynomial σ k, 0 < F.totalDegree ∧ V = zeroLocus k (span {F})) ∧
      (vanishingIdeal k V).IsPrime) ↔
      ∃ F : MvPolynomial σ k, Irreducible F ∧ V = zeroLocus k (span {F}) := by
  refine ⟨fun ⟨⟨F, hdeg, hV⟩, hP⟩ => ?_, fun ⟨F, hF, hV⟩ => ⟨⟨F, ?_, hV⟩, ?_⟩⟩
  · have hF : F ≠ 0 := by rintro rfl; simp at hdeg
    obtain ⟨p, hp, hpF, hVp⟩ := exists_irreducible_dvd_subset_zeroLocus hP hF hV.subset
    refine ⟨p, hp, le_antisymm hVp (hV ▸ zeroLocus_anti_mono ?_)⟩
    exact span_singleton_le_span_singleton.2 hpF
  · rw [Nat.pos_iff_ne_zero, Ne, totalDegree_eq_zero_iff_eq_C]
    intro h
    exact hF.not_isUnit (h ▸ (Ne.isUnit fun h0 => hF.ne_zero (by rw [h, h0, C_0])).map C)
  · exact hV ▸ isPrime_vanishingIdeal_zeroLocus_of_irreducible hF

end IsAlgClosed

end MvPolynomial

namespace PlaneCurves

open MvPolynomial

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k}

/-- In the plane, over any field, a polynomial that vanishes on an infinite set of zeros of an
irreducible `F` is divisible by `F` (Fulton, §1.6, Corollary 1). -/
theorem dvd_of_mem_vanishingIdeal_of_infinite (hF : Irreducible F) {V : Set (Fin 2 → k)}
    (hV : V.Infinite) (hVF : V ⊆ zeroLocus k (span {F})) {G : MvPolynomial (Fin 2) k}
    (hG : G ∈ vanishingIdeal k V) : F ∣ G := by
  by_contra h
  refine hV ((finite_zeroLocus_span_pair_of_isRelPrime
    (hF.isRelPrime_iff_not_dvd.2 h) k).subset fun P hP => ?_)
  have hFP := hVF hP
  rw [zeroLocus_span] at hFP ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    Set.mem_ofPred_eq] at hFP ⊢
  exact ⟨hFP, (mem_vanishingIdeal_iff.1 hG) P hP⟩

/-- In the plane, over any field, if `F` is irreducible and `V(F)` is infinite, then
`I(V(F)) = (F)`. -/
theorem vanishingIdeal_zeroLocus_eq_span_of_infinite (hF : Irreducible F)
    (hinf : (zeroLocus k (span {F})).Infinite) :
    vanishingIdeal k (zeroLocus k (span {F})) = span {F} :=
  le_antisymm (fun _ hG => mem_span_singleton.2 (dvd_of_mem_vanishingIdeal_of_infinite hF hinf
    subset_rfl hG)) ((span_singleton_le_iff_mem _).2
      (le_vanishingIdeal_zeroLocus _ (mem_span_singleton_self F)))

/-- In the plane, over any field, if `F` is irreducible and `V(F)` is infinite, then `V(F)` is
irreducible: its ideal is prime. -/
theorem isPrime_vanishingIdeal_zeroLocus_of_infinite (hF : Irreducible F)
    (hinf : (zeroLocus k (span {F})).Infinite) :
    (vanishingIdeal k (zeroLocus k (span {F}))).IsPrime := by
  rw [vanishingIdeal_zeroLocus_eq_span_of_infinite hF hinf, span_singleton_prime hF.ne_zero]
  exact hF.prime

/-- **Irreducible algebraic subsets of the plane** (Fulton, §1.6, Corollary 2). Over an infinite
field, an algebraic subset of `𝔸²` is irreducible, that is, has a prime ideal, if and only if it
is `𝔸²`, a point, or `V(F)` for an irreducible `F` with `V(F)` infinite. -/
theorem isPrime_vanishingIdeal_plane_iff [Infinite k] {V : Set (Fin 2 → k)} :
    ((∃ I : Ideal (MvPolynomial (Fin 2) k), V = zeroLocus k I) ∧ (vanishingIdeal k V).IsPrime) ↔
      V = Set.univ ∨ (∃ x, V = {x}) ∨
        ∃ F : MvPolynomial (Fin 2) k, Irreducible F ∧ (zeroLocus k (span {F})).Infinite ∧
          V = zeroLocus k (span {F}) := by
  refine ⟨fun ⟨⟨I, hVI⟩, hP⟩ => ?_, fun h => ?_⟩
  · have hV : zeroLocus k (vanishingIdeal k V) = V := by
      rw [hVI, ← zariskiClosure_apply, zariskiClosure_zeroLocus]
    by_cases hbot : vanishingIdeal k V = ⊥
    · left
      rw [← hV, hbot, zeroLocus_bot, Set.top_eq_univ]
    by_cases hfin : V.Finite
    · obtain ⟨x, hx, -⟩ := exists_vanishingIdeal_eq_singleton_of_finite hfin hP
      exact Or.inr (Or.inl ⟨x, by rw [← hV, hx, zeroLocus_vanishingIdeal_singleton]⟩)
    obtain ⟨G, hG, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨p, hp, -, hpV⟩ := hP.exists_irreducible_dvd_mem hG0 hG
    have hVp : V ⊆ zeroLocus k (span {p}) :=
      hV ▸ zeroLocus_anti_mono ((span_singleton_le_iff_mem _).2 hpV)
    have hspan : vanishingIdeal k V = span {p} :=
      le_antisymm (fun _ hH => mem_span_singleton.2
        (dvd_of_mem_vanishingIdeal_of_infinite hp hfin hVp hH))
        ((span_singleton_le_iff_mem _).2 hpV)
    have hVeq : V = zeroLocus k (span {p}) := by rw [← hV, hspan]
    exact Or.inr (Or.inr ⟨p, hp, hVeq ▸ hfin, hVeq⟩)
  · rcases h with rfl | ⟨x, rfl⟩ | ⟨F, hF, hinf, rfl⟩
    · refine ⟨⟨⊥, by rw [zeroLocus_bot, Set.top_eq_univ]⟩, ?_⟩
      rw [← Set.pi_univ, vanishingIdeal_pi_eq_bot fun _ => Set.infinite_univ]
      exact Ideal.isPrime_bot
    · exact ⟨⟨_, (zeroLocus_vanishingIdeal_singleton x).symm⟩, inferInstance⟩
    · exact ⟨⟨_, rfl⟩, isPrime_vanishingIdeal_zeroLocus_of_infinite hF hinf⟩

/-- **Irreducible algebraic subsets of the line.** Over an infinite field, an algebraic subset
of `𝔸¹`, the functions on a one-point type `σ`, is irreducible, that is, has a prime ideal, if
and only if it is `𝔸¹` or a point. -/
theorem isPrime_vanishingIdeal_line_iff {σ : Type*} [Unique σ] [Infinite k] {V : Set (σ → k)} :
    ((∃ I : Ideal (MvPolynomial σ k), V = zeroLocus k I) ∧ (vanishingIdeal k V).IsPrime) ↔
      V = Set.univ ∨ ∃ x, V = {x} := by
  refine ⟨fun ⟨⟨I, hVI⟩, hP⟩ => ?_, fun h => ?_⟩
  · have hV : zeroLocus k (vanishingIdeal k V) = V := by
      rw [hVI, ← zariskiClosure_apply, zariskiClosure_zeroLocus]
    by_cases hbot : vanishingIdeal k V = ⊥
    · left
      rw [← hV, hbot, zeroLocus_bot, Set.top_eq_univ]
    obtain ⟨G, hG, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hfin : V.Finite := (finite_zeroLocus_span_singleton_of_unique hG0).subset
      (hV ▸ zeroLocus_anti_mono ((span_singleton_le_iff_mem _).2 hG))
    obtain ⟨x, hx, -⟩ := exists_vanishingIdeal_eq_singleton_of_finite hfin hP
    exact Or.inr ⟨x, by rw [← hV, hx, zeroLocus_vanishingIdeal_singleton]⟩
  · rcases h with rfl | ⟨x, rfl⟩
    · refine ⟨⟨⊥, by rw [zeroLocus_bot, Set.top_eq_univ]⟩, ?_⟩
      rw [← Set.pi_univ, vanishingIdeal_pi_eq_bot fun _ => Set.infinite_univ]
      exact Ideal.isPrime_bot
    · exact ⟨⟨_, (zeroLocus_vanishingIdeal_singleton x).symm⟩, inferInstance⟩

/-- **Reduced equations and irreducible components of affine hypersurfaces** (Fulton, §1.6,
Corollaries 1–3, and §1.7, Corollary 3).

1. Let `k` be algebraically closed, `σ` finite, and `F = μ ∏ᵢ Fᵢ^{eᵢ}` with `μ ≠ 0`, pairwise
   non-associated irreducible `Fᵢ` and `eᵢ ≠ 0`. Then `I(V(F)) = (F₁ ⋯ F_r) = Rad(F)`, and
   `V(F) = V(F₁) ∪ ⋯ ∪ V(F_r)` is the decomposition of `V(F)` into irreducible components: each
   `V(Fᵢ)` has a prime ideal, none contains another, and every subset of `V(F)` with prime ideal
   lies in one of them.
2. Over such `k`, nonzero `F` and `G` have `V(F) = V(G)` if and only if they have the same
   irreducible factors; irreducible `F` and `G` have `V(F) = V(G)` if and only if they are
   associated; and the irreducible hypersurfaces (`V(F)` with `F` nonconstant and a prime ideal)
   are the `V(F)` with `F` irreducible. So `F ↦ V(F)` is a bijection from irreducible polynomials
   up to `kˣ` to irreducible hypersurfaces.
3. In the plane over any field, if `F` is irreducible and `V(F)` is infinite, then
   `I(V(F)) = (F)`, which is prime. Over an infinite field the irreducible algebraic subsets of
   `𝔸²` are `𝔸²`, the points, and the `V(F)` with `F` irreducible and `V(F)` infinite.

Milestone: *Reduced equations and irreducible components of affine hypersurfaces*. -/
theorem vanishingIdeal_zeroLocus_and_components :
    (∀ {k σ ι : Type*} [Field k] [IsAlgClosed k] [Finite σ] (s : Finset ι)
      (f : ι → MvPolynomial σ k) (e : ι → ℕ) (μ : k), μ ≠ 0 → (∀ i ∈ s, Irreducible (f i)) →
      (s : Set ι).Pairwise (fun i j => ¬Associated (f i) (f j)) → (∀ i ∈ s, e i ≠ 0) →
      vanishingIdeal k (zeroLocus k (span {C μ * ∏ i ∈ s, f i ^ e i})) =
          span {∏ i ∈ s, f i} ∧
        vanishingIdeal k (zeroLocus k (span {C μ * ∏ i ∈ s, f i ^ e i})) =
          (span {C μ * ∏ i ∈ s, f i ^ e i}).radical ∧
        zeroLocus k (span {C μ * ∏ i ∈ s, f i ^ e i}) = ⋃ i ∈ s, zeroLocus k (span {f i}) ∧
        (∀ i ∈ s, (vanishingIdeal k (zeroLocus k (span {f i}))).IsPrime) ∧
        (∀ i ∈ s, ∀ j ∈ s, zeroLocus k (span {f i}) ⊆ zeroLocus k (span {f j}) → i = j) ∧
        ∀ V ⊆ zeroLocus k (span {C μ * ∏ i ∈ s, f i ^ e i}), (vanishingIdeal k V).IsPrime →
          ∃ i ∈ s, V ⊆ zeroLocus k (span {f i})) ∧
    (∀ {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ] (F G : MvPolynomial σ k),
      F ≠ 0 → G ≠ 0 →
      (zeroLocus k (span {F}) = zeroLocus k (span {G}) ↔ ∀ p, Irreducible p → (p ∣ F ↔ p ∣ G))) ∧
    (∀ {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ] (F G : MvPolynomial σ k),
      Irreducible F → Irreducible G →
      (zeroLocus k (span {F}) = zeroLocus k (span {G}) ↔ Associated F G)) ∧
    (∀ {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ] (V : Set (σ → k)),
      ((∃ F : MvPolynomial σ k, 0 < F.totalDegree ∧ V = zeroLocus k (span {F})) ∧
        (vanishingIdeal k V).IsPrime) ↔
        ∃ F : MvPolynomial σ k, Irreducible F ∧ V = zeroLocus k (span {F})) ∧
    (∀ {k : Type*} [Field k] (F : MvPolynomial (Fin 2) k), Irreducible F →
      (zeroLocus k (span {F})).Infinite →
      vanishingIdeal k (zeroLocus k (span {F})) = span {F} ∧
        (vanishingIdeal k (zeroLocus k (span {F}))).IsPrime) ∧
    (∀ {k : Type*} [Field k] [Infinite k] (V : Set (Fin 2 → k)),
      ((∃ I : Ideal (MvPolynomial (Fin 2) k), V = zeroLocus k I) ∧
        (vanishingIdeal k V).IsPrime) ↔
        V = Set.univ ∨ (∃ x, V = {x}) ∨
          ∃ F : MvPolynomial (Fin 2) k, Irreducible F ∧ (zeroLocus k (span {F})).Infinite ∧
            V = zeroLocus k (span {F})) := by
  refine ⟨?_, fun F G => zeroLocus_span_singleton_eq_iff,
    fun F G => zeroLocus_span_singleton_eq_iff_associated,
    exists_irreducible_eq_zeroLocus_iff, fun F hF hinf =>
      ⟨vanishingIdeal_zeroLocus_eq_span_of_infinite hF hinf,
        isPrime_vanishingIdeal_zeroLocus_of_infinite hF hinf⟩,
    fun V => isPrime_vanishingIdeal_plane_iff⟩
  intro k σ ι _ _ _ s f e μ hμ hf hs he
  have hu : IsUnit (C μ : MvPolynomial σ k) := (Ne.isUnit hμ).map C
  have hF0 : C μ * ∏ i ∈ s, f i ^ e i ≠ 0 :=
    mul_ne_zero hu.ne_zero (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (hf i hi).ne_zero)
  have hdvd := fun p (hp : Irreducible p) =>
    UniqueFactorizationMonoid.dvd_mul_prod_pow_iff (f := f) hu hp he
  refine ⟨vanishingIdeal_zeroLocus_span_singleton hF0
      (UniqueFactorizationMonoid.squarefree_prod_of_irreducible hf hs) hdvd,
    vanishingIdeal_zeroLocus_eq_radical _, zeroLocus_span_singleton_C_mul_prod_pow s f he hμ,
    fun i hi => isPrime_vanishingIdeal_zeroLocus_of_irreducible (hf i hi),
    fun i hi j hj h => ?_, fun V hVF hV => ?_⟩
  · by_contra hij
    exact hs hi hj hij ((hf i hi).associated_of_dvd (hf j hj)
      ((zeroLocus_span_singleton_subset_iff (hf i hi)).1 h))
  · obtain ⟨p, hp, hpF, hVp⟩ := exists_irreducible_dvd_subset_zeroLocus hV hF0 hVF
    obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff _).1 ((hdvd p hp).1 hpF)
    refine ⟨i, hi, hVp.trans_eq ?_⟩
    rw [span_singleton_eq_span_singleton.2 (hp.associated_of_dvd (hf i hi) hpi)]

end PlaneCurves

end
