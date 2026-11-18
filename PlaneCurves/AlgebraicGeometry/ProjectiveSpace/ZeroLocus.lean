/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Nullstellensatz
public import PlaneCurves.RingTheory.MvPolynomial.HomogeneousIdeal
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Zero loci, vanishing ideals and affine cones in projective space

For a field `k`, points of `ℙⁿ` are `ℙ k (Fin (n + 1) → k)` and polynomials are
`MvPolynomial (Fin (n + 1)) k`, graded by total degree. This file defines the projective zero
locus `V(S)` of a set of polynomials, the homogeneous ideal `I(X)` of a set of points, and the
affine cone `C(X) ⊆ 𝔸ⁿ⁺¹` over `X`, and proves Fulton's Problems 4.2 and 4.6 and the cone
correspondence of §4.2.

## Main definitions

* `PlaneCurves.ProjectiveSpace.zeroLocus S`: the points at whose every set of homogeneous
  coordinates every element of `S` vanishes.
* `PlaneCurves.ProjectiveSpace.vanishingIdeal X`: the homogeneous ideal spanned by the forms that
  vanish on `X`; over an infinite field, the polynomials that vanish on `X`.
* `PlaneCurves.ProjectiveSpace.cone X`: the union of the lines of the points of `X`, with the
  origin.

## Main results

* `mk_mem_zeroLocus_iff`: for forms, one set of homogeneous coordinates suffices.
* `zeroLocus_homogeneousComponent` (Problem 4.2): over an infinite field, `V(S)` is the zero locus
  of the homogeneous components of the elements of `S`; with `zeroLocus_span` and
  `exists_finset_zeroLocus_eq`, it is the zero locus of the ideal spanned by `S`, and of
  finitely many forms.
* `mk_mem_zeroLocus_iff_mem_zeroLocus`: for a homogeneous ideal `I` and `v ≠ 0`, `[v] ∈ V(I)`
  exactly when `v` lies in the affine zero locus of `I`.
* Problem 4.6: `isRadical_vanishingIdeal`, the Galois connections `gc_homogeneousIdeal` and
  `gc_set`, `zeroLocus_sup`, `zeroLocus_iSup`, `zeroLocus_radical`, `zeroLocus_mul`,
  `zeroLocus_inf`, `zeroLocus_empty`, `zeroLocus_univ`, `vanishingIdeal_empty`,
  `vanishingIdeal_univ`, `zeroLocus_range_linearForms` and `vanishingIdeal_singleton` (a point
  is cut out by the linear forms `aᵢXⱼ - aⱼXᵢ`, which span its ideal),
  `zeroLocus_vanishingIdeal_subset` and `zeroLocus_vanishingIdeal_zeroLocus`.
* `isPrime_vanishingIdeal_singleton`: the ideal of a point is prime.
* `cone_zeroLocus` and `vanishingIdeal_cone`: the cone over `V(I)` is the affine zero locus of
  `I`, and the affine ideal of the cone over a nonempty `X` is `I(X)`.
* `zeroLocus_linearSubst` and `mem_zeroLocus_iff_affineChart`: zero loci under a linear change
  of coordinates, and in the standard affine charts.

## Implementation notes

Fulton works over an algebraically closed field. Here `k` is any field, and the hypothesis
`[Infinite k]` appears exactly where Problem 4.2 is used. The zero locus follows Fulton's
convention, vanishing at every set of homogeneous coordinates, so that it makes sense for
polynomials that are not forms. Over a finite field the polynomials vanishing on a set of points
need not form a homogeneous ideal, so `vanishingIdeal X` is defined as the largest homogeneous
ideal of polynomials vanishing on `X`, which is spanned by the forms vanishing on `X`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/


public section

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [IsDomain R] [Infinite R]

/-- If a polynomial over an infinite domain vanishes at every nonzero multiple of `v`, then so
does each of its homogeneous components (Fulton, Problem 4.2). -/
theorem eval_homogeneousComponent_eq_zero_of_forall_smul {f : MvPolynomial σ R} {v : σ → R}
    (h : ∀ c : R, c ≠ 0 → eval (c • v) f = 0) (d : ℕ) :
    eval v (homogeneousComponent d f) = 0 := by
  classical
  let p : Polynomial R :=
    ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i (eval v (homogeneousComponent i f))
  have hp : ∀ c : R, p.eval c = eval (c • v) f := fun c ↦ by
    conv_rhs => rw [← sum_homogeneousComponent f]
    simp [p, Polynomial.eval_finsetSum, (homogeneousComponent_isHomogeneous _ f).eval_smul,
      mul_comm]
  have h0 : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p
      ((Set.finite_singleton 0).infinite_compl.mono ?_)
    intro c hc
    simp only [Polynomial.IsRoot, hp, Set.mem_ofPred_eq]
    exact h c hc
  by_cases hd : d < f.totalDegree + 1
  · have := congrArg (fun q : Polynomial R ↦ q.coeff d) h0
    simpa [p, Polynomial.finsetSum_coeff, Finsupp.single_apply, hd] using this
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

/-- A form vanishes at one set of homogeneous coordinates of a point exactly when it vanishes at
any other, such as the representative `(mk k v hv).rep`. -/
theorem IsHomogeneous.eval_rep_mk_eq_zero_iff {k : Type*} [Field k] {f : MvPolynomial σ k}
    {d : ℕ} (hf : f.IsHomogeneous d) {v : σ → k} (hv : v ≠ 0) :
    eval (Projectivization.mk k v hv).rep f = 0 ↔ eval v f = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [← hc, Units.smul_def, hf.eval_smul, mul_eq_zero, or_iff_right (pow_ne_zero _ c.ne_zero)]


end MvPolynomial

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ}

/-- The zero locus `V(S)` of a set `S` of polynomials in `n + 1` variables: the points of `ℙⁿ`
at whose every set of homogeneous coordinates every element of `S` vanishes. -/
def zeroLocus (S : Set (MvPolynomial (Fin (n + 1)) k)) : Set (ℙ k (Fin (n + 1) → k)) :=
  {P | ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk k v hv = P → ∀ f ∈ S, eval v f = 0}

theorem zeroLocus_def (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus S =
      {P | ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk k v hv = P → ∀ f ∈ S, eval v f = 0} :=
  (rfl)

variable {S T : Set (MvPolynomial (Fin (n + 1)) k)} {P : ℙ k (Fin (n + 1) → k)}

theorem mem_zeroLocus_iff :
    P ∈ zeroLocus S ↔ ∀ v : Fin (n + 1) → k, ∀ hv : v ≠ 0, mk k v hv = P → ∀ f ∈ S, eval v f = 0 :=
  by rw [zeroLocus_def]; rfl

/-- The class of `v` is a zero of `S` exactly when every element of `S` vanishes at every nonzero
multiple of `v`. -/
theorem mk_mem_zeroLocus_iff_forall_smul (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    mk k v hv ∈ zeroLocus S ↔ ∀ f ∈ S, ∀ c : k, c ≠ 0 → eval (c • v) f = 0 := by
  rw [mem_zeroLocus_iff]
  constructor
  · intro h f hf c hc
    exact h _ (smul_ne_zero hc hv) ((mk_eq_mk_iff' k _ _ _ _).2 ⟨c, rfl⟩) f hf
  · intro h w hw hwv f hf
    obtain ⟨c, rfl⟩ := (mk_eq_mk_iff' k _ _ _ _).1 hwv
    exact h f hf c (left_ne_zero_of_smul hw)

theorem mem_zeroLocus_iff_forall_smul_rep :
    P ∈ zeroLocus S ↔ ∀ f ∈ S, ∀ c : k, c ≠ 0 → eval (c • P.rep) f = 0 := by
  conv_lhs => rw [← P.mk_rep]
  exact mk_mem_zeroLocus_iff_forall_smul _ _

/-- For a set of forms, one set of homogeneous coordinates suffices to test membership in the
zero locus. -/
theorem mk_mem_zeroLocus_iff (hS : ∀ f ∈ S, ∃ d, f.IsHomogeneous d) (v : Fin (n + 1) → k)
    (hv : v ≠ 0) : mk k v hv ∈ zeroLocus S ↔ ∀ f ∈ S, eval v f = 0 := by
  rw [mk_mem_zeroLocus_iff_forall_smul]
  refine forall₂_congr fun f hf ↦ ⟨fun h ↦ by simpa using h 1 one_ne_zero, fun h c _ ↦ ?_⟩
  obtain ⟨d, hd⟩ := hS f hf
  rw [hd.eval_smul, h, mul_zero]

/-- For a set of forms, membership in the zero locus is tested at the representative `P.rep`. -/
theorem mem_zeroLocus_iff_eval_rep (hS : ∀ f ∈ S, ∃ d, f.IsHomogeneous d) :
    P ∈ zeroLocus S ↔ ∀ f ∈ S, eval P.rep f = 0 := by
  conv_lhs => rw [← P.mk_rep]
  exact mk_mem_zeroLocus_iff hS _ _

theorem zeroLocus_anti_mono (h : S ⊆ T) : zeroLocus T ⊆ zeroLocus S :=
  fun _ hP v hv hvP f hf ↦ (mem_zeroLocus_iff.1 hP) v hv hvP f (h hf)

theorem antitone_zeroLocus : Antitone (zeroLocus (k := k) (n := n)) :=
  fun _ _ ↦ zeroLocus_anti_mono

@[simp]
theorem zeroLocus_empty : zeroLocus (∅ : Set (MvPolynomial (Fin (n + 1)) k)) = Set.univ := by
  ext; simp [mem_zeroLocus_iff]

@[simp]
theorem zeroLocus_singleton_zero :
    zeroLocus ({0} : Set (MvPolynomial (Fin (n + 1)) k)) = Set.univ := by
  ext; simp [mem_zeroLocus_iff]

theorem zeroLocus_eq_empty_of_one_mem (h : 1 ∈ S) : zeroLocus S = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun P hP ↦ ?_
  simpa using (mem_zeroLocus_iff_forall_smul_rep.1 hP) 1 h 1 one_ne_zero

@[simp]
theorem zeroLocus_univ : zeroLocus (Set.univ : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ :=
  zeroLocus_eq_empty_of_one_mem (Set.mem_univ _)

theorem zeroLocus_union (S T : Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (S ∪ T) = zeroLocus S ∩ zeroLocus T := by
  ext P
  simp only [mem_zeroLocus_iff, Set.mem_union, Set.mem_inter_iff]
  grind

theorem zeroLocus_iUnion {ι : Sort*} (S : ι → Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (⋃ i, S i) = ⋂ i, zeroLocus (S i) := by
  ext P
  simp only [mem_zeroLocus_iff, Set.mem_iUnion, Set.mem_iInter]
  grind

/-- A set of polynomials and the ideal it spans have the same zero locus. -/
@[simp]
theorem zeroLocus_span (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (Ideal.span S : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus S := by
  refine (zeroLocus_anti_mono Ideal.subset_span).antisymm fun P hP v hv hvP ↦ ?_
  have : S ⊆ RingHom.ker (eval v) := fun f hf ↦ (mem_zeroLocus_iff.1 hP) v hv hvP f hf
  exact fun f hf ↦ Ideal.span_le.2 this hf

/-- The zero locus of a sum of ideals is the intersection of their zero loci. -/
theorem zeroLocus_sup (I J : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (↑(I ⊔ J) : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus I ∩ zeroLocus J := by
  rw [← zeroLocus_union, ← zeroLocus_span (_ ∪ _), Ideal.span_union, Ideal.span_eq, Ideal.span_eq]

/-- The zero locus of a sum of ideals is the intersection of their zero loci. -/
theorem zeroLocus_iSup {ι : Sort*} (I : ι → Ideal (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (↑(⨆ i, I i) : Set (MvPolynomial (Fin (n + 1)) k)) = ⋂ i, zeroLocus (I i) := by
  rw [← zeroLocus_iUnion, ← zeroLocus_span (⋃ _, _), Ideal.span_iUnion]
  simp only [Ideal.span_eq]

/-- An ideal and its radical have the same zero locus. -/
@[simp]
theorem zeroLocus_radical (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (I.radical : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus I := by
  refine (zeroLocus_anti_mono Ideal.le_radical).antisymm fun P hP v hv hvP f ⟨m, hm⟩ ↦ ?_
  have := (mem_zeroLocus_iff.1 hP) v hv hvP _ hm
  exact eq_zero_of_pow_eq_zero (by simpa using this)

/-- Over an infinite field, a point is a zero of `S` exactly when it is a zero of every
homogeneous component of every element of `S` (Fulton, Problem 4.2). -/
theorem zeroLocus_homogeneousComponent [Infinite k] (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (⋃ d, homogeneousComponent d '' S) = zeroLocus S := by
  refine Set.Subset.antisymm (fun P hP ↦ ?_) fun P hP ↦ ?_
  · rw [mem_zeroLocus_iff_forall_smul_rep] at hP ⊢
    intro f hf c hc
    conv_lhs => rw [← sum_homogeneousComponent f]
    simp only [map_sum]
    exact Finset.sum_eq_zero fun d _ ↦ hP _ (Set.mem_iUnion.2 ⟨d, f, hf, rfl⟩) c hc
  · rw [mem_zeroLocus_iff_eval_rep (by
      simp only [Set.mem_iUnion, Set.mem_image]
      rintro _ ⟨d, f, -, rfl⟩
      exact ⟨d, homogeneousComponent_isHomogeneous d f⟩)]
    simp only [Set.mem_iUnion, Set.mem_image, forall_exists_index, and_imp]
    rintro _ d f hf rfl
    exact eval_homogeneousComponent_eq_zero_of_forall_smul
      ((mem_zeroLocus_iff_forall_smul_rep.1 hP) f hf) d

/-- Over an infinite field, every zero locus is the zero locus of finitely many forms. -/
theorem exists_finset_zeroLocus_eq [Infinite k] (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    ∃ s : Finset (MvPolynomial (Fin (n + 1)) k), (∀ f ∈ s, ∃ d, f.IsHomogeneous d) ∧
      zeroLocus (s : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus S := by
  obtain ⟨s, hs, hspan⟩ := exists_finset_isHomogeneous_span_eq
    (Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) k)
      (⋃ d, homogeneousComponent d '' S) (by
        simp only [Set.mem_iUnion, Set.mem_image]
        rintro _ ⟨d, f, -, rfl⟩
        exact ⟨d, homogeneousComponent_mem d f⟩))
  refine ⟨s, hs, ?_⟩
  rw [← zeroLocus_span, hspan, zeroLocus_span, zeroLocus_homogeneousComponent]

section Homogeneous

variable {I J : Ideal (MvPolynomial (Fin (n + 1)) k)}

/-- For a homogeneous ideal `I`, a point is a zero of `I` exactly when every element of `I`
vanishes at its representative `P.rep`. -/
theorem mem_zeroLocus_iff_le_ker (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    P ∈ zeroLocus I ↔ I ≤ RingHom.ker (eval P.rep) := by
  conv_lhs => rw [← hI.span_setOf_isHomogeneous, zeroLocus_span]
  conv_rhs => rw [← hI.span_setOf_isHomogeneous, Ideal.span_le]
  rw [mem_zeroLocus_iff_eval_rep fun f (hf : f ∈ I ∧ _) ↦ hf.2]
  rfl

/-- **The affine cone.** For a homogeneous ideal `I` and `v ≠ 0`, the class of `v` is a zero of
`I` in `ℙⁿ` exactly when `v` is a zero of `I` in `𝔸ⁿ⁺¹`. -/
theorem mk_mem_zeroLocus_iff_mem_zeroLocus
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) (v : Fin (n + 1) → k)
    (hv : v ≠ 0) : mk k v hv ∈ zeroLocus I ↔ v ∈ MvPolynomial.zeroLocus k I := by
  conv_lhs => rw [← hI.span_setOf_isHomogeneous, zeroLocus_span]
  conv_rhs => rw [← hI.span_setOf_isHomogeneous, MvPolynomial.zeroLocus_span]
  rw [mk_mem_zeroLocus_iff fun f (hf : f ∈ I ∧ _) ↦ hf.2]
  simp

/-- For homogeneous ideals, the zero locus of a product is the union of the zero loci. -/
theorem zeroLocus_mul (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    zeroLocus (↑(I * J) : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus I ∪ zeroLocus J := by
  ext P
  rw [Set.mem_union, mem_zeroLocus_iff_le_ker (hI.mul hJ), mem_zeroLocus_iff_le_ker hI,
    mem_zeroLocus_iff_le_ker hJ, (RingHom.ker_isPrime _).mul_le]

/-- For homogeneous ideals, the zero locus of an intersection is the union of the zero loci. -/
theorem zeroLocus_inf (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    zeroLocus (↑(I ⊓ J) : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus I ∪ zeroLocus J := by
  ext P
  rw [Set.mem_union, mem_zeroLocus_iff_le_ker (hI.inf hJ), mem_zeroLocus_iff_le_ker hI,
    mem_zeroLocus_iff_le_ker hJ, (RingHom.ker_isPrime _).inf_le]

end Homogeneous

/-- **Change of coordinates.** Substituting an injective linear change of coordinates `M` into
the equations pulls the zero locus back along the induced map of `ℙⁿ`. -/
theorem zeroLocus_linearSubst (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (hM : Function.Injective M.mulVecLin) (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    zeroLocus (linearSubst M '' S) = Projectivization.map M.mulVecLin hM ⁻¹' zeroLocus S := by
  ext P
  induction P using Projectivization.ind with | h v hv =>
  rw [Set.mem_preimage, map_mk, mk_mem_zeroLocus_iff_forall_smul,
    mk_mem_zeroLocus_iff_forall_smul]
  simp [eval_linearSubst, Matrix.mulVec_smul]

/-- **Chart equations.** On the standard affine open where the coordinate `i` is nonzero, a point
is a zero of a set of forms exactly when its chart coordinates are a common zero of their
dehomogenizations at `i`. -/
theorem mem_zeroLocus_iff_affineChart (hS : ∀ f ∈ S, ∃ d, f.IsHomogeneous d) {i : Fin (n + 1)}
    (hP : P ∈ affineOpen i) :
    P ∈ zeroLocus S ↔ ∀ f ∈ S, eval (affineChart i P) (TauCeti.dehomogenize i f) = 0 := by
  induction P using Projectivization.ind with | h v hv =>
  have hi : v i ≠ 0 := (mk_mem_affineOpen_iff i v hv).1 hP
  rw [mk_mem_zeroLocus_iff hS, affineChart_mk]
  refine forall₂_congr fun f hf ↦ ?_
  obtain ⟨d, hd⟩ := hS f hf
  rw [TauCeti.eval_dehomogenize_div i hd v hi, mul_eq_zero,
    or_iff_right (pow_ne_zero _ (inv_ne_zero hi))]

section Cone

/-! ### The affine cone -/

variable {X Y : Set (ℙ k (Fin (n + 1) → k))}

/-- The affine cone `C(X) ⊆ 𝔸ⁿ⁺¹` over a set `X ⊆ ℙⁿ`: the union of the lines of the points of
`X`, together with the origin. -/
def cone (X : Set (ℙ k (Fin (n + 1) → k))) : Set (Fin (n + 1) → k) :=
  {v | ∀ hv : v ≠ 0, mk k v hv ∈ X}

theorem cone_def (X : Set (ℙ k (Fin (n + 1) → k))) :
    cone X = {v | ∀ hv : v ≠ 0, mk k v hv ∈ X} :=
  (rfl)

@[simp]
theorem zero_mem_cone : (0 : Fin (n + 1) → k) ∈ cone X := by
  simp [cone_def]

theorem mem_cone_iff_of_ne_zero {v : Fin (n + 1) → k} (hv : v ≠ 0) :
    v ∈ cone X ↔ mk k v hv ∈ X := by
  simp [cone_def, hv]

@[simp]
theorem rep_mem_cone_iff : P.rep ∈ cone X ↔ P ∈ X := by
  rw [mem_cone_iff_of_ne_zero P.rep_ne_zero, mk_rep]

theorem smul_mem_cone {v : Fin (n + 1) → k} (hv : v ∈ cone X) (c : k) : c • v ∈ cone X := by
  intro hcv
  rw [mk_eq_mk_iff' k _ v hcv (right_ne_zero_of_smul hcv) |>.2 ⟨c, rfl⟩]
  exact hv _

theorem cone_mono (h : X ⊆ Y) : cone X ⊆ cone Y :=
  fun _ hv hv' ↦ h (hv hv')

/-- **The cone of a zero locus.** For a homogeneous ideal `I` with a projective zero, the cone
over its projective zero locus is its affine zero locus. -/
theorem cone_zeroLocus {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    (h : (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty) :
    cone (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) = MvPolynomial.zeroLocus k I := by
  ext v
  by_cases hv : v = 0
  · subst hv
    obtain ⟨P, hP⟩ := h
    simp only [zero_mem_cone, MvPolynomial.mem_zeroLocus_iff, true_iff]
    intro f hf
    have h0 := (mem_zeroLocus_iff_le_ker hI).1 hP (homogeneousComponent_mem_of_mem hI hf 0)
    simpa [homogeneousComponent_zero, ← constantCoeff_eq] using h0
  · rw [mem_cone_iff_of_ne_zero hv, mk_mem_zeroLocus_iff_mem_zeroLocus hI]

/-! ### The vanishing ideal -/

/-- The homogeneous ideal `I(X)` of a set `X ⊆ ℙⁿ`: the ideal spanned by the forms that vanish
at every point of `X`. Over an infinite field it consists of the polynomials that vanish at
every set of homogeneous coordinates of every point of `X`
(`mem_vanishingIdeal_iff_subset_zeroLocus`). -/
noncomputable def vanishingIdeal (X : Set (ℙ k (Fin (n + 1) → k))) :
    HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) :=
  (MvPolynomial.vanishingIdeal k (cone X \ {0})).homogeneousCore _

theorem vanishingIdeal_def (X : Set (ℙ k (Fin (n + 1) → k))) :
    vanishingIdeal X = (MvPolynomial.vanishingIdeal k (cone X \ {0})).homogeneousCore _ :=
  (rfl)

variable {f : MvPolynomial (Fin (n + 1)) k}

/-- A form lies in `I(X)` exactly when it vanishes at the representative of every point of
`X`. -/
theorem mem_vanishingIdeal_iff_of_isHomogeneous {d : ℕ} (hf : f.IsHomogeneous d) :
    f ∈ vanishingIdeal X ↔ ∀ P ∈ X, eval P.rep f = 0 := by
  rw [← HomogeneousIdeal.mem_iff, vanishingIdeal_def]
  refine ⟨fun h P hP ↦ ?_, fun h ↦ Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨d, (mem_homogeneousSubmodule d f).2 hf⟩ ?_⟩
  · refine (mem_vanishingIdeal_iff.1 (Ideal.toIdeal_homogeneousCore_le _ _ h)) P.rep
      ⟨rep_mem_cone_iff.2 hP, P.rep_ne_zero⟩ |>.trans ?_
    simp
  · rintro v ⟨hv, hv0 : v ≠ 0⟩
    rw [aeval_eq_eval, ← hf.eval_rep_mk_eq_zero_iff hv0]
    exact h _ (hv hv0)

/-- A polynomial lies in `I(X)` exactly when each of its homogeneous components vanishes at the
representative of every point of `X`. -/
theorem mem_vanishingIdeal_iff :
    f ∈ vanishingIdeal X ↔ ∀ d, ∀ P ∈ X, eval P.rep (homogeneousComponent d f) = 0 := by
  rw [← HomogeneousIdeal.mem_iff, mem_iff_homogeneousComponent_mem (vanishingIdeal X).isHomogeneous]
  exact forall_congr' fun d ↦
    mem_vanishingIdeal_iff_of_isHomogeneous (homogeneousComponent_isHomogeneous d f)

/-- Over an infinite field, `I(X)` consists of the polynomials that vanish at every set of
homogeneous coordinates of every point of `X`. -/
theorem mem_vanishingIdeal_iff_subset_zeroLocus [Infinite k] :
    f ∈ vanishingIdeal X ↔ X ⊆ zeroLocus {f} := by
  simp only [mem_vanishingIdeal_iff, Set.subset_def, mem_zeroLocus_iff_forall_smul_rep,
    Set.mem_singleton_iff, forall_eq]
  refine ⟨fun h P hP c _ ↦ ?_, fun h d P hP ↦
    eval_homogeneousComponent_eq_zero_of_forall_smul (h P hP) d⟩
  conv_lhs => rw [← sum_homogeneousComponent f]
  simp [(homogeneousComponent_isHomogeneous _ f).eval_smul, h _ P hP]

theorem subset_zeroLocus_iff : X ⊆ zeroLocus S ↔ ∀ f ∈ S, X ⊆ zeroLocus {f} := by
  simp only [Set.subset_def, mem_zeroLocus_iff_forall_smul_rep, Set.mem_singleton_iff,
    forall_eq]
  grind

/-- `X` lies in the zero locus of a homogeneous ideal `I` exactly when `I ≤ I(X)`. -/
theorem subset_zeroLocus_iff_le_vanishingIdeal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) :
    X ⊆ zeroLocus I ↔ I ≤ vanishingIdeal X := by
  refine ⟨fun h f hf ↦ mem_vanishingIdeal_iff.2 fun d P hP ↦ ?_, fun h P hP ↦ ?_⟩
  · exact (mem_zeroLocus_iff_le_ker I.isHomogeneous).1 (h hP)
      (homogeneousComponent_mem_of_mem I.isHomogeneous hf d)
  · refine (mem_zeroLocus_iff_le_ker I.isHomogeneous).2 fun f hf ↦ ?_
    rw [RingHom.mem_ker, ← sum_homogeneousComponent f, map_sum]
    exact Finset.sum_eq_zero fun d _ ↦ mem_vanishingIdeal_iff.1 (h hf) d P hP

/-- Over an infinite field, `X ⊆ V(S)` exactly when `S ⊆ I(X)`. -/
theorem subset_zeroLocus_iff_subset_vanishingIdeal [Infinite k] :
    X ⊆ zeroLocus S ↔ S ⊆ vanishingIdeal X := by
  rw [subset_zeroLocus_iff]
  exact forall₂_congr fun _ _ ↦ mem_vanishingIdeal_iff_subset_zeroLocus.symm

/-- The zero locus and the vanishing ideal form a Galois connection between homogeneous ideals
and sets of points of `ℙⁿ`, ordered by reverse inclusion. -/
theorem gc_homogeneousIdeal :
    @GaloisConnection (HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k))
      (Set (ℙ k (Fin (n + 1) → k)))ᵒᵈ _ _ (fun I ↦ zeroLocus I) fun X ↦ vanishingIdeal X :=
  fun I X ↦ subset_zeroLocus_iff_le_vanishingIdeal (X := X) I

/-- Over an infinite field, the zero locus and the vanishing ideal form a Galois connection
between sets of polynomials and sets of points of `ℙⁿ`, ordered by reverse inclusion. -/
theorem gc_set [Infinite k] :
    @GaloisConnection (Set (MvPolynomial (Fin (n + 1)) k)) (Set (ℙ k (Fin (n + 1) → k)))ᵒᵈ _ _
      (fun S ↦ zeroLocus S) fun X ↦ vanishingIdeal X :=
  fun _ X ↦ subset_zeroLocus_iff_subset_vanishingIdeal (X := X)

theorem vanishingIdeal_anti_mono (h : X ⊆ Y) : vanishingIdeal Y ≤ vanishingIdeal X :=
  gc_homogeneousIdeal.monotone_u h

theorem subset_zeroLocus_vanishingIdeal (X : Set (ℙ k (Fin (n + 1) → k))) :
    X ⊆ zeroLocus (vanishingIdeal X) :=
  gc_homogeneousIdeal.l_u_le X

theorem le_vanishingIdeal_zeroLocus
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) :
    I ≤ vanishingIdeal (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) :=
  gc_homogeneousIdeal.le_u_l I

/-- `V(I(X))` is the smallest projective algebraic set containing `X`. -/
theorem zeroLocus_vanishingIdeal_subset
    {I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)}
    (h : X ⊆ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) :
    zeroLocus (vanishingIdeal X : Set (MvPolynomial (Fin (n + 1)) k)) ⊆ zeroLocus (I : Set _) :=
  zeroLocus_anti_mono ((subset_zeroLocus_iff_le_vanishingIdeal I).1 h)

/-- An algebraic set is the zero locus of its ideal: `V(I(V)) = V`. -/
@[simp]
theorem zeroLocus_vanishingIdeal_zeroLocus
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) :
    zeroLocus (vanishingIdeal (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) : Set _) =
      zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) :=
  gc_homogeneousIdeal.l_u_l_eq_l I

@[simp]
theorem vanishingIdeal_zeroLocus_vanishingIdeal (X : Set (ℙ k (Fin (n + 1) → k))) :
    vanishingIdeal (zeroLocus (vanishingIdeal X)) = vanishingIdeal X :=
  gc_homogeneousIdeal.u_l_u_eq_u X

@[simp]
theorem vanishingIdeal_empty :
    vanishingIdeal (∅ : Set (ℙ k (Fin (n + 1) → k))) = ⊤ :=
  gc_homogeneousIdeal.u_top

theorem vanishingIdeal_union (X Y : Set (ℙ k (Fin (n + 1) → k))) :
    vanishingIdeal (X ∪ Y) = vanishingIdeal X ⊓ vanishingIdeal Y :=
  gc_homogeneousIdeal.u_inf

theorem vanishingIdeal_iUnion {ι : Sort*} (X : ι → Set (ℙ k (Fin (n + 1) → k))) :
    vanishingIdeal (⋃ i, X i) = ⨅ i, vanishingIdeal (X i) :=
  gc_homogeneousIdeal.u_iInf

/-- Over an infinite field, only the zero polynomial vanishes on all of `ℙⁿ`. -/
@[simp]
theorem vanishingIdeal_univ [Infinite k] :
    vanishingIdeal (Set.univ : Set (ℙ k (Fin (n + 1) → k))) = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  have hd : ∀ d, homogeneousComponent d f = 0 := fun d ↦ by
    have hF := homogeneousComponent_isHomogeneous d f
    have hv : ∀ v : Fin (n + 1) → k, v ≠ 0 → eval v (homogeneousComponent d f) = 0 :=
      fun v hv ↦ by
        have := mem_vanishingIdeal_iff_subset_zeroLocus.1
          ((mem_vanishingIdeal_iff_of_isHomogeneous hF).2 fun P _ ↦
            mem_vanishingIdeal_iff.1 hf d P trivial) (Set.mem_univ (mk k v hv))
        simpa using (mk_mem_zeroLocus_iff_forall_smul v hv).1 this _ rfl 1 one_ne_zero
    refine hF.funext (isHomogeneous_zero _ _ d) fun r ↦ ?_
    rw [map_zero]
    by_cases hr : r = 0
    · have he : (Pi.single 0 1 : Fin (n + 1) → k) ≠ 0 := by simp
      have := hF.eval_smul 0 (Pi.single 0 1)
      rw [hv _ he, mul_zero, zero_smul] at this
      rwa [hr]
    · exact hv r hr
  rw [← sum_homogeneousComponent f]
  simp [hd]

/-- The vanishing ideal of a set of points is radical. -/
theorem isRadical_vanishingIdeal (X : Set (ℙ k (Fin (n + 1) → k))) :
    (vanishingIdeal X).toIdeal.IsRadical := by
  set J := MvPolynomial.vanishingIdeal k (cone X \ {0})
  have hJ : J.IsRadical := fun f ⟨m, hm⟩ ↦ MvPolynomial.mem_vanishingIdeal_iff.2 fun v hv ↦
    eq_zero_of_pow_eq_zero (by rw [← map_pow]; exact MvPolynomial.mem_vanishingIdeal_iff.1 hm v hv)
  have hle : (vanishingIdeal X).toIdeal.radical ≤ J :=
    hJ.radical ▸ Ideal.radical_mono (Ideal.toIdeal_homogeneousCore_le _ _)
  exact (Ideal.homogeneousCore.gc _ ⟨_, (vanishingIdeal X).isHomogeneous.radical⟩ J).1 hle

/-- **The ideal of the cone.** Over an infinite field, the affine ideal of the cone over a
nonempty set `X ⊆ ℙⁿ` is `I(X)`. -/
theorem vanishingIdeal_cone [Infinite k] (hX : X.Nonempty) :
    MvPolynomial.vanishingIdeal k (cone X) = (vanishingIdeal X).toIdeal := by
  ext f
  rw [HomogeneousIdeal.mem_iff, MvPolynomial.mem_vanishingIdeal_iff,
    mem_vanishingIdeal_iff_subset_zeroLocus]
  refine ⟨fun h P hP ↦ ?_, fun h v hv ↦ ?_⟩
  · rw [mem_zeroLocus_iff_forall_smul_rep]
    rintro _ rfl c -
    exact h _ (smul_mem_cone (rep_mem_cone_iff.2 hP) c)
  by_cases hv0 : v = 0
  · subst hv0
    obtain ⟨P, hP⟩ := hX
    have h0 := eval_homogeneousComponent_eq_zero_of_forall_smul
      ((mem_zeroLocus_iff_forall_smul_rep.1 (h hP)) f rfl) 0
    simpa [homogeneousComponent_zero, ← constantCoeff_eq] using h0
  · simpa using (mk_mem_zeroLocus_iff_forall_smul v hv0).1
      (h ((mem_cone_iff_of_ne_zero hv0).1 hv)) f rfl 1 one_ne_zero

end Cone

/-! ### Points -/

/-- The point `[a]` is the common zero locus of the linear forms `aᵢXⱼ - aⱼXᵢ`. -/
theorem zeroLocus_range_linearForms (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    zeroLocus (Set.range fun ij : Fin (n + 1) × Fin (n + 1) ↦
      C (a ij.1) * X ij.2 - C (a ij.2) * X ij.1) = {mk k a ha} := by
  ext P
  induction P using Projectivization.ind with | h v hv =>
  rw [mk_mem_zeroLocus_iff (by
      rintro _ ⟨ij, rfl⟩
      exact ⟨1, (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)⟩),
    Set.mem_singleton_iff, mk_eq_mk_iff' k v a hv ha]
  simp only [Set.mem_range, Prod.exists, forall_exists_index]
  constructor
  · intro h
    have h' : ∀ x y, a x * v y = a y * v x := fun x y ↦ by
      simpa [sub_eq_zero] using h _ x y rfl
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := Function.ne_iff.1 ha
    refine ⟨v i / a i, funext fun j ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_eq_iff hi]
    linear_combination -h' i j
  · rintro ⟨c, rfl⟩ _ i j rfl
    simp only [map_sub, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    ring

/-- Substituting `X ↦ (bⱼ Xᵢ)ⱼ` into a form of degree `d` gives `f(b) Xᵢᵈ`. -/
private theorem aeval_C_mul_X_of_isHomogeneous {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (b : Fin (n + 1) → k) (i : Fin (n + 1)) :
    aeval (fun j ↦ C (b j) * X i) f = X i ^ d * C (eval b f) := by
  have h := (hf.map (C : k →+* MvPolynomial (Fin (n + 1)) k)).eval_smul (X i) (C ∘ b)
  rw [eval_map, eval_map, ← eval₂_comp] at h
  rw [← h, aeval_def]
  congr 1
  funext j
  simp [mul_comm]

/-- The homogeneous ideal of the point `[a]` is spanned by the linear forms `aᵢXⱼ - aⱼXᵢ`. -/
theorem vanishingIdeal_singleton (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    (vanishingIdeal {mk k a ha}).toIdeal = Ideal.span (Set.range
      fun ij : Fin (n + 1) × Fin (n + 1) ↦ C (a ij.1) * X ij.2 - C (a ij.2) * X ij.1) := by
  set L := Ideal.span (Set.range
    fun ij : Fin (n + 1) × Fin (n + 1) ↦ C (a ij.1) * X ij.2 - C (a ij.2) * X ij.1)
  have hhom : ∀ g ∈ Set.range fun ij : Fin (n + 1) × Fin (n + 1) ↦
      C (a ij.1) * X ij.2 - C (a ij.2) * X ij.1, g.IsHomogeneous 1 := by
    rintro _ ⟨ij, rfl⟩
    exact (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.2 fun g hg ↦ ?_)
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := Function.ne_iff.1 ha
    let σ : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
      aeval fun j ↦ C (a j / a i) * X i
    have hσ : (Ideal.Quotient.mkₐ k L).comp σ = Ideal.Quotient.mkₐ k L := by
      refine algHom_ext fun j ↦ ?_
      simp only [AlgHom.comp_apply, σ, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
      refine (Ideal.Quotient.eq.2 ?_).symm
      have : X j - C (a j / a i) * X i = C (a i)⁻¹ * (C (a i) * X j - C (a j) * X i) := by
        rw [mul_sub, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, inv_mul_cancel₀ hi, C_1,
          one_mul, div_eq_inv_mul]
      rw [this]
      exact L.mul_mem_left _ (Ideal.subset_span ⟨(i, j), rfl⟩)
    rw [← sum_homogeneousComponent f]
    refine Ideal.sum_mem _ fun d _ ↦ ?_
    have hF := homogeneousComponent_isHomogeneous d f
    have h0 : eval a (homogeneousComponent d f) = 0 := by
      have := mem_vanishingIdeal_iff.1 (HomogeneousIdeal.mem_iff.1 hf) d _ rfl
      rwa [hF.eval_rep_mk_eq_zero_iff] at this
    have hσF : σ (homogeneousComponent d f) = 0 := by
      have hb : (fun j ↦ a j / a i) = (a i)⁻¹ • a := funext fun j ↦ by
        simp [div_eq_inv_mul]
      simp only [σ, aeval_C_mul_X_of_isHomogeneous hF, hb, hF.eval_smul, h0, mul_zero, map_zero]
    have := Ideal.Quotient.eq.1 (DFunLike.congr_fun hσ (homogeneousComponent d f))
    simpa [σ, hσF] using this
  · rw [SetLike.mem_coe, HomogeneousIdeal.mem_iff,
      mem_vanishingIdeal_iff_of_isHomogeneous (hhom g hg)]
    rintro _ rfl
    rw [(hhom g hg).eval_rep_mk_eq_zero_iff]
    exact (mk_mem_zeroLocus_iff (fun g hg ↦ ⟨1, hhom g hg⟩) a ha).1
      (by rw [zeroLocus_range_linearForms]; rfl) g hg

/-- The homogeneous ideal of a point is prime. -/
instance isPrime_vanishingIdeal_singleton (P : ℙ k (Fin (n + 1) → k)) :
    (vanishingIdeal {P}).toIdeal.IsPrime := by
  refine (vanishingIdeal {P}).isHomogeneous.isPrime_of_homogeneous_mem_or_mem ?_ ?_
  · refine fun h ↦ one_ne_zero (α := k) ?_
    have := (mem_vanishingIdeal_iff_of_isHomogeneous (isHomogeneous_one _ _)).1
      (h ▸ Submodule.mem_top : (1 : MvPolynomial (Fin (n + 1)) k) ∈ (vanishingIdeal {P}).toIdeal)
      P rfl
    simp at this
  · rintro x y ⟨d, hx⟩ ⟨e, hy⟩ hxy
    rw [mem_homogeneousSubmodule] at hx hy
    simp only [HomogeneousIdeal.mem_iff, mem_vanishingIdeal_iff_of_isHomogeneous hx,
      mem_vanishingIdeal_iff_of_isHomogeneous hy,
      mem_vanishingIdeal_iff_of_isHomogeneous (hx.mul hy), Set.mem_singleton_iff, forall_eq,
      map_mul, mul_eq_zero] at hxy ⊢
    exact hxy

end PlaneCurves.ProjectiveSpace

end
