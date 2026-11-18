/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Nullstellensatz
public import PlaneCurves.RingTheory.Ideal.Radical
public import PlaneCurves.RingTheory.MvPolynomial.BinaryForm.Basis
public import PlaneCurves.RingTheory.UniqueFactorizationDomain.Radical
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.RingTheory.MvPolynomial.CommonZero
public import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Hypersurfaces and hyperplanes in projective space

Let `k` be algebraically closed and `n ≥ 1`. This file proves the part of the projective
Nullstellensatz of Fulton, §4.2, that concerns hypersurfaces, and assembles the whole theorem.

## Main results

* `zeroLocus_nonempty_of_card_le`: at most `n` forms of positive degree have a common zero in
  `ℙⁿ`; in particular every form of positive degree has a zero
  (`zeroLocus_singleton_nonempty`).
* `vanishingIdeal_zeroLocus_singleton`: for a form `F`, `I(V(F)) = Rad (F)`;
  `vanishingIdeal_zeroLocus_singleton_eq_span_prod`: if `F = λ F₁^e₁ ⋯ F_r^e_r` with pairwise
  non-associated irreducible `Fᵢ`, then `I(V(F)) = (F₁ ⋯ F_r)`.
* `zeroLocus_singleton_eq_iff_associated` and `exists_squarefree_zeroLocus_eq`: `F ↦ V(F)` is a
  bijection from the squarefree forms of positive degree, up to nonzero scalars, onto the
  hypersurfaces; `isPrime_vanishingIdeal_zeroLocus_singleton_iff`: irreducible forms give the
  irreducible hypersurfaces.
* `vanishingIdeal_zeroLocus_singleton_of_degree_eq_one`: the ideal of a hyperplane `V(L)` is
  `(L)`; `zeroLocus_singleton_X`: the coordinate hyperplane `V(Xᵢ)` is the complement of the
  standard affine chart `Uᵢ`.
* `vanishingIdeal_zeroLocus_eq_radical_and_hypersurface`: the projective Nullstellensatz,
  parts (1)–(4).

## Implementation notes

A hypersurface is the zero locus `zeroLocus {F}` of a form `F` of positive degree; it has no
definition of its own.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {n : ℕ} {f g : MvPolynomial (Fin (n + 1)) k} {d e : ℕ}

/-- The zero locus of a unit is empty. -/
theorem zeroLocus_singleton_eq_empty_of_isUnit (hf : IsUnit f) :
    zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ := by
  rw [← zeroLocus_span, Ideal.span_singleton_eq_top.2 hf, Submodule.top_coe, zeroLocus_univ]

/-- Associated polynomials have the same zero locus. -/
theorem zeroLocus_singleton_eq_of_associated (h : Associated f g) :
    zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus {g} := by
  rw [← zeroLocus_span, Ideal.span_singleton_eq_span_singleton.2 h, zeroLocus_span]

/-- A nonzero form `F` has the same zero locus as some squarefree form `G` dividing it, the
product of its distinct prime factors. -/
theorem exists_squarefree_zeroLocus_eq (hf0 : f ≠ 0) (hf : f.IsHomogeneous d) :
    ∃ g, g ∣ f ∧ Squarefree g ∧ g.IsHomogeneous g.totalDegree ∧
      zeroLocus ({g} : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus {f} := by
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := MvPolynomial (Fin (n + 1)) k)
  obtain ⟨h, hh⟩ := UniqueFactorizationMonoid.radical_dvd_self (a := f)
  refine ⟨_, UniqueFactorizationMonoid.radical_dvd_self,
    UniqueFactorizationMonoid.squarefree_radical,
    (hh ▸ hf).of_mul_left (right_ne_zero_of_mul (hh ▸ hf0)), ?_⟩
  rw [← zeroLocus_span {UniqueFactorizationMonoid.radical f},
    ← Ideal.radical_span_singleton_eq_span_radical hf0, zeroLocus_radical, zeroLocus_span]

variable [IsAlgClosed k]

/-- At most `n` forms of positive degree have a common zero in `ℙⁿ`, over an algebraically
closed field (Fulton, §4.2, for one form; the general case is the projective dimension
theorem). -/
theorem zeroLocus_nonempty_of_card_le {s : Finset (MvPolynomial (Fin (n + 1)) k)}
    (hs : s.card ≤ n) (hs' : ∀ f ∈ s, ∃ d ≠ 0, f.IsHomogeneous d) :
    (zeroLocus (s : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
  obtain ⟨x, hx, h⟩ := exists_ne_zero_forall_aeval_eq_zero (K := k) (s := s)
    (by simpa using Nat.lt_succ_of_le hs) fun f hf ↦ by
      obtain ⟨d, hd0, hd⟩ := hs' f hf
      exact hd.coeff_eq_zero (by simpa using Ne.symm hd0)
  refine ⟨mk k x hx, (mk_mem_zeroLocus_iff (fun f hf ↦ ?_) x hx).2 fun f hf ↦ ?_⟩
  · obtain ⟨d, -, hd⟩ := hs' f hf
    exact ⟨d, hd⟩
  · simpa using h f hf

/-- Over an algebraically closed field, a form of positive degree has a zero in `ℙⁿ`, `n ≥ 1`. -/
theorem zeroLocus_singleton_nonempty (hn : n ≠ 0) (hf : f.IsHomogeneous d) (hd : d ≠ 0) :
    (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
  simpa using zeroLocus_nonempty_of_card_le (s := {f}) (by simpa [Nat.one_le_iff_ne_zero])
    (by rintro _ hg; rw [Finset.mem_singleton.1 hg]; exact ⟨d, hd, hf⟩)

/-- Over an algebraically closed field and for `n ≥ 1`, the ideal of the zero locus of a form `F`
is the radical of `(F)`. -/
theorem vanishingIdeal_zeroLocus_singleton (hn : n ≠ 0) (hf : f.IsHomogeneous d) :
    (vanishingIdeal (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal =
      (Ideal.span {f}).radical := by
  obtain rfl | hf0 := eq_or_ne f 0
  · rw [zeroLocus_singleton_zero, vanishingIdeal_univ, Ideal.span_singleton_eq_bot.2 rfl,
      Ideal.radical_bot_of_isReduced, HomogeneousIdeal.toIdeal_bot]
  obtain rfl | hd := eq_or_ne d 0
  · have hu : IsUnit f := isUnit_iff_totalDegree_of_isReduced.2
      ⟨isUnit_iff_ne_zero.2 fun h ↦ hf0 ?_, hf.totalDegree hf0⟩
    · rw [zeroLocus_singleton_eq_empty_of_isUnit hu, vanishingIdeal_empty,
        Ideal.span_singleton_eq_top.2 hu, Ideal.radical_top, HomogeneousIdeal.toIdeal_top]
    · rw [totalDegree_eq_zero_iff_eq_C.1 (hf.totalDegree hf0), h, map_zero]
  have hI : (Ideal.span {f}).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    Ideal.homogeneous_span _ _ fun _ hg ↦ ⟨d, (mem_homogeneousSubmodule d _).2 (hg ▸ hf)⟩
  have := vanishingIdeal_zeroLocus_eq_radical hI
  rw [zeroLocus_span] at this
  exact this (zeroLocus_singleton_nonempty hn hf hd)

/-- Over an algebraically closed field and for `n ≥ 1`, the ideal of the zero locus of a
squarefree form `F` is `(F)`. -/
theorem vanishingIdeal_zeroLocus_singleton_of_squarefree (hn : n ≠ 0) (hf : f.IsHomogeneous d)
    (hsf : Squarefree f) :
    (vanishingIdeal (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal =
      Ideal.span {f} := by
  rw [vanishingIdeal_zeroLocus_singleton hn hf,
    (isRadical_iff_span_singleton.1 hsf.isRadical).radical]

/-- **Ideal of a hypersurface.** Over an algebraically closed field and for `n ≥ 1`, if
`F = λ F₁^e₁ ⋯ F_r^e_r` is a form with `λ ≠ 0`, pairwise non-associated irreducible `Fᵢ` and
`eᵢ ≥ 1`, then `I(V(F)) = (F₁ ⋯ F_r)`. -/
theorem vanishingIdeal_zeroLocus_singleton_eq_span_prod {ι : Type*} (hn : n ≠ 0) {s : Finset ι}
    {c : k} {F : ι → MvPolynomial (Fin (n + 1)) k} {m : ι → ℕ} (hc : c ≠ 0)
    (hF : ∀ i ∈ s, Irreducible (F i)) (hFF : Set.Pairwise s fun i j ↦ ¬Associated (F i) (F j))
    (hm : ∀ i ∈ s, m i ≠ 0) (hd : (C c * ∏ i ∈ s, F i ^ m i).IsHomogeneous d) :
    (vanishingIdeal (zeroLocus ({C c * ∏ i ∈ s, F i ^ m i} :
      Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal = Ideal.span {∏ i ∈ s, F i} := by
  have hsq := UniqueFactorizationMonoid.squarefree_prod_of_irreducible hF hFF
  have hu : IsUnit (C c : MvPolynomial (Fin (n + 1)) k) := (isUnit_iff_ne_zero.2 hc).map C
  rw [vanishingIdeal_zeroLocus_singleton hn hd]
  refine Ideal.radical_span_singleton_eq_of_dvd hsq.isRadical (m := s.sup m) ?_ ?_
  · exact Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦
      dvd_pow_self _ (hm i hi)) _
  · rw [hu.mul_left_dvd, ← Finset.prod_pow]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi ↦ pow_dvd_pow _ (Finset.le_sup hi)

/-- **Hypersurfaces determine their reduced equations.** Over an algebraically closed field and
for `n ≥ 1`, two squarefree forms have the same zero locus exactly when they are associated, that
is, differ by a nonzero scalar factor. -/
theorem zeroLocus_singleton_eq_iff_associated (hn : n ≠ 0) (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous e) (hsf : Squarefree f) (hsg : Squarefree g) :
    zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus {g} ↔ Associated f g := by
  refine ⟨fun h ↦ ?_, zeroLocus_singleton_eq_of_associated⟩
  rw [← Ideal.span_singleton_eq_span_singleton,
    ← vanishingIdeal_zeroLocus_singleton_of_squarefree hn hf hsf, h,
    vanishingIdeal_zeroLocus_singleton_of_squarefree hn hg hsg]

/-- Over an algebraically closed field and for `n ≥ 1`, every hypersurface `V(F)`, `F` a form of
positive degree, is the zero locus of a squarefree form of positive degree. -/
theorem exists_squarefree_zeroLocus_eq_of_degree_ne_zero (hn : n ≠ 0) (hf0 : f ≠ 0)
    (hf : f.IsHomogeneous d) (hd : d ≠ 0) :
    ∃ g, Squarefree g ∧ g.IsHomogeneous g.totalDegree ∧ g.totalDegree ≠ 0 ∧
      zeroLocus ({g} : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus {f} := by
  have hne := zeroLocus_singleton_nonempty hn hf hd
  obtain ⟨g, -, hsg, hg, hgf⟩ := exists_squarefree_zeroLocus_eq hf0 hf
  refine ⟨g, hsg, hg, fun h0 ↦ ?_, hgf⟩
  have hu : IsUnit g := isUnit_iff_totalDegree_of_isReduced.2
    ⟨isUnit_iff_ne_zero.2 fun h ↦ hsg.ne_zero ?_, h0⟩
  · rw [← hgf, zeroLocus_singleton_eq_empty_of_isUnit hu] at hne
    exact Set.not_nonempty_empty hne
  · rw [totalDegree_eq_zero_iff_eq_C.1 h0, h, map_zero]

/-- **Irreducible hypersurfaces.** Over an algebraically closed field and for `n ≥ 1`, the zero
locus of a squarefree form `F` has a prime ideal, that is, is irreducible, exactly when `F` is
irreducible. -/
theorem isPrime_vanishingIdeal_zeroLocus_singleton_iff (hn : n ≠ 0) (hf : f.IsHomogeneous d)
    (hsf : Squarefree f) :
    (vanishingIdeal (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal.IsPrime ↔
      Irreducible f := by
  rw [vanishingIdeal_zeroLocus_singleton_of_squarefree hn hf hsf,
    Ideal.span_singleton_prime hsf.ne_zero, UniqueFactorizationMonoid.irreducible_iff_prime]

/-- **Hyperplanes.** Over an algebraically closed field and for `n ≥ 1`, the ideal of the
hyperplane `V(L)` of a nonzero linear form `L` is `(L)`, a prime ideal. -/
theorem vanishingIdeal_zeroLocus_singleton_of_degree_eq_one (hn : n ≠ 0) (hf : f.IsHomogeneous 1)
    (hf0 : f ≠ 0) :
    (vanishingIdeal (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal =
      Ideal.span {f} :=
  vanishingIdeal_zeroLocus_singleton_of_squarefree hn hf
    (irreducible_of_totalDegree_eq_one' (hf.totalDegree hf0)).squarefree

omit [IsAlgClosed k] in
/-- The coordinate hyperplane `V(Xᵢ)` is the complement of the standard affine chart `Uᵢ`. -/
theorem zeroLocus_singleton_X (i : Fin (n + 1)) :
    zeroLocus ({X i} : Set (MvPolynomial (Fin (n + 1)) k)) = (affineOpen i)ᶜ := by
  ext P
  rw [mem_zeroLocus_iff_eval_rep (by rintro _ rfl; exact ⟨1, isHomogeneous_X k i⟩)]
  simp [mem_affineOpen_iff]

/-- **Projective Nullstellensatz.** Let `k` be algebraically closed and `R = k[X₀, …, Xₙ]`.

* (1) For a homogeneous ideal `I`, the following are equivalent: `V(I) = ∅`; `I` contains every
  form of degree at least some `N`; `I` contains a power of `(X₀, …, Xₙ)`; the radical of `I`
  contains `(X₀, …, Xₙ)`.
* (2) For a homogeneous ideal `I` with `V(I) ≠ ∅`, `I(V(I)) = Rad (I)`.
* (3) `V ↦ I(V)` is a bijection from the projective algebraic sets onto the homogeneous radical
  ideals other than `(X₀, …, Xₙ)`, and from those with prime ideal (the projective varieties)
  onto the homogeneous primes other than `(X₀, …, Xₙ)`.
* (4) Let `n ≥ 1`. Every form of positive degree has a zero in `ℙⁿ`. If
  `F = λ F₁^e₁ ⋯ F_r^e_r` is a form with `λ ≠ 0`, pairwise non-associated irreducible `Fᵢ` and
  `eᵢ ≥ 1`, then `I(V(F)) = (F₁ ⋯ F_r)`. Two squarefree forms have the same zero locus exactly
  when they differ by a nonzero scalar, and every hypersurface `V(F)` is the zero locus of a
  squarefree form of positive degree, so that `F ↦ V(F)` is a bijection from the squarefree forms
  of positive degree up to scalars onto the hypersurfaces; the hypersurface of a squarefree form
  is irreducible exactly when the form is. The ideal of a hyperplane `V(L)`, `L` a nonzero linear
  form, is `(L)`, and the coordinate hyperplane `V(Xᵢ)` is the complement of the chart `Uᵢ`.

Milestone: *Projective Nullstellensatz*. -/
theorem vanishingIdeal_zeroLocus_eq_radical_and_hypersurface :
    -- (1)
    (∀ I : Ideal (MvPolynomial (Fin (n + 1)) k),
      I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) →
      List.TFAE [zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅,
        ∃ N, ∀ d, N ≤ d → ∀ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d → f ∈ I,
        ∃ N, idealOfVars (Fin (n + 1)) k ^ N ≤ I,
        idealOfVars (Fin (n + 1)) k ≤ I.radical]) ∧
    -- (2)
    (∀ I : Ideal (MvPolynomial (Fin (n + 1)) k),
      I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) →
      (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
      (vanishingIdeal (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal =
        I.radical) ∧
    -- (3)
    Set.BijOn vanishingIdeal
      (Set.range fun I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) ↦
        zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))
      {J | J.toIdeal.IsRadical ∧ J.toIdeal ≠ idealOfVars (Fin (n + 1)) k} ∧
    Set.BijOn vanishingIdeal
      {V | V ∈ Set.range (fun I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) ↦
        zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) ∧ (vanishingIdeal V).toIdeal.IsPrime}
      {J | J.toIdeal.IsPrime ∧ J.toIdeal ≠ idealOfVars (Fin (n + 1)) k} ∧
    -- (4)
    (n ≠ 0 →
      (∀ (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ), f.IsHomogeneous d → d ≠ 0 →
        (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty) ∧
      (∀ (r : ℕ) (c : k) (F : Fin r → MvPolynomial (Fin (n + 1)) k) (m : Fin r → ℕ) (d : ℕ),
        c ≠ 0 → (∀ i, Irreducible (F i)) → Pairwise (fun i j ↦ ¬Associated (F i) (F j)) →
        (∀ i, m i ≠ 0) → (C c * ∏ i, F i ^ m i).IsHomogeneous d →
        (vanishingIdeal (zeroLocus ({C c * ∏ i, F i ^ m i} :
          Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal = Ideal.span {∏ i, F i}) ∧
      (∀ (f g : MvPolynomial (Fin (n + 1)) k) (d e : ℕ), f.IsHomogeneous d → g.IsHomogeneous e →
        Squarefree f → Squarefree g →
        (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus {g} ↔
          Associated f g)) ∧
      (∀ (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ), f ≠ 0 → f.IsHomogeneous d → d ≠ 0 →
        ∃ g, Squarefree g ∧ g.IsHomogeneous g.totalDegree ∧ g.totalDegree ≠ 0 ∧
          zeroLocus ({g} : Set (MvPolynomial (Fin (n + 1)) k)) = zeroLocus {f}) ∧
      (∀ (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ), f.IsHomogeneous d → Squarefree f →
        ((vanishingIdeal (zeroLocus ({f} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal.IsPrime ↔
          Irreducible f)) ∧
      (∀ L : MvPolynomial (Fin (n + 1)) k, L.IsHomogeneous 1 → L ≠ 0 →
        (vanishingIdeal (zeroLocus ({L} : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal =
          Ideal.span {L}) ∧
      (∀ i : Fin (n + 1),
        zeroLocus ({X i} : Set (MvPolynomial (Fin (n + 1)) k)) = (affineOpen i)ᶜ)) :=
  ⟨fun _ hI ↦ zeroLocus_eq_empty_tfae hI, fun _ hI h ↦ vanishingIdeal_zeroLocus_eq_radical hI h,
    bijOn_vanishingIdeal, bijOn_vanishingIdeal_isPrime, fun hn ↦
    ⟨fun _ _ hf hd ↦ zeroLocus_singleton_nonempty hn hf hd,
      fun _ _ _ _ _ hc hF hFF hm hd ↦ vanishingIdeal_zeroLocus_singleton_eq_span_prod hn hc
        (fun i _ ↦ hF i) (fun _ _ _ _ hij ↦ hFF hij) (fun i _ ↦ hm i) hd,
      fun _ _ _ _ hf hg hsf hsg ↦ zeroLocus_singleton_eq_iff_associated hn hf hg hsf hsg,
      fun _ _ hf0 hf hd ↦ exists_squarefree_zeroLocus_eq_of_degree_ne_zero hn hf0 hf hd,
      fun _ _ hf hsf ↦ isPrime_vanishingIdeal_zeroLocus_singleton_iff hn hf hsf,
      fun _ hL hL0 ↦ vanishingIdeal_zeroLocus_singleton_of_degree_eq_one hn hL hL0,
      zeroLocus_singleton_X⟩⟩

end PlaneCurves.ProjectiveSpace

end
