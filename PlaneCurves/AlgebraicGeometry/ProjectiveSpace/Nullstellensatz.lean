/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.HomogeneousIdeal
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal

/-!
# The projective Nullstellensatz

Let `k` be algebraically closed and `I` a homogeneous ideal of `k[X₀, …, Xₙ]`. This file proves
the projective Nullstellensatz of Fulton, §4.2, through the affine cone over `V(I)`.

## Main results

* `zeroLocus_eq_empty_tfae`: `V(I) = ∅` exactly when `I` contains every form of degree at least
  some `N`, exactly when `I` contains a power of the ideal `(X₀, …, Xₙ)` of the variables,
  exactly when the radical of `I` contains `(X₀, …, Xₙ)`.
* `vanishingIdeal_zeroLocus_eq_radical`: if `V(I) ≠ ∅`, then `I(V(I)) = Rad(I)`.
* `bijOn_vanishingIdeal`: `V ↦ I(V)` is a bijection from the projective algebraic sets onto the
  homogeneous radical ideals other than `(X₀, …, Xₙ)`, and `bijOn_vanishingIdeal_isPrime`
  restricts it to the algebraic sets with prime ideal and the homogeneous primes other than
  `(X₀, …, Xₙ)`.

The implications that do not need `k` to be algebraically closed, or `I` to be homogeneous, are
stated without these hypotheses: `zeroLocus_eq_empty_of_idealOfVars_le_radical`.

## Implementation notes

A projective algebraic set is the zero locus of a homogeneous ideal, an element of
`Set.range fun I : HomogeneousIdeal _ ↦ zeroLocus I`. Over an infinite field, the zero locus of
any set of polynomials is of this form (`zeroLocus_homogeneousComponent` and `zeroLocus_span`).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {n : ℕ} {I : Ideal (MvPolynomial (Fin (n + 1)) k)}

/-- An ideal whose radical contains the variables has no zero in `ℙⁿ`. -/
theorem zeroLocus_eq_empty_of_idealOfVars_le_radical
    (h : idealOfVars (Fin (n + 1)) k ≤ I.radical) :
    zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun P hP ↦ P.rep_ne_zero (funext fun i ↦ ?_)
  obtain ⟨m, hm⟩ := h (Ideal.subset_span ⟨i, rfl⟩)
  have := (mem_zeroLocus_iff_forall_smul_rep.1 hP) _ hm 1 one_ne_zero
  simp only [one_smul, map_pow, eval_X] at this
  exact eq_zero_of_pow_eq_zero this

/-- The ideal of the variables has no zero in `ℙⁿ`. -/
@[simp]
theorem zeroLocus_idealOfVars :
    zeroLocus (idealOfVars (Fin (n + 1)) k : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ :=
  zeroLocus_eq_empty_of_idealOfVars_le_radical Ideal.le_radical

/-- The ideal of a projective algebraic set is not the ideal of the variables. -/
theorem vanishingIdeal_zeroLocus_ne_idealOfVars
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) :
    (vanishingIdeal (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal ≠
      idealOfVars (Fin (n + 1)) k := by
  intro h
  have he : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ := by
    rw [← zeroLocus_vanishingIdeal_zeroLocus]
    exact zeroLocus_eq_empty_of_idealOfVars_le_radical (h ▸ Ideal.le_radical)
  rw [he, vanishingIdeal_empty, HomogeneousIdeal.toIdeal_top] at h
  exact (isMaximal_idealOfVars (Fin (n + 1)) k).ne_top h.symm

variable [IsAlgClosed k]

/-- **Projective Nullstellensatz**, part (1). Over an algebraically closed field, a homogeneous
ideal has no zero in `ℙⁿ` exactly when its radical contains the variables. -/
theorem zeroLocus_eq_empty_iff_idealOfVars_le_radical
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ ↔
      idealOfVars (Fin (n + 1)) k ≤ I.radical := by
  refine ⟨fun h f hf ↦ ?_, zeroLocus_eq_empty_of_idealOfVars_le_radical⟩
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := k), MvPolynomial.mem_vanishingIdeal_iff]
  intro v hv
  by_cases hv0 : v = 0
  · subst hv0
    rw [idealOfVars_eq_ker_eval_zero, RingHom.mem_ker] at hf
    simpa using hf
  · have := (mk_mem_zeroLocus_iff_mem_zeroLocus hI v hv0).2 hv
    simp [h] at this

/-- **Projective Nullstellensatz**, part (1). Over an algebraically closed field, a homogeneous
ideal has no zero in `ℙⁿ` exactly when it contains a power of the ideal of the variables. -/
theorem zeroLocus_eq_empty_iff_exists_pow_idealOfVars_le
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ ↔
      ∃ N, idealOfVars (Fin (n + 1)) k ^ N ≤ I := by
  rw [zeroLocus_eq_empty_iff_idealOfVars_le_radical hI]
  exact ⟨fun h ↦ Ideal.exists_pow_le_of_le_radical_of_fg h (fg_idealOfVars _ _),
    fun ⟨N, hN⟩ _ hf ↦ ⟨N, hN (Ideal.pow_mem_pow hf N)⟩⟩

/-- **Projective Nullstellensatz**, part (1). Over an algebraically closed field, a homogeneous
ideal has no zero in `ℙⁿ` exactly when it contains every form of degree at least some `N`. -/
theorem zeroLocus_eq_empty_iff_exists_forall_isHomogeneous_mem
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ ↔
      ∃ N, ∀ d, N ≤ d → ∀ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d → f ∈ I := by
  simp_rw [zeroLocus_eq_empty_iff_exists_pow_idealOfVars_le hI, pow_idealOfVars_le_iff]

/-- **Projective Nullstellensatz**, part (1). For a homogeneous ideal `I` over an algebraically
closed field, the following are equivalent: `V(I) = ∅`; `I` contains every form of degree at
least some `N`; `I` contains a power of the ideal `(X₀, …, Xₙ)`; the radical of `I` contains
`(X₀, …, Xₙ)`. -/
theorem zeroLocus_eq_empty_tfae
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k)) :
    List.TFAE [zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅,
      ∃ N, ∀ d, N ≤ d → ∀ f : MvPolynomial (Fin (n + 1)) k, f.IsHomogeneous d → f ∈ I,
      ∃ N, idealOfVars (Fin (n + 1)) k ^ N ≤ I,
      idealOfVars (Fin (n + 1)) k ≤ I.radical] := by
  tfae_have 1 ↔ 2 := zeroLocus_eq_empty_iff_exists_forall_isHomogeneous_mem hI
  tfae_have 1 ↔ 3 := zeroLocus_eq_empty_iff_exists_pow_idealOfVars_le hI
  tfae_have 1 ↔ 4 := zeroLocus_eq_empty_iff_idealOfVars_le_radical hI
  tfae_finish

/-- **Projective Nullstellensatz**, part (2). Over an algebraically closed field, the ideal of the
zero locus of a homogeneous ideal `I` with a zero in `ℙⁿ` is the radical of `I`. -/
theorem vanishingIdeal_zeroLocus_eq_radical
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    (h : (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty) :
    (vanishingIdeal (zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))).toIdeal = I.radical := by
  rw [← vanishingIdeal_cone h, cone_zeroLocus hI h,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]

/-- **Projective Nullstellensatz**, part (3). Over an algebraically closed field, `V ↦ I(V)` is
a bijection from the projective algebraic sets onto the homogeneous radical ideals other than
the ideal `(X₀, …, Xₙ)` of the variables; it sends `∅` to the unit ideal. -/
theorem bijOn_vanishingIdeal :
    Set.BijOn vanishingIdeal
      (Set.range fun I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) ↦
        zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))
      {J | J.toIdeal.IsRadical ∧ J.toIdeal ≠ idealOfVars (Fin (n + 1)) k} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨I, rfl⟩
    exact ⟨isRadical_vanishingIdeal _, vanishingIdeal_zeroLocus_ne_idealOfVars I⟩
  · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩ h
    dsimp only at h ⊢
    rw [← zeroLocus_vanishingIdeal_zeroLocus I, h, zeroLocus_vanishingIdeal_zeroLocus]
  · rintro J ⟨hrad, hne⟩
    refine ⟨_, ⟨J, rfl⟩, ?_⟩
    dsimp only
    rcases (zeroLocus (J : Set (MvPolynomial (Fin (n + 1)) k))).eq_empty_or_nonempty with he | he
    · have hle := (zeroLocus_eq_empty_iff_idealOfVars_le_radical J.isHomogeneous).1 he
      rw [hrad.radical] at hle
      have htop : J = ⊤ := by
        by_contra hJ
        exact hne ((isMaximal_idealOfVars (Fin (n + 1)) k).eq_of_le
          (fun h ↦ hJ ((HomogeneousIdeal.eq_top_iff J).2 h)) hle).symm
      rw [he, vanishingIdeal_empty, htop]
    · exact HomogeneousIdeal.ext
        ((vanishingIdeal_zeroLocus_eq_radical J.isHomogeneous he).trans hrad.radical)

/-- **Projective Nullstellensatz**, part (3), for primes. Over an algebraically closed field,
`V ↦ I(V)` is a bijection from the projective algebraic sets whose ideal is prime onto the
homogeneous prime ideals other than the ideal `(X₀, …, Xₙ)` of the variables. -/
theorem bijOn_vanishingIdeal_isPrime :
    Set.BijOn vanishingIdeal
      {V | V ∈ Set.range (fun I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) ↦
        zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) ∧ (vanishingIdeal V).toIdeal.IsPrime}
      {J | J.toIdeal.IsPrime ∧ J.toIdeal ≠ idealOfVars (Fin (n + 1)) k} := by
  refine ⟨fun V hV ↦ ⟨hV.2, (bijOn_vanishingIdeal.mapsTo hV.1).2⟩,
    bijOn_vanishingIdeal.injOn.mono fun V hV ↦ hV.1, fun J hJ ↦ ?_⟩
  obtain ⟨V, hV, rfl⟩ := bijOn_vanishingIdeal.surjOn ⟨hJ.1.isRadical, hJ.2⟩
  exact ⟨V, ⟨hV, hJ.1⟩, rfl⟩

end PlaneCurves.ProjectiveSpace

end
