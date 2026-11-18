/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Nullstellensatz
public import PlaneCurves.AlgebraicGeometry.AffineSpace.LocalRing

/-!
# Rational functions and local rings of an affine variety

For a field `k`, a prime ideal `I` of `k[X₁, …, Xₙ]` (the variety `V = V(I)`) and a point
`P ∈ V(I)`, this file defines the function field `k(V)` and the local ring `𝒪_P(V)` as a local
subring of `k(V)`, the localization of `Γ(V) = k[X] ⧸ I` at the ideal of `P`. It gives the value
map `𝒪_P(V) → k`, the comparison with the quotient `𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)` of
`PlaneCurves.AffineSpace.localRing`, the maps induced by polynomial maps, pole sets, and the
prime ideals of `𝒪_P(V)`.

## Main definitions

* `PlaneCurves.AffineSpace.functionField I`: the function field `k(V) = Frac(k[X] ⧸ I)`.
* `PlaneCurves.AffineSpace.coordinateEval P hI`: the value map `Γ(V) → k`, `a ↦ a(P)`.
* `PlaneCurves.AffineSpace.localSubring P hI`: the local ring `𝒪_P(V)`, a `LocalSubring` of
  `k(V)` (built with `LocalSubring.ofPrime`). It is a `Γ(V)`-algebra and a `k`-algebra, and a
  localization of `Γ(V)` at the ideal of `P` (an `IsLocalization.AtPrime` instance).
* `PlaneCurves.AffineSpace.evalAt P hI`: the value map `𝒪_P(V) → k`, `f ↦ f(P)`.
* `PlaneCurves.AffineSpace.residueFieldAlgEquiv P hI`: the residue field of `𝒪_P(V)` is `k`.
* `PlaneCurves.AffineSpace.quotientAlgEquiv P hI`: `𝒪_P(V) ≅ 𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)`.
* `PlaneCurves.AffineSpace.map`, `PlaneCurves.AffineSpace.mapEquiv`: the local homomorphism
  `𝒪_Q(W) → 𝒪_P(V)` induced by a polynomial map `V → W` sending `P` to `Q`, and the isomorphism
  induced by a polynomial isomorphism.
* `PlaneCurves.AffineSpace.denominatorIdeal I f`, `PlaneCurves.AffineSpace.poleSet I f`: the
  ideal of denominators `{G : G f ∈ Γ(V)}` and the pole set of `f ∈ k(V)`.
* `PlaneCurves.AffineSpace.primesOrderIso P hI`: the prime ideals of `𝒪_P(V)` correspond to the
  prime ideals `J` of `k[X]` with `I ≤ J ≤ I_P`.

## Main results

* `PlaneCurves.AffineSpace.mem_localSubring_iff`: `f ∈ 𝒪_P(V)` iff `f = a / b` with `b(P) ≠ 0`.
* `PlaneCurves.AffineSpace.ker_evalAt`: the kernel of the value map is the maximal ideal.
* `PlaneCurves.AffineSpace.isUnit_iff_evalAt_ne_zero`: the units of `𝒪_P(V)` are the functions
  not vanishing at `P`.
* `PlaneCurves.AffineSpace.poleSet_eq_zeroLocus`: the pole set is the zero set of the ideal of
  denominators, so it is algebraic.
* `PlaneCurves.AffineSpace.mem_range_algebraMap_iff`: over an algebraically closed field,
  `Γ(V)` is the intersection of the `𝒪_P(V)`, `P ∈ V` (by the Nullstellensatz).
* `PlaneCurves.AffineSpace.map_unique`, `PlaneCurves.AffineSpace.isLocalHom_map`: the map
  induced by a polynomial map is the unique ring map extending `Γ(W) → Γ(V)`, and is local.
* `PlaneCurves.AffineSpace.localSubring_spec`: the milestone, parts (a)–(f).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.4, Propositions 2 and 3, Problems 2.18, 2.21
  and 2.22
-/

public section

open MvPolynomial IsLocalRing Ideal

namespace MvPolynomial

/-- An ideal vanishes at `x` iff `x` lies in its zero locus. -/
theorem le_vanishingIdeal_singleton_iff {k : Type*} [Field k] {σ : Type*}
    {I : Ideal (MvPolynomial σ k)} {x : σ → k} :
    I ≤ vanishingIdeal k {x} ↔ x ∈ zeroLocus k I := by
  rw [mem_zeroLocus_iff]
  exact ⟨fun h p hp => (mem_vanishingIdeal_singleton_iff _ _).1 (h hp),
    fun h p hp => (mem_vanishingIdeal_singleton_iff _ _).2 (h p hp)⟩

end MvPolynomial

namespace PlaneCurves.AffineSpace

variable {k : Type*} [Field k] {σ : Type*}

section coordinateEval

variable {I : Ideal (MvPolynomial σ k)} (P : σ → k) (hI : I ≤ vanishingIdeal k {P})

/-- The value `a(P)` of an element `a` of the coordinate ring `Γ(V) = k[X] ⧸ I` at a point
`P ∈ V(I)`, as a `k`-algebra map to `k`. -/
noncomputable def coordinateEval : MvPolynomial σ k ⧸ I →ₐ[k] k :=
  Ideal.Quotient.liftₐ I (aeval P) fun _ hf => (mem_vanishingIdeal_singleton_iff P _).1 (hI hf)

theorem coordinateEval_def : coordinateEval P hI = Ideal.Quotient.liftₐ I (aeval P)
    fun _ hf => (mem_vanishingIdeal_singleton_iff P _).1 (hI hf) :=
  (rfl)

@[simp]
theorem coordinateEval_mk (f : MvPolynomial σ k) :
    coordinateEval P hI (Ideal.Quotient.mk I f) = eval P f :=
  (rfl)

theorem coordinateEval_surjective : Function.Surjective (coordinateEval P hI) :=
  fun c => ⟨Ideal.Quotient.mk I (C c), by simp⟩

/-- The kernel of the value map `Γ(V) → k` is the ideal of `P` in `Γ(V)`. -/
theorem ker_coordinateEval :
    RingHom.ker (coordinateEval P hI) = (vanishingIdeal k {P}).map (Ideal.Quotient.mk I) := by
  ext a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.mem_ker, coordinateEval_mk, mem_quotient_iff_mem hI,
    mem_vanishingIdeal_singleton_iff]
  rfl

end coordinateEval

variable (I : Ideal (MvPolynomial σ k)) [I.IsPrime]

/-- The function field `k(V)` of the variety `V = V(I)`, for a prime ideal `I`: the fraction
field of the coordinate ring `Γ(V) = k[X] ⧸ I`. -/
abbrev functionField : Type _ := FractionRing (MvPolynomial σ k ⧸ I)

variable {I} (P : σ → k) (hI : I ≤ vanishingIdeal k {P})

/-- The value map on the image of `Γ(V)` in `k(V)`. -/
noncomputable def rangeEval :
    (algebraMap (MvPolynomial σ k ⧸ I) (functionField I)).range →+* k :=
  (coordinateEval P hI).toRingHom.comp (RingEquiv.ofBijective _
    ⟨fun _ _ h => IsFractionRing.injective _ (functionField I) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).symm.toRingHom

omit [I.IsPrime] in
theorem rangeEval_rangeRestrict (a : MvPolynomial σ k ⧸ I) :
    rangeEval P hI ((algebraMap _ (functionField I)).rangeRestrict a) = coordinateEval P hI a :=
  congrArg (coordinateEval P hI) ((RingEquiv.ofBijective _ _).symm_apply_apply a)

instance : (RingHom.ker (rangeEval P hI)).IsPrime := RingHom.ker_isPrime _

/-- The local ring `𝒪_P(V)` of the variety `V = V(I)` at a point `P ∈ V`, as a local subring of
the function field `k(V)`: the localization of `Γ(V)` at the ideal of `P`. -/
noncomputable def localSubring : LocalSubring (functionField I) :=
  LocalSubring.ofPrime _ (RingHom.ker (rangeEval P hI))

theorem localSubring_def : localSubring P hI =
    LocalSubring.ofPrime _ (RingHom.ker (rangeEval P hI)) :=
  (rfl)

variable {P} in
omit [I.IsPrime] in
include hI in
theorem algebraMap_mk_ne_zero {b : MvPolynomial σ k} (hb : eval P b ≠ 0) :
    algebraMap _ (functionField I) (Ideal.Quotient.mk I b) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  exact fun h => hb (by simpa using congrArg (coordinateEval P hI) h)

/-- A rational function lies in `𝒪_P(V)` iff it is a quotient `a / b` of polynomials with
`b(P) ≠ 0`. -/
theorem mem_localSubring_iff {f : functionField I} :
    f ∈ (localSubring P hI).toSubring ↔ ∃ a b : MvPolynomial σ k, eval P b ≠ 0 ∧
      f = algebraMap _ _ (Ideal.Quotient.mk I a) / algebraMap _ _ (Ideal.Quotient.mk I b) := by
  rw [localSubring_def, LocalSubring.ofPrime, LocalSubring.range_toSubring]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨⟨_, a, rfl⟩, ⟨⟨_, b, rfl⟩, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (RingHom.ker (rangeEval P hI)).primeCompl y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb : eval P b ≠ 0 := by
      simpa [Ideal.primeCompl, RingHom.mem_ker] using
        (rangeEval_rangeRestrict P hI (Ideal.Quotient.mk I b)).symm.trans_ne hb
    refine ⟨a, b, hb, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    exact (mul_div_cancel₀ _ (algebraMap_mk_ne_zero hI hb)).symm
  · rintro ⟨a, b, hb, rfl⟩
    refine ⟨IsLocalization.mk' _ ((algebraMap _ (functionField I)).rangeRestrict
      (Ideal.Quotient.mk I a)) (⟨(algebraMap _ (functionField I)).rangeRestrict
      (Ideal.Quotient.mk I b), ?_⟩ : (RingHom.ker (rangeEval P hI)).primeCompl), ?_⟩
    · simpa [Ideal.primeCompl, RingHom.mem_ker, rangeEval_rangeRestrict] using hb
    · rw [IsLocalization.lift_mk'_spec]
      exact (mul_div_cancel₀ _ (algebraMap_mk_ne_zero hI hb)).symm

theorem algebraMap_mem_localSubring (a : MvPolynomial σ k ⧸ I) :
    algebraMap _ (functionField I) a ∈ (localSubring P hI).toSubring :=
  LocalSubring.le_ofPrime _ _ ⟨a, rfl⟩

/-- `𝒪_P(V)` is a `Γ(V)`-algebra, by the inclusion `Γ(V) ⊆ 𝒪_P(V)` in `k(V)`. -/
noncomputable instance : Algebra (MvPolynomial σ k ⧸ I) (localSubring P hI).toSubring :=
  ((algebraMap _ (functionField I)).codRestrict _
    (algebraMap_mem_localSubring P hI)).toAlgebra

@[simp]
theorem coe_algebraMap_localSubring (a : MvPolynomial σ k ⧸ I) :
    (algebraMap _ (localSubring P hI).toSubring a : functionField I) =
      algebraMap _ (functionField I) a :=
  (rfl)

instance : IsScalarTower (MvPolynomial σ k ⧸ I) (localSubring P hI).toSubring
    (functionField I) :=
  .of_algebraMap_eq fun _ => rfl

/-- `𝒪_P(V)` is a `k`-algebra. -/
noncomputable instance : Algebra k (localSubring P hI).toSubring :=
  ((algebraMap (MvPolynomial σ k ⧸ I) (localSubring P hI).toSubring).comp
    (algebraMap k _)).toAlgebra

instance : IsScalarTower k (MvPolynomial σ k ⧸ I) (localSubring P hI).toSubring :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := MvPolynomial σ k ⧸ I) fun _ => rfl

instance : (RingHom.ker (coordinateEval P hI)).IsPrime := RingHom.ker_isPrime _

omit [I.IsPrime] in
theorem mk_mem_primeCompl_iff {b : MvPolynomial σ k} :
    Ideal.Quotient.mk I b ∈ (RingHom.ker (coordinateEval P hI)).primeCompl ↔ eval P b ≠ 0 := by
  simp [Ideal.primeCompl, RingHom.mem_ker]

/-- `𝒪_P(V)` is the localization of `Γ(V)` at the ideal of `P`. -/
instance : IsLocalization.AtPrime (localSubring P hI).toSubring
    (RingHom.ker (coordinateEval P hI)) := by
  refine (isLocalization_iff _ _).2 ⟨fun ⟨s, hs⟩ => ?_, fun ⟨f, hf⟩ => ?_,
    fun {x y} h => ⟨1, ?_⟩⟩
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hb := (mk_mem_primeCompl_iff P hI).1 hs
    refine IsUnit.of_mul_eq_one ⟨_, (mem_localSubring_iff P hI).2 ⟨1, b, hb, rfl⟩⟩
      (Subtype.ext ?_)
    simpa using mul_inv_cancel₀ (algebraMap_mk_ne_zero hI hb)
  · obtain ⟨a, b, hb, rfl⟩ := (mem_localSubring_iff P hI).1 hf
    exact ⟨⟨Ideal.Quotient.mk I a, _, (mk_mem_primeCompl_iff P hI).2 hb⟩,
      Subtype.ext (div_mul_cancel₀ _ (algebraMap_mk_ne_zero hI hb))⟩
  · simpa using IsFractionRing.injective _ (functionField I) (congrArg Subtype.val h)

/-- **`𝒪_P(V)` is the localization `Γ(V)_{𝔪_P}`.** -/
noncomputable def localizationAlgEquiv :
    Localization.AtPrime (RingHom.ker (coordinateEval P hI)) ≃ₐ[MvPolynomial σ k ⧸ I]
      (localSubring P hI).toSubring :=
  IsLocalization.algEquiv (RingHom.ker (coordinateEval P hI)).primeCompl _ _

theorem localizationAlgEquiv_def : localizationAlgEquiv P hI =
    IsLocalization.algEquiv (RingHom.ker (coordinateEval P hI)).primeCompl _ _ :=
  (rfl)

/-! ### The value map of `𝒪_P(V)` -/

/-- The value `f(P)` of a rational function `f ∈ 𝒪_P(V)`, as a `k`-algebra map to `k`. -/
noncomputable def evalAt : (localSubring P hI).toSubring →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := (RingHom.ker (coordinateEval P hI)).primeCompl)
    (f := coordinateEval P hI) fun y => isUnit_iff_ne_zero.2 fun h => y.2 h

theorem evalAt_def : evalAt P hI =
    IsLocalization.liftAlgHom (M := (RingHom.ker (coordinateEval P hI)).primeCompl)
      (f := coordinateEval P hI) fun y => isUnit_iff_ne_zero.2 fun h => y.2 h :=
  (rfl)

@[simp]
theorem evalAt_algebraMap (a : MvPolynomial σ k ⧸ I) :
    evalAt P hI (algebraMap _ _ a) = coordinateEval P hI a := by
  rw [evalAt_def, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- The value of `a / b ∈ 𝒪_P(V)` is `a(P) / b(P)`. -/
theorem evalAt_eq_div {f : (localSubring P hI).toSubring} {a b : MvPolynomial σ k}
    (hb : eval P b ≠ 0)
    (hf : (f : functionField I) =
      algebraMap _ _ (Ideal.Quotient.mk I a) / algebraMap _ _ (Ideal.Quotient.mk I b)) :
    evalAt P hI f = eval P a / eval P b := by
  have : f * algebraMap _ _ (Ideal.Quotient.mk I b) = algebraMap _ _ (Ideal.Quotient.mk I a) :=
    Subtype.ext (by simp [hf, div_mul_cancel₀ _ (algebraMap_mk_ne_zero hI hb)])
  rw [eq_div_iff hb, ← coordinateEval_mk P hI, ← coordinateEval_mk P hI, ← evalAt_algebraMap,
    ← evalAt_algebraMap, ← map_mul, this]

theorem evalAt_surjective : Function.Surjective (evalAt P hI) :=
  fun c => ⟨algebraMap _ _ (Ideal.Quotient.mk I (C c)), by simp⟩

/-- An element of `𝒪_P(V)` is a unit iff its value at `P` is not zero. -/
theorem isUnit_iff_evalAt_ne_zero {f : (localSubring P hI).toSubring} :
    IsUnit f ↔ evalAt P hI f ≠ 0 := by
  refine ⟨fun h => (h.map (evalAt P hI)).ne_zero, fun h => ?_⟩
  obtain ⟨a, b, hb, hf⟩ := (mem_localSubring_iff P hI).1 f.2
  have ha : eval P a ≠ 0 := by
    rw [evalAt_eq_div P hI hb hf] at h
    exact fun ha => h (by rw [ha, zero_div])
  refine IsUnit.of_mul_eq_one ⟨_, (mem_localSubring_iff P hI).2 ⟨b, a, ha, rfl⟩⟩
    (Subtype.ext ?_)
  simp only [Subring.coe_mul, hf, Subring.coe_one]
  have h1 := algebraMap_mk_ne_zero hI hb
  have h2 := algebraMap_mk_ne_zero hI ha
  field_simp

/-- The kernel of the value map `𝒪_P(V) → k` is the maximal ideal: `𝒪_P(V)` is local, and its
maximal ideal `𝔪_P(V)` consists of the functions vanishing at `P`. -/
theorem ker_evalAt :
    RingHom.ker (evalAt P hI) = maximalIdeal (localSubring P hI).toSubring := by
  ext f
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_evalAt_ne_zero, not_not]

/-- The residue field of `𝒪_P(V)` is `k`, by the value map. -/
noncomputable def residueFieldAlgEquiv : ResidueField (localSubring P hI).toSubring ≃ₐ[k] k :=
  (quotientEquivAlgOfEq k (ker_evalAt P hI).symm).trans
    (quotientKerAlgEquivOfSurjective (evalAt_surjective P hI))

theorem residueFieldAlgEquiv_def : residueFieldAlgEquiv P hI =
    (quotientEquivAlgOfEq k (ker_evalAt P hI).symm).trans
      (quotientKerAlgEquivOfSurjective (evalAt_surjective P hI)) :=
  (rfl)

@[simp]
theorem residueFieldAlgEquiv_residue (f : (localSubring P hI).toSubring) :
    residueFieldAlgEquiv P hI (residue _ f) = evalAt P hI f :=
  quotientKerAlgEquivOfSurjective_mk (evalAt_surjective P hI) f

/-- `𝒪_P(V)` is Noetherian. -/
instance [Finite σ] : IsNoetherianRing (localSubring P hI).toSubring :=
  IsLocalization.isNoetherianRing (RingHom.ker (coordinateEval P hI)).primeCompl _
    inferInstance

/-! ### Comparison with `𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)` -/

omit [I.IsPrime] in
theorem primeCompl_ker_coordinateEval :
    (RingHom.ker (coordinateEval P hI)).primeCompl =
      haveI := isPrime_map_quotientMk_of_isPrime hI
      ((vanishingIdeal k {P}).map (Ideal.Quotient.mk I)).primeCompl := by
  ext
  simp [Ideal.primeCompl, ker_coordinateEval P hI]

instance : IsLocalization (RingHom.ker (coordinateEval P hI)).primeCompl
    (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) :=
  haveI := isPrime_map_quotientMk_of_isPrime hI
  primeCompl_ker_coordinateEval P hI ▸
    Localization.AtPrime.isLocalization_quotient I (vanishingIdeal k {P}) hI

/-- The isomorphism `𝒪_P(V) ≅ 𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)` of `Γ(V)`-algebras. -/
noncomputable def quotientEquiv :
    (localSubring P hI).toSubring ≃ₐ[MvPolynomial σ k ⧸ I]
      localRing k P ⧸ I.map (algebraMap _ (localRing k P)) :=
  IsLocalization.algEquiv (RingHom.ker (coordinateEval P hI)).primeCompl
    (localSubring P hI).toSubring (localRing k P ⧸ I.map (algebraMap _ (localRing k P)))

theorem quotientEquiv_def : quotientEquiv P hI =
    IsLocalization.algEquiv (RingHom.ker (coordinateEval P hI)).primeCompl
      (localSubring P hI).toSubring (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) :=
  (rfl)

/-- The local ring `𝒪_P(V) ⊆ k(V)` is isomorphic to the quotient `𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)` by the
natural map. -/
noncomputable def quotientAlgEquiv :
    (localSubring P hI).toSubring ≃ₐ[k] localRing k P ⧸ I.map (algebraMap _ (localRing k P)) :=
  AlgEquiv.ofRingEquiv (f := (quotientEquiv P hI).toRingEquiv) fun c => by
    change quotientEquiv P hI (algebraMap _ _ (Ideal.Quotient.mk I (C c))) = _
    rw [AlgEquiv.commutes, Ideal.Quotient.algebraMap_quotient_map_quotient]
    rfl

theorem quotientAlgEquiv_def : quotientAlgEquiv P hI =
    AlgEquiv.ofRingEquiv (f := (quotientEquiv P hI).toRingEquiv) fun c => by
      change quotientEquiv P hI (algebraMap _ _ (Ideal.Quotient.mk I (C c))) = _
      rw [AlgEquiv.commutes, Ideal.Quotient.algebraMap_quotient_map_quotient]
      rfl :=
  (rfl)

@[simp]
theorem quotientAlgEquiv_algebraMap (f : MvPolynomial σ k) :
    quotientAlgEquiv P hI (algebraMap _ _ (Ideal.Quotient.mk I f)) =
      Ideal.Quotient.mk _ (algebraMap _ (localRing k P) f) :=
  ((quotientEquiv P hI).commutes _).trans (Ideal.Quotient.algebraMap_quotient_map_quotient _)

@[simp]
theorem quotientAlgEquiv_symm_mk (f : MvPolynomial σ k) :
    (quotientAlgEquiv P hI).symm (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) f)) =
      algebraMap _ _ (Ideal.Quotient.mk I f) := by
  rw [AlgEquiv.symm_apply_eq, quotientAlgEquiv_algebraMap]

/-- Two ring maps out of `𝒪_P(V)` that agree on `Γ(V)` are equal. -/
theorem ringHom_ext {R : Type*} [Semiring R] {φ φ' : (localSubring P hI).toSubring →+* R}
    (h : ∀ f : MvPolynomial σ k, φ (algebraMap _ _ (Ideal.Quotient.mk I f)) =
      φ' (algebraMap _ _ (Ideal.Quotient.mk I f))) : φ = φ' :=
  IsLocalization.ringHom_ext (RingHom.ker (coordinateEval P hI)).primeCompl <|
    Ideal.Quotient.ringHom_ext (RingHom.ext h)

/-! ### Polynomial maps -/

section map

variable {τ : Type*} {J : Ideal (MvPolynomial τ k)} [J.IsPrime] {Q : τ → k}
  (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (h : ∀ g, eval P (ψ g) = eval Q g)
  (hJI : J ≤ I.comap ψ)

/-- The local homomorphism `𝒪_Q(W) → 𝒪_P(V)` induced by a polynomial map `V → W` sending `P` to
`Q`, for `V = V(I)` and `W = V(J)`: it is given by `ψ : k[Y] → k[X]` with `(ψ g)(P) = g(Q)` and
`J ≤ ψ⁻¹(I)`. -/
noncomputable def map :
    (localSubring Q (localRing.le_vanishingIdeal_of_le_comap ψ h hJI hI)).toSubring →ₐ[k]
      (localSubring P hI).toSubring :=
  (quotientAlgEquiv P hI).symm.toAlgHom.comp ((localRing.quotientMap ψ h hJI).comp
    (quotientAlgEquiv Q (localRing.le_vanishingIdeal_of_le_comap ψ h hJI hI)).toAlgHom)

theorem map_def : map P hI ψ h hJI =
    (quotientAlgEquiv P hI).symm.toAlgHom.comp ((localRing.quotientMap ψ h hJI).comp
      (quotientAlgEquiv Q (localRing.le_vanishingIdeal_of_le_comap ψ h hJI hI)).toAlgHom) :=
  (rfl)

@[simp]
theorem map_algebraMap (g : MvPolynomial τ k) :
    map P hI ψ h hJI (algebraMap _ _ (Ideal.Quotient.mk J g)) =
      algebraMap _ _ (Ideal.Quotient.mk I (ψ g)) := by
  change (quotientAlgEquiv P hI).symm (localRing.quotientMap ψ h hJI
    (quotientAlgEquiv Q _ (algebraMap _ _ (Ideal.Quotient.mk J g)))) = _
  rw [quotientAlgEquiv_algebraMap, localRing.quotientMap_mk, localRing.map_algebraMap,
    quotientAlgEquiv_symm_mk]

/-- The map induced by a polynomial map respects values: `(φ̃ f)(P) = f(Q)`. -/
@[simp]
theorem evalAt_map (f) : evalAt P hI (map P hI ψ h hJI f) = evalAt Q _ f := by
  have := ringHom_ext Q (localRing.le_vanishingIdeal_of_le_comap ψ h hJI hI)
    (φ := (evalAt P hI).toRingHom.comp (map P hI ψ h hJI).toRingHom)
    (φ' := (evalAt Q _).toRingHom) fun g => by simp [h]
  exact RingHom.congr_fun this f

instance isLocalHom_map : IsLocalHom (map P hI ψ h hJI) :=
  ⟨fun f hf => by
    rw [isUnit_iff_evalAt_ne_zero, evalAt_map] at hf
    exact (isUnit_iff_evalAt_ne_zero _ _).2 hf⟩

/-- The map induced by a polynomial map is the unique ring map `𝒪_Q(W) → 𝒪_P(V)` extending the
map `Γ(W) → Γ(V)`. -/
theorem map_unique
    (φ : (localSubring Q (localRing.le_vanishingIdeal_of_le_comap ψ h hJI hI)).toSubring →+*
      (localSubring P hI).toSubring)
    (hφ : ∀ g, φ (algebraMap _ _ (Ideal.Quotient.mk J g)) =
      algebraMap _ _ (Ideal.Quotient.mk I (ψ g))) :
    φ = (map P hI ψ h hJI).toRingHom :=
  ringHom_ext _ _ fun g => (hφ g).trans (map_algebraMap P hI ψ h hJI g).symm

end map

section mapEquiv

variable {τ : Type*} {J : Ideal (MvPolynomial τ k)} [J.IsPrime] {Q : τ → k}

omit [I.IsPrime] [J.IsPrime] in
include hI in
/-- If `I = ψ(J)` for a polynomial isomorphism `ψ` sending `P` to `Q`, and `P ∈ V(I)`, then
`Q ∈ V(J)`. -/
theorem le_vanishingIdeal_of_eq_map (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) (hJI : I = J.map ψ) : J ≤ vanishingIdeal k {Q} :=
  localRing.le_vanishingIdeal_of_le_comap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) h
    (hJI ▸ le_comap_map) hI

variable (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) (h : ∀ g, eval P (ψ g) = eval Q g)
  (hJI : I = J.map ψ)

/-- The isomorphism `𝒪_Q(W) ≅ 𝒪_P(V)` induced by a polynomial isomorphism sending `P` to `Q`
and `V = V(I)` onto `W = V(J)`: it is given by `ψ : k[Y] ≃ k[X]` with `(ψ g)(P) = g(Q)` and
`I = ψ(J)`. For an affine change of coordinates `T` this is `𝒪_Q(V) ≅ 𝒪_P(V^T)`. -/
noncomputable def mapEquiv :
    (localSubring Q (le_vanishingIdeal_of_eq_map P hI ψ h hJI)).toSubring ≃ₐ[k]
      (localSubring P hI).toSubring :=
  (quotientAlgEquiv Q _).trans
    ((localRing.quotientMapEquiv ψ h hJI).trans (quotientAlgEquiv P hI).symm)

theorem mapEquiv_def : mapEquiv P hI ψ h hJI = (quotientAlgEquiv Q _).trans
    ((localRing.quotientMapEquiv ψ h hJI).trans (quotientAlgEquiv P hI).symm) :=
  (rfl)

@[simp]
theorem mapEquiv_algebraMap (g : MvPolynomial τ k) :
    mapEquiv P hI ψ h hJI (algebraMap _ _ (Ideal.Quotient.mk J g)) =
      algebraMap _ _ (Ideal.Quotient.mk I (ψ g)) := by
  rw [mapEquiv_def, AlgEquiv.trans_apply, AlgEquiv.trans_apply, quotientAlgEquiv_algebraMap,
    localRing.quotientMapEquiv_mk, localRing.mapEquiv_algebraMap, quotientAlgEquiv_symm_mk]

end mapEquiv

/-! ### Poles -/

section poles

variable (I) in
/-- The ideal of denominators `J_f = {G ∈ k[X] : G f ∈ Γ(V)}` of a rational function
`f ∈ k(V)`. -/
def denominatorIdeal (f : functionField I) : Ideal (MvPolynomial σ k) where
  carrier := {g | algebraMap _ _ (Ideal.Quotient.mk I g) * f ∈
    (algebraMap (MvPolynomial σ k ⧸ I) (functionField I)).range}
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by simp [hx, hy, add_mul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨x, hx⟩
    exact ⟨Ideal.Quotient.mk I c * x, by simp [hx, mul_assoc]⟩

omit [I.IsPrime] in
theorem mem_denominatorIdeal_iff {f : functionField I} {g : MvPolynomial σ k} :
    g ∈ denominatorIdeal I f ↔ ∃ a : MvPolynomial σ k ⧸ I,
      algebraMap _ _ a = algebraMap _ (functionField I) (Ideal.Quotient.mk I g) * f :=
  Iff.rfl

omit [I.IsPrime] in
theorem le_denominatorIdeal (f : functionField I) : I ≤ denominatorIdeal I f :=
  fun g hg => ⟨0, by simp [Ideal.Quotient.eq_zero_iff_mem.2 hg]⟩

/-- A rational function lies in `𝒪_P(V)` iff `P` is not a zero of its ideal of denominators. -/
theorem mem_localSubring_iff_notMem_zeroLocus {f : functionField I} :
    f ∈ (localSubring P hI).toSubring ↔ P ∉ zeroLocus k (denominatorIdeal I f) := by
  rw [mem_localSubring_iff, mem_zeroLocus_iff]
  simp only [not_forall, exists_prop]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    refine ⟨b, ⟨Ideal.Quotient.mk I a, ?_⟩, hb⟩
    rw [mul_div_cancel₀ _ (algebraMap_mk_ne_zero hI hb)]
  · rintro ⟨b, ⟨a, ha⟩, hb⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨a, b, hb, by rw [ha, mul_div_cancel_left₀ _ (algebraMap_mk_ne_zero hI hb)]⟩

variable (I) in
/-- The pole set of a rational function `f ∈ k(V)`: the points `P ∈ V` with `f ∉ 𝒪_P(V)`. -/
def poleSet (f : functionField I) : Set (σ → k) :=
  {P | ∃ hP : I ≤ vanishingIdeal k {P}, f ∉ (localSubring P hP).toSubring}

theorem poleSet_def (f : functionField I) : poleSet I f =
    {P | ∃ hP : I ≤ vanishingIdeal k {P}, f ∉ (localSubring P hP).toSubring} :=
  (rfl)

/-- **The pole set of a rational function is algebraic**: it is the zero set of the ideal of
denominators. -/
theorem poleSet_eq_zeroLocus (f : functionField I) :
    poleSet I f = zeroLocus k (denominatorIdeal I f) := by
  ext Q
  refine ⟨fun ⟨hQ, hf⟩ => not_not.1 fun h => hf ((mem_localSubring_iff_notMem_zeroLocus Q hQ).2 h),
    fun h => ?_⟩
  have hQ : I ≤ vanishingIdeal k {Q} := le_vanishingIdeal_singleton_iff.2
    (zeroLocus_anti_mono (le_denominatorIdeal f) h)
  exact ⟨hQ, fun hf => (mem_localSubring_iff_notMem_zeroLocus Q hQ).1 hf h⟩

/-- **`Γ(V)` is the intersection of the local rings `𝒪_P(V)`**, over an algebraically closed
field: a rational function regular at every point of `V` is a polynomial function. -/
theorem mem_range_algebraMap_iff [IsAlgClosed k] [Finite σ] {f : functionField I} :
    f ∈ (algebraMap (MvPolynomial σ k ⧸ I) (functionField I)).range ↔
      ∀ (Q : σ → k) (hQ : I ≤ vanishingIdeal k {Q}), f ∈ (localSubring Q hQ).toSubring := by
  refine ⟨fun ⟨a, ha⟩ Q hQ => ha ▸ algebraMap_mem_localSubring Q hQ a, fun h => ?_⟩
  have hempty : zeroLocus k (denominatorIdeal I f) = ∅ := by
    rw [← poleSet_eq_zeroLocus, Set.eq_empty_iff_forall_notMem]
    exact fun Q ⟨hQ, hf⟩ => hf (h Q hQ)
  have h1 : (1 : MvPolynomial σ k) ∈ denominatorIdeal I f := by
    have := vanishingIdeal_zeroLocus_eq_radical (K := k) (denominatorIdeal I f)
    rw [hempty, vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    exact this ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := h1
  exact ⟨a, by simpa using ha⟩

end poles

/-! ### Prime ideals -/

omit [I.IsPrime] in
theorem comap_ker_coordinateEval :
    (RingHom.ker (coordinateEval P hI)).comap (Ideal.Quotient.mk I) = vanishingIdeal k {P} := by
  ext f
  simp [RingHom.mem_ker]

/-- **Prime ideals of `𝒪_P(V)` correspond to subvarieties of `V` through `P`**: the prime ideals
of `𝒪_P(V)` are in order-preserving bijection with the prime ideals `J` of `k[X]` with
`I ≤ J ≤ I_P`. -/
noncomputable def primesOrderIso :
    {p : Ideal (localSubring P hI).toSubring // p.IsPrime} ≃o
      {J : Ideal (MvPolynomial σ k) // J.IsPrime ∧ I ≤ J ∧ J ≤ vanishingIdeal k {P}} :=
  (IsLocalization.AtPrime.orderIsoOfPrime _ (RingHom.ker (coordinateEval P hI))).trans
    { toFun q := ⟨q.1.comap (Ideal.Quotient.mk I), comap_isPrime _ _ (H := q.2.1),
        fun x hx => by simp [Ideal.Quotient.eq_zero_iff_mem.2 hx],
        (comap_mono q.2.2).trans (comap_ker_coordinateEval P hI).le⟩
      invFun J := ⟨J.1.map (Ideal.Quotient.mk I),
        map_isPrime_of_surjective Ideal.Quotient.mk_surjective (H := J.2.1)
          (by rw [Ideal.mk_ker]; exact J.2.2.1),
        map_le_iff_le_comap.2 (J.2.2.2.trans (comap_ker_coordinateEval P hI).ge)⟩
      left_inv q := Subtype.ext (map_comap_of_surjective _ Ideal.Quotient.mk_surjective _)
      right_inv J := Subtype.ext <| by
        simp only
        rw [comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
          sup_eq_left.2 J.2.2.1]
      map_rel_iff' {q q'} := comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _ }

@[simp]
theorem coe_primesOrderIso_apply (p : {p : Ideal (localSubring P hI).toSubring // p.IsPrime}) :
    (primesOrderIso P hI p : Ideal (MvPolynomial σ k)) =
      (p.1.comap (algebraMap (MvPolynomial σ k ⧸ I) _)).comap (Ideal.Quotient.mk I) :=
  (rfl)

/-! ### The milestone -/

/-- **The local ring of an affine variety at a point.** Let `k` be algebraically closed,
`V = V(I) ⊆ 𝔸ⁿ` the variety of a prime ideal `I`, `P ∈ V`, and `𝔪_P` the ideal of the
functions in `Γ(V) = k[X] ⧸ I` that vanish at `P`. Then:

* (a) `𝒪_P(V) = {a / b : b(P) ≠ 0}` is a subring of `k(V)` containing `Γ(V)`, and it is the
  localization `Γ(V)_{𝔪_P}`;
* (b) the value map `f ↦ f(P)` is a surjective `k`-algebra map `𝒪_P(V) → k` whose kernel is the
  maximal ideal, so the residue field of `𝒪_P(V)` is `k`;
* (c) `𝒪_P(V)` is a Noetherian local domain;
* (d) the pole set of every `f ∈ k(V)` is the algebraic set of its ideal of denominators, and
  `Γ(V)` is the intersection of the `𝒪_Q(V)`, `Q ∈ V`;
* (e) a polynomial map `V → W` sending `P` to `Q`, given by `ψ : k[Y] → k[X]`, induces a unique
  ring map `𝒪_Q(W) → 𝒪_P(V)` extending `Γ(W) → Γ(V)`, and it is local; a polynomial isomorphism
  with `I = ψ(J)`, such as an affine change of coordinates, induces an isomorphism
  `𝒪_Q(W) ≅ 𝒪_P(V)`;
* (f) the prime ideals of `𝒪_P(V)` correspond, preserving order, to the prime ideals `J` of
  `k[X]` with `I ≤ J ≤ I_P`, that is, to the subvarieties of `V` through `P`.

Milestone: *Local ring of an affine variety at a point*. -/
theorem localSubring_spec [IsAlgClosed k] [Finite σ] :
    ((∀ f : functionField I, f ∈ (localSubring P hI).toSubring ↔
        ∃ a b : MvPolynomial σ k, eval P b ≠ 0 ∧
          f = algebraMap _ _ (Ideal.Quotient.mk I a) / algebraMap _ _ (Ideal.Quotient.mk I b)) ∧
      (algebraMap (MvPolynomial σ k ⧸ I) (functionField I)).range ≤
        (localSubring P hI).toSubring ∧
      IsLocalization.AtPrime (localSubring P hI).toSubring (RingHom.ker (coordinateEval P hI))) ∧
    (Function.Surjective (evalAt P hI) ∧
      RingHom.ker (evalAt P hI) = maximalIdeal (localSubring P hI).toSubring ∧
      Nonempty (ResidueField (localSubring P hI).toSubring ≃ₐ[k] k)) ∧
    (IsNoetherianRing (localSubring P hI).toSubring ∧ IsDomain (localSubring P hI).toSubring ∧
      IsLocalRing (localSubring P hI).toSubring) ∧
    ((∀ f : functionField I, poleSet I f = zeroLocus k (denominatorIdeal I f)) ∧
      ∀ f : functionField I, f ∈ (algebraMap (MvPolynomial σ k ⧸ I) (functionField I)).range ↔
        ∀ (Q : σ → k) (hQ : I ≤ vanishingIdeal k {Q}), f ∈ (localSubring Q hQ).toSubring) ∧
    ((∀ {τ : Type*} {J : Ideal (MvPolynomial τ k)} [J.IsPrime] {Q : τ → k}
        (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (h : ∀ g, eval P (ψ g) = eval Q g)
        (hJI : J ≤ I.comap ψ),
        ∃! φ : (localSubring Q (localRing.le_vanishingIdeal_of_le_comap ψ h hJI hI)).toSubring →+*
          (localSubring P hI).toSubring,
          (∀ g, φ (algebraMap _ _ (Ideal.Quotient.mk J g)) =
            algebraMap _ _ (Ideal.Quotient.mk I (ψ g))) ∧ IsLocalHom φ) ∧
      ∀ {τ : Type*} {J : Ideal (MvPolynomial τ k)} [J.IsPrime] {Q : τ → k}
        (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) (h : ∀ g, eval P (ψ g) = eval Q g)
        (hJI : I = J.map ψ),
        ∃ e : (localSubring Q (le_vanishingIdeal_of_eq_map P hI ψ h hJI)).toSubring ≃ₐ[k]
          (localSubring P hI).toSubring,
          ∀ g, e (algebraMap _ _ (Ideal.Quotient.mk J g)) =
            algebraMap _ _ (Ideal.Quotient.mk I (ψ g))) ∧
    Nonempty ({p : Ideal (localSubring P hI).toSubring // p.IsPrime} ≃o
      {J : Ideal (MvPolynomial σ k) // J.IsPrime ∧ I ≤ J ∧ J ≤ vanishingIdeal k {P}}) :=
  ⟨⟨fun _ => mem_localSubring_iff P hI, fun _ ⟨a, ha⟩ => ha ▸ algebraMap_mem_localSubring P hI a,
      inferInstance⟩,
    ⟨evalAt_surjective P hI, ker_evalAt P hI, ⟨residueFieldAlgEquiv P hI⟩⟩,
    ⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨poleSet_eq_zeroLocus, fun _ => mem_range_algebraMap_iff⟩,
    ⟨fun ψ h hJI => ⟨(map P hI ψ h hJI).toRingHom,
        ⟨map_algebraMap P hI ψ h hJI, ⟨(isLocalHom_map P hI ψ h hJI).map_nonunit⟩⟩,
        fun φ hφ => map_unique P hI ψ h hJI φ hφ.1⟩,
      fun ψ h hJI => ⟨mapEquiv P hI ψ h hJI, mapEquiv_algebraMap P hI ψ h hJI⟩⟩,
    ⟨primesOrderIso P hI⟩⟩

end PlaneCurves.AffineSpace

end
