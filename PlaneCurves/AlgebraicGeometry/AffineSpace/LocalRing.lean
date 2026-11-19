/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.MvPolynomial.LocalOrder
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst
public import PlaneCurves.RingTheory.Localization.Quotient
public import PlaneCurves.RingTheory.MvPolynomial.Taylor

/-!
# The local ring of affine space at a point

For a field `k` and a point `P ∈ kⁿ`, the local ring `𝒪_P(𝔸ⁿ)` is the localization of the
polynomial ring `k[X₁, …, Xₙ]` at the ideal `I_P` of `P`. This file defines it, with its value
map `𝒪_P(𝔸ⁿ) → k`, and describes its maximal ideal, its powers and its quotients.

## Main definitions

* `PlaneCurves.AffineSpace.localRing k P`: the local ring `𝒪_P(𝔸ⁿ)`.
* `PlaneCurves.AffineSpace.localRing.evalAt`: the value `f ↦ f(P)`, a `k`-algebra map to `k`.
* `PlaneCurves.AffineSpace.localRing.residueFieldAlgEquiv`: the residue field is `k`.
* `PlaneCurves.AffineSpace.localRing.map`, `PlaneCurves.AffineSpace.localRing.mapEquiv`: the
  local homomorphisms induced by polynomial maps, and the isomorphisms induced by the Taylor
  shift (`localRing.taylorEquiv`) and by invertible linear substitutions
  (`localRing.linearSubstEquiv`).
* `PlaneCurves.AffineSpace.localRing.quotientPowAlgEquiv`: `k[X] ⧸ I_P ^ r ≅ 𝒪_P ⧸ 𝔪 ^ r`.
* `PlaneCurves.AffineSpace.localRing.quotientEvalAt`,
  `PlaneCurves.AffineSpace.localRing.quotientResidueFieldAlgEquiv`: the value map of the local
  ring `𝒪_P(V) = 𝒪_P ⧸ I 𝒪_P` of `V = V(I) ∋ P`, and its residue field `k`.
* `PlaneCurves.AffineSpace.localRing.quotientMap`,
  `PlaneCurves.AffineSpace.localRing.quotientMapEquiv`: the local homomorphism `𝒪_Q(W) → 𝒪_P(V)`
  induced by a polynomial map `V → W` sending `P` to `Q`, and the isomorphisms
  `𝒪_Q(V) ≅ 𝒪_P(V^T)` induced by the Taylor shift (`localRing.quotientTaylorEquiv`) and by
  invertible linear substitutions (`localRing.quotientLinearSubstEquiv`).
* `PlaneCurves.AffineSpace.localRing.ofAway`: the map `k[X][1/h] → 𝒪_P(𝔸ⁿ)` for `h(P) ≠ 0`;
  `PlaneCurves.AffineSpace.localRing.mapOfAway`: the map `𝒪_P(𝔸ⁿ) → 𝒪_Q(𝔸ᵐ)` induced by a
  `k`-algebra map `k[X][1/h] → k[Y][1/h']` compatible with the values at `P` and `Q`.
* `PlaneCurves.AffineSpace.localRingEquivOfAway`: the isomorphism `𝒪_P(𝔸ⁿ) ≅ 𝒪_Q(𝔸ᵐ)` induced
  by such an isomorphism `k[X][1/h] ≅ k[Y][1/h']`, and
  `PlaneCurves.AffineSpace.quotientEquivOfAway`: the isomorphism
  `𝒪_P(𝔸ⁿ) ⧸ (f) ≅ 𝒪_Q(𝔸ᵐ) ⧸ (g)` when it sends `f` to a unit times `g`.

## Main results

* `PlaneCurves.AffineSpace.localRing.ker_evalAt`: the kernel of the value map is the maximal
  ideal.
* `PlaneCurves.AffineSpace.localRing.isUnit_algebraMap_iff`: a polynomial is a unit in `𝒪_P`
  iff it does not vanish at `P`.
* `PlaneCurves.AffineSpace.localRing.ringKrullDim_eq`: `𝒪_P(𝔸ⁿ)` is a regular local ring of
  dimension `n`.
* `PlaneCurves.AffineSpace.localRing.algebraMap_mem_maximalIdeal_pow_iff`: a polynomial lies in
  `𝔪 ^ r` iff its order at `P` is at least `r`; `localRing.algebraMap_mem_maximalIdeal_iff`: it
  lies in `𝔪` iff it vanishes at `P`.
* `PlaneCurves.AffineSpace.localRing.bijective_quotientMap_sup_maximalIdeal_pow`,
  `PlaneCurves.AffineSpace.localRing.length_quotient_map_sup_maximalIdeal_pow`: for an ideal `J`
  of `k[X]`, the natural map `k[X] ⧸ (J + I_P ^ r) → 𝒪_P ⧸ (J 𝒪_P + 𝔪 ^ r)` is bijective, so the
  two have the same length over `k`.
* `PlaneCurves.AffineSpace.localRing.quotient_iso`: local rings of subvarieties are quotients
  of the local ring of affine space. For ideals `I ≤ J ≤ I_P` it gives
  `𝒪_P ⧸ J 𝒪_P ≅ 𝒪_P(k[X] ⧸ I) ⧸ J' 𝒪_P(k[X] ⧸ I)`, from
  `Localization.AtPrime.quotientMapAlgEquiv`.
* `PlaneCurves.AffineSpace.localRing.isDomain_quotient`: the local ring of a variety is a domain.
* `PlaneCurves.AffineSpace.localRing.isLocalRing_quotient_span_singleton`: for `F(P) = 0`,
  `𝒪_P(𝔸ⁿ) ⧸ (F)` is a local ring; `localRing.mk_mem_map_maximalIdeal_iff` and
  `localRing.mk_mem_map_maximalIdeal_pow_iff` describe its maximal ideal and, for `r ≤ m_P(F)`,
  its `r`-th power.
* `PlaneCurves.AffineSpace.localRing.ker_quotientEvalAt`: the kernel of the value map of
  `𝒪_P(V)` is its maximal ideal.
* `PlaneCurves.AffineSpace.localRing.isLocalHom_quotientMap`,
  `PlaneCurves.AffineSpace.localRing.quotientMap_unique`: the map induced by a polynomial map is
  local, and is the unique `k`-algebra map extending it.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.4, §2.8, Problems 2.21, 2.22, 2.43, 2.44
-/

public section

open MvPolynomial IsLocalRing Ideal Matrix

namespace PlaneCurves.AffineSpace

variable (k : Type*) [Field k] {σ : Type*} (P : σ → k)

/-- The local ring `𝒪_P(𝔸ⁿ)` of affine space at a point `P ∈ kⁿ`: the polynomial ring
localized at the ideal of `P`. -/
abbrev localRing : Type _ :=
  Localization.AtPrime (vanishingIdeal k {P} : Ideal (MvPolynomial σ k))

namespace localRing

variable {k P}

/-- A polynomial is a unit in `𝒪_P(𝔸ⁿ)` iff it does not vanish at `P`. -/
@[simp]
theorem isUnit_algebraMap_iff {f : MvPolynomial σ k} :
    IsUnit (algebraMap _ (localRing k P) f) ↔ eval P f ≠ 0 := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (localRing k P) (vanishingIdeal k {P}),
    mem_primeCompl_iff, mem_vanishingIdeal_singleton_iff]
  simp

/-- An element of the complement of the ideal of `P` does not vanish at `P`. -/
theorem eval_ne_zero (s : (vanishingIdeal k {P}).primeCompl) : eval P s.1 ≠ 0 := by
  simpa using (mem_vanishingIdeal_singleton_iff P s.1).not.1 s.2

variable (k P)

/-- The value `f(P)` of an element `f` of `𝒪_P(𝔸ⁿ)`, as a `k`-algebra map to `k`. -/
noncomputable def evalAt : localRing k P →ₐ[k] k :=
  (IsLocalization.liftAlgHom (M := (vanishingIdeal k {P}).primeCompl)
    (f := aeval (R := k) P) fun s => by
      simpa [isUnit_iff_ne_zero] using
        (mem_vanishingIdeal_singleton_iff P s.1).not.1 s.2).restrictScalars k

theorem evalAt_def : evalAt k P =
    (IsLocalization.liftAlgHom (M := (vanishingIdeal k {P}).primeCompl)
      (f := aeval (R := k) P) fun s => by
        simpa [isUnit_iff_ne_zero] using
          (mem_vanishingIdeal_singleton_iff P s.1).not.1 s.2).restrictScalars k :=
  (rfl)

variable {k P}

@[simp]
theorem evalAt_algebraMap (f : MvPolynomial σ k) :
    evalAt k P (algebraMap _ _ f) = eval P f := by
  rw [evalAt_def, AlgHom.restrictScalars_apply, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  simp

@[simp]
theorem evalAt_mk' (f : MvPolynomial σ k) (s : (vanishingIdeal k {P}).primeCompl) :
    evalAt k P (IsLocalization.mk' _ f s) = eval P f / eval P s.1 := by
  rw [eq_div_iff (eval_ne_zero s), ← evalAt_algebraMap,
    ← evalAt_algebraMap, ← map_mul, IsLocalization.mk'_spec]

theorem evalAt_surjective : Function.Surjective (evalAt k P) :=
  fun a => ⟨algebraMap _ _ (C a), by rw [evalAt_algebraMap, eval_C]⟩

/-- The ideal of `P` generates the maximal ideal of `𝒪_P(𝔸ⁿ)`. -/
theorem map_vanishingIdeal :
    (vanishingIdeal k {P}).map (algebraMap _ (localRing k P)) = maximalIdeal (localRing k P) :=
  Localization.AtPrime.map_eq_maximalIdeal

/-- The powers of the ideal of `P` generate the powers of the maximal ideal of `𝒪_P(𝔸ⁿ)`. -/
theorem map_vanishingIdeal_pow (r : ℕ) :
    (vanishingIdeal k {P} ^ r).map (algebraMap _ (localRing k P)) =
      maximalIdeal (localRing k P) ^ r := by
  rw [Ideal.map_pow, map_vanishingIdeal]

/-- The kernel of the value map `𝒪_P(𝔸ⁿ) → k` is the maximal ideal. -/
theorem ker_evalAt : RingHom.ker (evalAt k P) = maximalIdeal (localRing k P) :=
  (IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective (evalAt k P) evalAt_surjective)).trans rfl

@[simp]
theorem evalAt_eq_zero_iff {f : localRing k P} :
    evalAt k P f = 0 ↔ f ∈ maximalIdeal (localRing k P) := by
  rw [← ker_evalAt, RingHom.mem_ker]

variable (k P)

/-- The residue field of `𝒪_P(𝔸ⁿ)` is `k`, by the value map. -/
noncomputable def residueFieldAlgEquiv : ResidueField (localRing k P) ≃ₐ[k] k :=
  (quotientEquivAlgOfEq k (ker_evalAt (k := k) (P := P)).symm).trans
    (quotientKerAlgEquivOfSurjective (evalAt_surjective (k := k) (P := P)))

theorem residueFieldAlgEquiv_def : residueFieldAlgEquiv k P =
    (quotientEquivAlgOfEq k (ker_evalAt (k := k) (P := P)).symm).trans
      (quotientKerAlgEquivOfSurjective (evalAt_surjective (k := k) (P := P))) :=
  (rfl)

variable {k P}

@[simp]
theorem residueFieldAlgEquiv_residue (f : localRing k P) :
    residueFieldAlgEquiv k P (residue _ f) = evalAt k P f := by
  rw [residueFieldAlgEquiv_def]
  change ((quotientEquivAlgOfEq k (ker_evalAt (k := k) (P := P)).symm).trans
    (quotientKerAlgEquivOfSurjective (evalAt_surjective (k := k) (P := P))))
      (Ideal.Quotient.mk (maximalIdeal (localRing k P)) f) = _
  rw [AlgEquiv.trans_apply, quotientEquivAlgOfEq_mk]
  exact quotientKerAlgEquivOfSurjective_mk _ f

/-- A polynomial lies in the `r`-th power of the maximal ideal of `𝒪_P(𝔸ⁿ)` iff its order of
vanishing at `P` is at least `r`. -/
theorem algebraMap_mem_maximalIdeal_pow_iff {f : MvPolynomial σ k} {r : ℕ} :
    algebraMap _ (localRing k P) f ∈ maximalIdeal (localRing k P) ^ r ↔ r ≤ f.orderAt P := by
  rw [← mem_comap, ← under_def,
    IsLocalization.AtPrime.under_maximalIdeal_pow (vanishingIdeal k {P}) (localRing k P),
    mem_pow_vanishingIdeal_singleton_iff]

/-- A polynomial lies in the maximal ideal of `𝒪_P(𝔸ⁿ)` iff it vanishes at `P`. -/
theorem algebraMap_mem_maximalIdeal_iff {f : MvPolynomial σ k} :
    algebraMap _ (localRing k P) f ∈ maximalIdeal (localRing k P) ↔ eval P f = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_algebraMap_iff, not_not]

variable (k P) in
/-- The map `k[X] → 𝒪_P(𝔸ⁿ)` is injective. -/
theorem algebraMap_injective :
    Function.Injective (algebraMap (MvPolynomial σ k) (localRing k P)) :=
  IsLocalization.injective (localRing k P)
    (vanishingIdeal k {P} : Ideal (MvPolynomial σ k)).primeCompl_le_nonZeroDivisors

variable [Finite σ]

/-- `𝒪_P(𝔸ⁿ)` is a regular local ring. -/
instance : IsRegularLocalRing (localRing k P) := inferInstance

/-- The local ring of `n`-dimensional affine space at a point has Krull dimension `n`. -/
theorem ringKrullDim_eq : ringKrullDim (localRing k P) = Nat.card σ := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (vanishingIdeal k {P}),
    height_eq_natCard_of_isMaximal]
  rfl

end localRing

/-! ### Quotients -/

namespace localRing

variable {k P}

variable (P) in
/-- The quotient of the polynomial ring by a power of the ideal of `P` is the quotient of
`𝒪_P(𝔸ⁿ)` by the same power of its maximal ideal: `k[X] ⧸ I_P ^ r ≅ 𝒪_P ⧸ 𝔪 ^ r`. -/
noncomputable def quotientPowAlgEquiv (r : ℕ) :
    (MvPolynomial σ k ⧸ vanishingIdeal k {P} ^ r) ≃ₐ[k]
      localRing k P ⧸ maximalIdeal (localRing k P) ^ r :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow (vanishingIdeal k {P}) (localRing k P)
    r).restrictScalars k

theorem quotientPowAlgEquiv_def (r : ℕ) : quotientPowAlgEquiv P r =
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (vanishingIdeal k {P}) (localRing k P)
      r).restrictScalars k :=
  (rfl)

@[simp]
theorem quotientPowAlgEquiv_mk (r : ℕ) (f : MvPolynomial σ k) :
    quotientPowAlgEquiv P r (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (algebraMap _ _ f) := by
  rw [quotientPowAlgEquiv_def, AlgEquiv.restrictScalars_apply,
    IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]

/-- A polynomial lies in `J 𝒪_P + 𝔪 ^ r` iff it lies in `J + I_P ^ r`. -/
theorem algebraMap_mem_map_sup_maximalIdeal_pow_iff {J : Ideal (MvPolynomial σ k)} {r : ℕ}
    {f : MvPolynomial σ k} :
    algebraMap _ (localRing k P) f ∈
        J.map (algebraMap _ (localRing k P)) ⊔ maximalIdeal (localRing k P) ^ r ↔
      f ∈ J ⊔ vanishingIdeal k {P} ^ r := by
  set e := quotientPowAlgEquiv P r
  have hcomp : (Ideal.Quotient.mk (maximalIdeal (localRing k P) ^ r)).comp
      (algebraMap (MvPolynomial σ k) (localRing k P)) =
      (e : _ →+* _).comp (Ideal.Quotient.mk (vanishingIdeal k {P} ^ r)) :=
    RingHom.ext fun f ↦ by simp [e]
  have h := congr($hcomp f)
  rw [RingHom.comp_apply, RingHom.comp_apply] at h
  rw [← Ideal.mem_quotient_iff_mem_sup, ← Ideal.mem_quotient_iff_mem_sup, Ideal.map_map, hcomp,
    ← Ideal.map_map, h]
  exact Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv)

variable (P) in
/-- The polynomials in `J 𝒪_P + 𝔪 ^ r` are those of `J + I_P ^ r`. -/
theorem comap_map_sup_maximalIdeal_pow (J : Ideal (MvPolynomial σ k)) (r : ℕ) :
    (J.map (algebraMap _ (localRing k P)) ⊔ maximalIdeal (localRing k P) ^ r).comap
      (algebraMap _ _) = J ⊔ vanishingIdeal k {P} ^ r :=
  Ideal.ext fun _ ↦ algebraMap_mem_map_sup_maximalIdeal_pow_iff

variable (P) in
/-- The map `k[X] ⧸ (J + I_P ^ r) → 𝒪_P ⧸ (J 𝒪_P + 𝔪 ^ r)` is bijective. -/
theorem bijective_quotientMap_sup_maximalIdeal_pow (J : Ideal (MvPolynomial σ k)) (r : ℕ) :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap _ (localRing k P)) ⊔
      maximalIdeal (localRing k P) ^ r) (algebraMap (MvPolynomial σ k) (localRing k P))
      (comap_map_sup_maximalIdeal_pow P J r).ge) := by
  refine ⟨Ideal.quotientMap_injective' (comap_map_sup_maximalIdeal_pow P J r).le, fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := (quotientPowAlgEquiv P r).surjective (Ideal.Quotient.mk _ y)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  rw [quotientPowAlgEquiv_mk] at hg
  exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.Quotient.eq.1 hg))⟩

variable (P) in
/-- `k[X] ⧸ (J + I_P ^ r)` and `𝒪_P ⧸ (J 𝒪_P + 𝔪 ^ r)` have the same length over `k`. -/
theorem length_quotient_map_sup_maximalIdeal_pow (J : Ideal (MvPolynomial σ k)) (r : ℕ) :
    Module.length k
        (localRing k P ⧸ J.map (algebraMap _ (localRing k P)) ⊔ maximalIdeal (localRing k P) ^ r) =
      Module.length k (MvPolynomial σ k ⧸ J ⊔ vanishingIdeal k {P} ^ r) :=
  (LinearEquiv.ofBijective (Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom k _ (localRing k P))
    (by exact (comap_map_sup_maximalIdeal_pow P J r).ge)).toLinearMap
    (by exact bijective_quotientMap_sup_maximalIdeal_pow P J r)).length_eq.symm

/-- **Local rings of a subvariety as quotients of the local ring of affine space.** Let `P ∈ kⁿ`
with ideal `I_P`, `𝒪 = 𝒪_P(𝔸ⁿ)` and `𝔪` its maximal ideal.

* `I_P ^ r 𝒪 = 𝔪 ^ r` for all `r`, and the natural map `k[X] ⧸ I_P ^ r → 𝒪 ⧸ 𝔪 ^ r` is an
  isomorphism.
* For ideals `I ≤ J ≤ I_P`, the image of `I_P` in `k[X] ⧸ I` is prime, the natural map
  `𝒪_P(k[X] ⧸ I) → 𝒪 ⧸ I 𝒪` is an isomorphism, and so is the natural map
  `𝒪 ⧸ J 𝒪 → 𝒪_P(k[X] ⧸ I) ⧸ J' 𝒪_P(k[X] ⧸ I)`, where `J'` is the image of `J` in `k[X] ⧸ I`
  and `𝒪_P(k[X] ⧸ I)` is the localization of `k[X] ⧸ I` at the image of `I_P`.

Milestone: *Local rings of a subvariety as quotients of the local ring of affine space*. -/
theorem quotient_iso (I J : Ideal (MvPolynomial σ k)) (hIJ : I ≤ J)
    (hJ : J ≤ vanishingIdeal k {P}) :
    (∀ r : ℕ, (vanishingIdeal k {P} ^ r).map (algebraMap _ (localRing k P)) =
      maximalIdeal (localRing k P) ^ r) ∧
    (∀ r : ℕ, ∃ e : (MvPolynomial σ k ⧸ vanishingIdeal k {P} ^ r) ≃ₐ[k]
        localRing k P ⧸ maximalIdeal (localRing k P) ^ r,
      ∀ f, e (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (algebraMap _ _ f)) ∧
    ∃ _ : ((vanishingIdeal k {P}).map (Ideal.Quotient.mk I)).IsPrime,
      (∃ e : Localization.AtPrime ((vanishingIdeal k {P}).map (Ideal.Quotient.mk I)) ≃ₐ[k]
          localRing k P ⧸ I.map (algebraMap _ (localRing k P)),
        ∀ f, e (algebraMap _ _ (Ideal.Quotient.mk I f)) =
          Ideal.Quotient.mk _ (algebraMap _ _ f)) ∧
      ∃ e : (localRing k P ⧸ J.map (algebraMap _ (localRing k P))) ≃ₐ[k]
          Localization.AtPrime ((vanishingIdeal k {P}).map (Ideal.Quotient.mk I)) ⧸
            (J.map (Ideal.Quotient.mk I)).map (algebraMap _ _),
        ∀ f, e (Ideal.Quotient.mk _ (algebraMap _ _ f)) =
          Ideal.Quotient.mk _ (algebraMap _ _ (Ideal.Quotient.mk I f)) :=
  have := isPrime_map_quotientMk_of_isPrime (hIJ.trans hJ)
  ⟨map_vanishingIdeal_pow, fun r => ⟨quotientPowAlgEquiv P r, quotientPowAlgEquiv_mk r⟩, this,
    ⟨Localization.AtPrime.quotientAlgEquiv k (hIJ.trans hJ),
      Localization.AtPrime.quotientAlgEquiv_algebraMap_mk _⟩,
    Localization.AtPrime.quotientMapAlgEquiv k hIJ (hIJ.trans hJ),
      Localization.AtPrime.quotientMapAlgEquiv_mk_algebraMap _ _⟩

/-- The local ring at `P` of a variety `V(I) ∋ P`, for a prime `I`, is a domain:
`𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)` is a domain. -/
theorem isDomain_quotient (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (hI : I ≤ vanishingIdeal k {P}) :
    IsDomain (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) :=
  have := isPrime_map_quotientMk_of_isPrime hI
  MulEquiv.isDomain _ (Localization.AtPrime.quotientAlgEquiv k hI).symm.toRingEquiv.toMulEquiv

/-! #### The value map of `𝒪_P(V)` -/

/-- For `P ∈ V(I)`, the ideal `I 𝒪_P(𝔸ⁿ)` lies in the maximal ideal. -/
theorem map_le_maximalIdeal {I : Ideal (MvPolynomial σ k)} (hI : I ≤ vanishingIdeal k {P}) :
    I.map (algebraMap _ (localRing k P)) ≤ maximalIdeal (localRing k P) :=
  map_vanishingIdeal (k := k) (P := P) ▸ map_mono hI

/-- For `P ∈ V(I)`, the local ring `𝒪_P(V(I)) = 𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)` is a local ring. -/
theorem isLocalRing_quotient {I : Ideal (MvPolynomial σ k)} (hI : I ≤ vanishingIdeal k {P}) :
    IsLocalRing (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) :=
  have : Nontrivial (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
      (map_le_maximalIdeal hI))
  .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- For `F(P) = 0`, the local ring `𝒪_P(𝔸ⁿ) ⧸ (F)` of the hypersurface `F` at `P` is a local
ring. -/
theorem isLocalRing_quotient_span_singleton {F : MvPolynomial σ k} (hF : eval P F = 0) :
    IsLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) := by
  have := isLocalRing_quotient (P := P) (I := span {F})
    (span_le.2 (Set.singleton_subset_iff.2 ((mem_vanishingIdeal_singleton_iff P F).2 hF)))
  rwa [Ideal.map_span, Set.image_singleton] at this

/-- Every element of `𝒪_P(𝔸ⁿ) ⧸ I` is the image of a polynomial up to a unit. -/
theorem exists_mul_isUnit_eq_mk (I : Ideal (localRing k P)) (r : localRing k P ⧸ I) :
    ∃ (G : MvPolynomial σ k) (u : localRing k P ⧸ I), IsUnit u ∧
      r * u = Ideal.Quotient.mk I (algebraMap _ _ G) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨⟨G, s⟩, rfl⟩ := IsLocalization.mk'_surjective (vanishingIdeal k {P}).primeCompl x
  refine ⟨G, Ideal.Quotient.mk I (algebraMap _ _ (s : MvPolynomial σ k)),
    (IsLocalization.map_units (localRing k P) s).map _, ?_⟩
  rw [← map_mul, IsLocalization.mk'_spec]

/-- For `F(P) = 0`, an element of `𝒪_P(𝔸ⁿ)` maps into the maximal ideal of `𝒪_P(𝔸ⁿ) ⧸ (F)` iff
it lies in `𝔪_P`. -/
theorem mk_mem_map_maximalIdeal_iff {F : MvPolynomial σ k} (hF : eval P F = 0)
    (x : localRing k P) :
    Ideal.Quotient.mk (span {algebraMap _ (localRing k P) F}) x ∈
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ↔
      x ∈ maximalIdeal (localRing k P) := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.2]
  exact span_le.2 (Set.singleton_subset_iff.2 (algebraMap_mem_maximalIdeal_iff.2 hF))

/-- Membership in a power of the image of an ideal in a quotient ring. -/
private theorem mk_mem_map_pow_iff {A : Type*} [CommRing A] (I J : Ideal A) (r : ℕ) (x : A) :
    Ideal.Quotient.mk I x ∈ J.map (Ideal.Quotient.mk I) ^ r ↔ x ∈ J ^ r ⊔ I := by
  rw [← Ideal.map_pow, mem_quotient_iff_mem_sup]

/-- For `r ≤ m_P(F)`, an element of `𝒪_P(𝔸ⁿ)` maps into the `r`-th power of the maximal ideal
of `𝒪_P(𝔸ⁿ) ⧸ (F)` iff it lies in `𝔪_P ^ r`. -/
theorem mk_mem_map_maximalIdeal_pow_iff {F : MvPolynomial σ k} {r : ℕ}
    (hr : (r : ℕ∞) ≤ F.orderAt P) (x : localRing k P) :
    Ideal.Quotient.mk (span {algebraMap _ (localRing k P) F}) x ∈
        (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ r ↔
      x ∈ maximalIdeal (localRing k P) ^ r := by
  rw [mk_mem_map_pow_iff, sup_eq_left.2]
  exact span_le.2 (Set.singleton_subset_iff.2 (algebraMap_mem_maximalIdeal_pow_iff.2 hr))

variable (P) in
/-- The value `f(P)` of an element `f` of `𝒪_P(V(I)) = 𝒪_P(𝔸ⁿ) ⧸ I 𝒪_P(𝔸ⁿ)`, for `P ∈ V(I)`, as a
`k`-algebra map to `k`. -/
noncomputable def quotientEvalAt (I : Ideal (MvPolynomial σ k))
    (hI : I ≤ vanishingIdeal k {P}) :
    localRing k P ⧸ I.map (algebraMap _ (localRing k P)) →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (evalAt k P) fun _ ha => evalAt_eq_zero_iff.2 (map_le_maximalIdeal hI ha)

theorem quotientEvalAt_def (I : Ideal (MvPolynomial σ k)) (hI : I ≤ vanishingIdeal k {P}) :
    quotientEvalAt P I hI = Ideal.Quotient.liftₐ _ (evalAt k P)
      fun _ ha => evalAt_eq_zero_iff.2 (map_le_maximalIdeal hI ha) :=
  (rfl)

@[simp]
theorem quotientEvalAt_mk {I : Ideal (MvPolynomial σ k)} (hI : I ≤ vanishingIdeal k {P})
    (f : localRing k P) :
    quotientEvalAt P I hI (Ideal.Quotient.mk _ f) = evalAt k P f :=
  (rfl)

@[simp]
theorem quotientEvalAt_algebraMap {I : Ideal (MvPolynomial σ k)}
    (hI : I ≤ vanishingIdeal k {P}) (f : MvPolynomial σ k) :
    quotientEvalAt P I hI (algebraMap _ _ f) = eval P f :=
  (quotientEvalAt_mk hI _).trans (evalAt_algebraMap f)

theorem quotientEvalAt_surjective {I : Ideal (MvPolynomial σ k)}
    (hI : I ≤ vanishingIdeal k {P}) : Function.Surjective (quotientEvalAt P I hI) :=
  fun a => ⟨_, (quotientEvalAt_algebraMap hI (C a)).trans (eval_C a)⟩

/-- An element of `𝒪_P(V(I))` is a unit iff its value at `P` is not zero. -/
theorem isUnit_iff_quotientEvalAt_ne_zero {I : Ideal (MvPolynomial σ k)}
    (hI : I ≤ vanishingIdeal k {P}) {f : localRing k P ⧸ I.map (algebraMap _ (localRing k P))} :
    IsUnit f ↔ quotientEvalAt P I hI f ≠ 0 := by
  refine ⟨fun h => ((h.map (quotientEvalAt P I hI)).ne_zero), fun h => ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [quotientEvalAt_mk, Ne, evalAt_eq_zero_iff] at h
  exact (notMem_maximalIdeal.1 h).map _

/-- The kernel of the value map `𝒪_P(V(I)) → k` is the maximal ideal. -/
theorem ker_quotientEvalAt {I : Ideal (MvPolynomial σ k)} (hI : I ≤ vanishingIdeal k {P})
    [IsLocalRing (localRing k P ⧸ I.map (algebraMap _ (localRing k P)))] :
    RingHom.ker (quotientEvalAt P I hI) =
      maximalIdeal (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) := by
  ext f
  rw [RingHom.mem_ker, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_quotientEvalAt_ne_zero hI,
    not_not]

variable (P) in
/-- The residue field of `𝒪_P(V(I))`, for `P ∈ V(I)`, is `k`, by the value map. -/
noncomputable def quotientResidueFieldAlgEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I ≤ vanishingIdeal k {P})
    [IsLocalRing (localRing k P ⧸ I.map (algebraMap _ (localRing k P)))] :
    ResidueField (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) ≃ₐ[k] k :=
  (quotientEquivAlgOfEq k (ker_quotientEvalAt hI).symm).trans
    (quotientKerAlgEquivOfSurjective (quotientEvalAt_surjective hI))

theorem quotientResidueFieldAlgEquiv_def (I : Ideal (MvPolynomial σ k))
    (hI : I ≤ vanishingIdeal k {P})
    [IsLocalRing (localRing k P ⧸ I.map (algebraMap _ (localRing k P)))] :
    quotientResidueFieldAlgEquiv P I hI =
      (quotientEquivAlgOfEq k (ker_quotientEvalAt hI).symm).trans
        (quotientKerAlgEquivOfSurjective (quotientEvalAt_surjective hI)) :=
  (rfl)

@[simp]
theorem quotientResidueFieldAlgEquiv_residue {I : Ideal (MvPolynomial σ k)}
    (hI : I ≤ vanishingIdeal k {P})
    [IsLocalRing (localRing k P ⧸ I.map (algebraMap _ (localRing k P)))]
    (f : localRing k P ⧸ I.map (algebraMap _ (localRing k P))) :
    quotientResidueFieldAlgEquiv P I hI (residue _ f) = quotientEvalAt P I hI f :=
  quotientKerAlgEquivOfSurjective_mk (quotientEvalAt_surjective hI) f

end localRing

/-! ### Polynomial maps and changes of coordinates -/

namespace localRing

variable {k P} {τ : Type*} {Q : τ → k}

/-- A polynomial map sending `P` to `Q`, given by `ψ : k[Y] → k[X]` with `(ψ g)(P) = g(Q)`, pulls
the ideal of `P` back to the ideal of `Q`. -/
theorem comap_vanishingIdeal (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) :
    (vanishingIdeal k {P}).comap ψ = vanishingIdeal k {Q} := by
  ext g
  simp [h]

/-- The local homomorphism `𝒪_Q(𝔸ᵐ) → 𝒪_P(𝔸ⁿ)` induced by a polynomial map sending `P` to `Q`,
given by `ψ : k[Y] → k[X]` with `(ψ g)(P) = g(Q)`. -/
noncomputable def map (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) : localRing k Q →ₐ[k] localRing k P :=
  Localization.localAlgHom _ _ ψ (comap_vanishingIdeal ψ h).symm

theorem map_def (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) :
    map ψ h = Localization.localAlgHom _ _ ψ (comap_vanishingIdeal ψ h).symm :=
  (rfl)

@[simp]
theorem map_algebraMap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) (g : MvPolynomial τ k) :
    map ψ h (algebraMap _ _ g) = algebraMap _ _ (ψ g) := by
  simp [map_def, Localization.localRingHom_to_map]

instance (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (h : ∀ g, eval P (ψ g) = eval Q g) :
    IsLocalHom (map ψ h) :=
  ⟨fun a ha => (Localization.isLocalHom_localRingHom _ _ ψ.toRingHom
    (comap_vanishingIdeal ψ h).symm).map_nonunit a ha⟩

/-- The map induced by a polynomial map respects values: `(φ̃ f)(P) = f(Q)`. -/
@[simp]
theorem evalAt_map (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) (f : localRing k Q) :
    evalAt k P (map ψ h f) = evalAt k Q f := by
  obtain ⟨g, s, rfl⟩ := IsLocalization.mk'_surjective (vanishingIdeal k {Q}).primeCompl f
  simp [map_def, Localization.localRingHom_mk', h]

/-- The map induced by a polynomial map is the unique `k`-algebra map extending it. -/
theorem map_unique (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) (φ : localRing k Q →ₐ[k] localRing k P)
    (hφ : ∀ g, φ (algebraMap _ _ g) = algebraMap _ _ (ψ g)) : φ = map ψ h :=
  AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (vanishingIdeal k {Q}).primeCompl <|
    RingHom.ext fun g => by simp [hφ]

/-- The isomorphism `𝒪_Q(𝔸ᵐ) ≅ 𝒪_P(𝔸ⁿ)` induced by a polynomial isomorphism sending `P` to
`Q`, given by `ψ : k[Y] ≃ k[X]` with `(ψ g)(P) = g(Q)`. -/
noncomputable def mapEquiv (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) : localRing k Q ≃ₐ[k] localRing k P :=
  Localization.localAlgEquiv _ _ ψ (comap_vanishingIdeal ψ.toAlgHom h).symm

theorem mapEquiv_def (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) :
    mapEquiv ψ h = Localization.localAlgEquiv _ _ ψ (comap_vanishingIdeal ψ.toAlgHom h).symm :=
  (rfl)

@[simp]
theorem coe_mapEquiv (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) :
    (mapEquiv ψ h : localRing k Q →ₐ[k] localRing k P) = map ψ.toAlgHom h :=
  (rfl)

@[simp]
theorem mapEquiv_algebraMap (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) (g : MvPolynomial τ k) :
    mapEquiv ψ h (algebraMap _ _ g) = algebraMap _ _ (ψ g) :=
  map_algebraMap ψ.toAlgHom h g

variable (P) in
/-- The Taylor shift `f ↦ f(X + P)` identifies `𝒪_P(𝔸ⁿ)` with the local ring at the origin. -/
noncomputable def taylorEquiv : localRing k P ≃ₐ[k] localRing k (0 : σ → k) :=
  mapEquiv (taylorAlgEquiv P) fun g => by simp

@[simp]
theorem taylorEquiv_algebraMap (g : MvPolynomial σ k) :
    taylorEquiv P (algebraMap _ _ g) = algebraMap _ _ (taylor P g) :=
  (mapEquiv_algebraMap (taylorAlgEquiv P) _ g).trans (by rw [coe_taylorAlgEquiv])

/-- An invertible linear substitution `f ↦ f(M X)` identifies the local ring at `M P` with the
local ring at `P`. -/
noncomputable def linearSubstEquiv [Fintype σ] [DecidableEq σ] (M : Matrix.GeneralLinearGroup σ k) :
    localRing k (M.1 *ᵥ P) ≃ₐ[k] localRing k P :=
  mapEquiv (linearSubstAlgEquiv M) fun g => by
    rw [linearSubstAlgEquiv_apply]; exact eval_linearSubst _ _ g

@[simp]
theorem linearSubstEquiv_algebraMap [Fintype σ] [DecidableEq σ] (M : Matrix.GeneralLinearGroup σ k)
    (g : MvPolynomial σ k) :
    linearSubstEquiv (P := P) M (algebraMap _ _ g) = algebraMap _ _ (linearSubst M.1 g) :=
  by rw [← linearSubstAlgEquiv_apply]; exact mapEquiv_algebraMap _ _ g

/-! #### Polynomial maps between subvarieties -/

/-- A polynomial map sending `V(I)` into `V(J)` and `P` to `Q`, given by `ψ : k[Y] → k[X]` with
`(ψ g)(P) = g(Q)` and `J ≤ ψ⁻¹(I)`, maps `J 𝒪_Q(𝔸ᵐ)` into `I 𝒪_P(𝔸ⁿ)`. -/
theorem map_le_comap_map (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) :
    J.map (algebraMap _ (localRing k Q)) ≤
      (I.map (algebraMap _ (localRing k P))).comap (map ψ h) := by
  rw [map_le_iff_le_comap]
  intro g hg
  rw [mem_comap, mem_comap, map_algebraMap]
  exact mem_map_of_mem _ (hJI hg)

/-- The homomorphism `𝒪_Q(W) → 𝒪_P(V)` induced by a polynomial map `V → W` sending `P` to `Q`,
for `V = V(I)` and `W = V(J)`: it is given by `ψ : k[Y] → k[X]` with `(ψ g)(P) = g(Q)` and
`J ≤ ψ⁻¹(I)`. -/
noncomputable def quotientMap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) :
    localRing k Q ⧸ J.map (algebraMap _ (localRing k Q)) →ₐ[k]
      localRing k P ⧸ I.map (algebraMap _ (localRing k P)) :=
  quotientMapₐ _ (map ψ h) (map_le_comap_map ψ h hJI)

theorem quotientMap_def (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) :
    quotientMap ψ h hJI = quotientMapₐ _ (map ψ h) (map_le_comap_map ψ h hJI) :=
  (rfl)

@[simp]
theorem quotientMap_mk (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) (f : localRing k Q) :
    quotientMap ψ h hJI (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (map ψ h f) :=
  (rfl)

@[simp]
theorem quotientMap_algebraMap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) (g : MvPolynomial τ k) :
    quotientMap ψ h hJI (algebraMap _ _ g) = algebraMap _ _ (ψ g) :=
  congrArg (Ideal.Quotient.mk _) (map_algebraMap ψ h g)

/-- If `P ∈ V(I)` and `J ≤ ψ⁻¹(I)`, then `Q ∈ V(J)`. -/
theorem le_vanishingIdeal_of_le_comap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) (hI : I ≤ vanishingIdeal k {P}) :
    J ≤ vanishingIdeal k {Q} :=
  comap_vanishingIdeal ψ h ▸ hJI.trans (comap_mono hI)

/-- The map induced by a polynomial map respects values: `(φ̃ f)(P) = f(Q)`. -/
@[simp]
theorem quotientEvalAt_quotientMap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) (hI : I ≤ vanishingIdeal k {P})
    (f : localRing k Q ⧸ J.map (algebraMap _ (localRing k Q))) :
    quotientEvalAt P I hI (quotientMap ψ h hJI f) =
      quotientEvalAt Q J (le_vanishingIdeal_of_le_comap ψ h hJI hI) f := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  simp

/-- For `P ∈ V(I)`, the map `𝒪_Q(W) → 𝒪_P(V)` induced by a polynomial map is a local
homomorphism. -/
theorem isLocalHom_quotientMap (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ) (hI : I ≤ vanishingIdeal k {P}) :
    IsLocalHom (quotientMap ψ h hJI) :=
  ⟨fun f hf => by
    rw [isUnit_iff_quotientEvalAt_ne_zero hI, quotientEvalAt_quotientMap _ _ _ hI] at hf
    exact (isUnit_iff_quotientEvalAt_ne_zero _).2 hf⟩

/-- The map `𝒪_Q(W) → 𝒪_P(V)` induced by a polynomial map is the unique `k`-algebra map
extending it. -/
theorem quotientMap_unique (ψ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : J ≤ I.comap ψ)
    (φ : localRing k Q ⧸ J.map (algebraMap _ (localRing k Q)) →ₐ[k]
      localRing k P ⧸ I.map (algebraMap _ (localRing k P)))
    (hφ : ∀ g, φ (Ideal.Quotient.mk _ (algebraMap _ _ g)) =
      Ideal.Quotient.mk _ (algebraMap _ _ (ψ g))) :
    φ = quotientMap ψ h hJI :=
  Ideal.Quotient.algHom_ext _ <| AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (vanishingIdeal k {Q}).primeCompl <|
      RingHom.ext fun g => (hφ g).trans (quotientMap_algebraMap ψ h hJI g).symm

/-- A polynomial isomorphism `ψ` sending `P` to `Q` carries `J 𝒪_Q(𝔸ᵐ)` to `ψ(J) 𝒪_P(𝔸ⁿ)`. -/
theorem map_map_algebraMap (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) (J : Ideal (MvPolynomial τ k)) :
    (J.map ψ).map (algebraMap _ (localRing k P)) =
      (J.map (algebraMap _ (localRing k Q))).map (mapEquiv ψ h : _ →+* _) := by
  rw [Ideal.map_map]
  refine (Ideal.map_map (ψ : MvPolynomial τ k →+* MvPolynomial σ k) _).trans ?_
  congr 1
  exact RingHom.ext fun g => (mapEquiv_algebraMap ψ h g).symm

/-- The isomorphism `𝒪_Q(W) ≅ 𝒪_P(V)` induced by a polynomial isomorphism sending `P` to `Q`
and `V = V(I)` onto `W = V(J)`: it is given by `ψ : k[Y] ≃ k[X]` with `(ψ g)(P) = g(Q)` and
`I = ψ(J)`. -/
noncomputable def quotientMapEquiv (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : I = J.map ψ) :
    (localRing k Q ⧸ J.map (algebraMap _ (localRing k Q))) ≃ₐ[k]
      localRing k P ⧸ I.map (algebraMap _ (localRing k P)) :=
  quotientEquivAlg _ _ (mapEquiv ψ h) (hJI ▸ map_map_algebraMap ψ h J)

theorem quotientMapEquiv_def (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : I = J.map ψ) :
    quotientMapEquiv ψ h hJI =
      quotientEquivAlg _ _ (mapEquiv ψ h) (hJI ▸ map_map_algebraMap ψ h J) :=
  (rfl)

@[simp]
theorem quotientMapEquiv_mk (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : I = J.map ψ) (f : localRing k Q) :
    quotientMapEquiv ψ h hJI (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (mapEquiv ψ h f) :=
  (rfl)

@[simp]
theorem quotientMapEquiv_algebraMap (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : I = J.map ψ) (g : MvPolynomial τ k) :
    quotientMapEquiv ψ h hJI (algebraMap _ _ g) = algebraMap _ _ (ψ g) :=
  congrArg (Ideal.Quotient.mk _) (mapEquiv_algebraMap ψ h g)

/-- The isomorphism `𝒪_Q(W) ≅ 𝒪_P(V)` underlies the map `𝒪_Q(W) → 𝒪_P(V)`. -/
theorem coe_quotientMapEquiv (ψ : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (h : ∀ g, eval P (ψ g) = eval Q g) {J : Ideal (MvPolynomial τ k)}
    {I : Ideal (MvPolynomial σ k)} (hJI : I = J.map ψ) :
    (quotientMapEquiv ψ h hJI : _ →ₐ[k] _) =
      quotientMap ψ.toAlgHom h (hJI ▸ le_comap_map (f := ψ.toAlgHom)) :=
  (quotientMap_unique _ _ _ _ fun g => quotientMapEquiv_algebraMap ψ h hJI g)

variable (P) in
/-- The Taylor shift `f ↦ f(X + P)` identifies `𝒪_P(V(I))` with the local ring at the origin of
the translate `V(I) - P`, whose ideal is the image of `I`. -/
noncomputable def quotientTaylorEquiv (I : Ideal (MvPolynomial σ k)) :
    (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) ≃ₐ[k]
      localRing k (0 : σ → k) ⧸ (I.map (taylor P)).map (algebraMap _ (localRing k 0)) :=
  quotientMapEquiv (taylorAlgEquiv P) (fun g => by simp)
    (by simp only [Ideal.map, coe_taylorAlgEquiv])

@[simp]
theorem quotientTaylorEquiv_algebraMap (I : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k) :
    quotientTaylorEquiv P I (algebraMap _ _ g) = algebraMap _ _ (taylor P g) :=
  (quotientMapEquiv_algebraMap (taylorAlgEquiv P) _ _ g).trans (by rw [coe_taylorAlgEquiv])

/-- An invertible linear substitution `f ↦ f(M X)` identifies the local ring of `V(I)` at `M P`
with the local ring at `P` of its preimage, whose ideal is the image of `I`. -/
noncomputable def quotientLinearSubstEquiv [Fintype σ] [DecidableEq σ]
    (M : Matrix.GeneralLinearGroup σ k) (I : Ideal (MvPolynomial σ k)) :
    (localRing k (M.1 *ᵥ P) ⧸ I.map (algebraMap _ (localRing k (M.1 *ᵥ P)))) ≃ₐ[k]
      localRing k P ⧸ (I.map (linearSubst M.1)).map (algebraMap _ (localRing k P)) :=
  quotientMapEquiv (linearSubstAlgEquiv M)
    (fun g => by rw [linearSubstAlgEquiv_apply]; exact eval_linearSubst _ _ g)
    (by rw [← toAlgHom_linearSubstAlgEquiv]; rfl)

@[simp]
theorem quotientLinearSubstEquiv_algebraMap [Fintype σ] [DecidableEq σ]
    (M : Matrix.GeneralLinearGroup σ k) (I : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k) :
    quotientLinearSubstEquiv (P := P) M I (algebraMap _ _ g) =
      algebraMap _ _ (linearSubst M.1 g) :=
  by rw [← linearSubstAlgEquiv_apply]; exact quotientMapEquiv_algebraMap _ _ _ g

end localRing

/-! #### Isomorphisms from localizations away from a polynomial -/

namespace localRing

variable {k P} {τ : Type*} {Q : τ → k}

variable (P) in
/-- For `h(P) ≠ 0`, the `k`-algebra map `k[X][1/h] → 𝒪_P(𝔸ⁿ)`: `h` is a unit in `𝒪_P(𝔸ⁿ)`. -/
noncomputable def ofAway (h : MvPolynomial σ k) (hP : eval P h ≠ 0) :
    Localization.Away h →ₐ[k] localRing k P :=
  IsLocalization.liftAlgHom (M := Submonoid.powers h)
    (f := IsScalarTower.toAlgHom k (MvPolynomial σ k) (localRing k P)) fun s => by
      obtain ⟨n, hn⟩ := s.2
      rw [← hn]
      simpa using (isUnit_algebraMap_iff.2 hP).pow n

theorem ofAway_def (h : MvPolynomial σ k) (hP : eval P h ≠ 0) : ofAway P h hP =
    IsLocalization.liftAlgHom (M := Submonoid.powers h)
      (f := IsScalarTower.toAlgHom k (MvPolynomial σ k) (localRing k P)) fun s => by
        obtain ⟨n, hn⟩ := s.2
        rw [← hn]
        simpa using (isUnit_algebraMap_iff.2 hP).pow n :=
  (rfl)

@[simp]
theorem ofAway_algebraMap {h : MvPolynomial σ k} (hP : eval P h ≠ 0) (f : MvPolynomial σ k) :
    ofAway P h hP (algebraMap _ _ f) = algebraMap _ _ f := by
  simp [ofAway_def]

/-- The value at `P` of the image of `x ∈ k[X][1/h]` in `𝒪_P(𝔸ⁿ)` is the value of `x` at `P`. -/
@[simp]
theorem evalAt_ofAway {h : MvPolynomial σ k} (hP : eval P h ≠ 0) (x : Localization.Away h) :
    evalAt k P (ofAway P h hP x) =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP) x := by
  have : ((evalAt k P).toRingHom.comp (ofAway P h hP).toRingHom) =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP) :=
    IsLocalization.ringHom_ext (Submonoid.powers h) <| RingHom.ext fun f => by
      simp [Localization.awayLift]
  exact congr($this x)

/-- An element of `𝒪_P(𝔸ⁿ)` is a unit iff its value at `P` is nonzero. -/
theorem isUnit_iff_evalAt_ne_zero {f : localRing k P} : IsUnit f ↔ evalAt k P f ≠ 0 := by
  rw [ne_eq, evalAt_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]

/-- A `k`-algebra map `e : k[X][1/h] → k[Y][1/h']` with `(e x)(Q) = x(P)`, for `h(P) ≠ 0` and
`h'(Q) ≠ 0`, induces a `k`-algebra map `𝒪_P(𝔸ⁿ) → 𝒪_Q(𝔸ᵐ)`. -/
noncomputable def mapOfAway {h : MvPolynomial σ k} {h' : MvPolynomial τ k}
    (e : Localization.Away h →ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) :
    localRing k P →ₐ[k] localRing k Q :=
  IsLocalization.liftAlgHom (M := (vanishingIdeal k {P}).primeCompl)
    (f := (ofAway Q h' hQ).comp (e.comp (IsScalarTower.toAlgHom k _ _))) fun s => by
      rw [isUnit_iff_evalAt_ne_zero]
      have := congr($he (algebraMap _ (Localization.Away h) s.1))
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at this
      simpa [this, Localization.awayLift, IsLocalization.Away.lift_eq] using eval_ne_zero s

theorem mapOfAway_def {h : MvPolynomial σ k} {h' : MvPolynomial τ k}
    (e : Localization.Away h →ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) :
    mapOfAway e hP hQ he = IsLocalization.liftAlgHom (M := (vanishingIdeal k {P}).primeCompl)
      (f := (ofAway Q h' hQ).comp (e.comp (IsScalarTower.toAlgHom k _ _))) fun s => by
        rw [isUnit_iff_evalAt_ne_zero]
        have := congr($he (algebraMap _ (Localization.Away h) s.1))
        simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at this
        simpa [this, Localization.awayLift, IsLocalization.Away.lift_eq] using eval_ne_zero s :=
  (rfl)

@[simp]
theorem mapOfAway_algebraMap {h : MvPolynomial σ k} {h' : MvPolynomial τ k}
    (e : Localization.Away h →ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) (f : MvPolynomial σ k) :
    mapOfAway e hP hQ he (algebraMap _ _ f) = ofAway Q h' hQ (e (algebraMap _ _ f)) := by
  simp [mapOfAway_def]

/-- On the image of `k[X][1/h]`, the map induced by `e` is `e`. -/
@[simp]
theorem mapOfAway_ofAway {h : MvPolynomial σ k} {h' : MvPolynomial τ k}
    (e : Localization.Away h →ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) (x : Localization.Away h) :
    mapOfAway e hP hQ he (ofAway P h hP x) = ofAway Q h' hQ (e x) := by
  have : (mapOfAway e hP hQ he).toRingHom.comp (ofAway P h hP).toRingHom =
      (ofAway Q h' hQ).toRingHom.comp (e : Localization.Away h →+* Localization.Away h') :=
    IsLocalization.ringHom_ext (Submonoid.powers h) <| RingHom.ext fun f => by simp
  exact congr($this x)

/-- The map induced by `e` respects values: `(ẽ f)(Q) = f(P)`. -/
@[simp]
theorem evalAt_mapOfAway {h : MvPolynomial σ k} {h' : MvPolynomial τ k}
    (e : Localization.Away h →ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) (f : localRing k P) :
    evalAt k Q (mapOfAway e hP hQ he f) = evalAt k P f := by
  have : (evalAt k Q).toRingHom.comp (mapOfAway e hP hQ he).toRingHom =
      (evalAt k P).toRingHom :=
    IsLocalization.ringHom_ext (vanishingIdeal k {P}).primeCompl <| RingHom.ext fun f => by
      have := congr($he (algebraMap _ (Localization.Away h) f))
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at this
      simpa [Localization.awayLift, IsLocalization.Away.lift_eq] using this
  exact congr($this f)

end localRing

open localRing

variable {k P} {τ : Type*} {Q : τ → k} {h : MvPolynomial σ k} {h' : MvPolynomial τ k}

/-- An isomorphism `e : k[X][1/h] ≅ k[Y][1/h']` with `(e x)(Q) = x(P)`, for `h(P) ≠ 0` and
`h'(Q) ≠ 0`, induces an isomorphism of local rings `𝒪_P(𝔸ⁿ) ≅ 𝒪_Q(𝔸ᵐ)`. -/
noncomputable def localRingEquivOfAway
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) :
    localRing k P ≃ₐ[k] localRing k Q :=
  AlgEquiv.ofAlgHom (mapOfAway e.toAlgHom hP hQ he)
    (mapOfAway e.symm.toAlgHom hQ hP (by rw [← he]; exact RingHom.ext fun x => by simp))
    (AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (vanishingIdeal k {Q}).primeCompl <|
      RingHom.ext fun g => by
        have h1 := mapOfAway_ofAway e.toAlgHom hP hQ he
        simp [← ofAway_algebraMap hQ g, -ofAway_algebraMap, h1])
    (AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (vanishingIdeal k {P}).primeCompl <|
      RingHom.ext fun f => by
        have h1 := mapOfAway_ofAway e.toAlgHom hP hQ he
        have h2 := mapOfAway_ofAway e.symm.toAlgHom hQ hP
          (by rw [← he]; exact RingHom.ext fun x => by simp)
        simp [← ofAway_algebraMap hP f, -ofAway_algebraMap, h1, h2])

theorem localRingEquivOfAway_def
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) :
    (localRingEquivOfAway e hP hQ he : localRing k P →ₐ[k] localRing k Q) =
      mapOfAway e.toAlgHom hP hQ he :=
  (rfl)

/-- On the image of `k[X][1/h]`, the isomorphism induced by `e` is `e`. -/
@[simp]
theorem localRingEquivOfAway_ofAway
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) (x : Localization.Away h) :
    localRingEquivOfAway e hP hQ he (ofAway P h hP x) = ofAway Q h' hQ (e x) := by
  rw [← AlgEquiv.coe_toAlgHom, localRingEquivOfAway_def]
  exact mapOfAway_ofAway e.toAlgHom hP hQ he x

/-- On polynomials, the isomorphism induced by `e` is `e`. -/
@[simp]
theorem localRingEquivOfAway_algebraMap
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) (f : MvPolynomial σ k) :
    localRingEquivOfAway e hP hQ he (algebraMap _ _ f) =
      ofAway Q h' hQ (e (algebraMap _ _ f)) := by
  rw [← ofAway_algebraMap hP f, localRingEquivOfAway_ofAway]

/-- The inverse of the isomorphism induced by `e` is the one induced by `e⁻¹`. -/
theorem localRingEquivOfAway_symm
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) :
    (localRingEquivOfAway e hP hQ he).symm = localRingEquivOfAway e.symm hQ hP
      (by rw [← he]; exact RingHom.ext fun x => by simp) :=
  (rfl)

/-- The isomorphism induced by `e` respects values: `(ẽ f)(Q) = f(P)`. -/
@[simp]
theorem evalAt_localRingEquivOfAway
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP)) (f : localRing k P) :
    evalAt k Q (localRingEquivOfAway e hP hQ he f) = evalAt k P f := by
  rw [← AlgEquiv.coe_toAlgHom, localRingEquivOfAway_def]
  exact evalAt_mapOfAway e.toAlgHom hP hQ he f

/-- If moreover `e f = u g` for a unit `u` of `k[Y][1/h']`, the isomorphism induced by `e`
passes to the quotients: `𝒪_P(𝔸ⁿ) ⧸ (f) ≅ 𝒪_Q(𝔸ᵐ) ⧸ (g)`. -/
noncomputable def quotientEquivOfAway
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP))
    {f : MvPolynomial σ k} {g : MvPolynomial τ k} (u : (Localization.Away h')ˣ)
    (hfg : e (algebraMap _ _ f) = u * algebraMap _ _ g) :
    (localRing k P ⧸ span {algebraMap _ (localRing k P) f}) ≃ₐ[k]
      (localRing k Q ⧸ span {algebraMap _ (localRing k Q) g}) :=
  Ideal.quotientEquivAlg _ _ (localRingEquivOfAway e hP hQ he) <| by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, localRingEquivOfAway_algebraMap,
      hfg, map_mul, ofAway_algebraMap, span_singleton_mul_left_unit ((u.isUnit).map _)]

@[simp]
theorem quotientEquivOfAway_mk
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP))
    {f : MvPolynomial σ k} {g : MvPolynomial τ k} (u : (Localization.Away h')ˣ)
    (hfg : e (algebraMap _ _ f) = u * algebraMap _ _ g) (x : localRing k P) :
    quotientEquivOfAway e hP hQ he u hfg (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (localRingEquivOfAway e hP hQ he x) :=
  (rfl)

/-- The Taylor shift `taylorEquiv P` is the isomorphism induced by the automorphism of
`k[X][1/h]` that the Taylor shift induces, for any `h` with `h(P) ≠ 0`. -/
example (h : MvPolynomial σ k) (hP : eval P h ≠ 0) :
    localRingEquivOfAway (Q := (0 : σ → k)) (h' := taylor P h)
      (IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers h)
        (T := Submonoid.powers (taylor P h)) _ _ (taylorAlgEquiv P)
        (by rw [Submonoid.map_powers, coe_taylorAlgEquiv]))
      hP (by simpa using hP) (IsLocalization.ringHom_ext (Submonoid.powers h) <|
        RingHom.ext fun f => by
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
          rw [IsLocalization.algEquivOfAlgEquiv_eq]
          simp [Localization.awayLift]) =
      taylorEquiv P := by
  refine AlgEquiv.coe_toAlgHom_injective <| AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (vanishingIdeal k {P}).primeCompl <| RingHom.ext fun f => ?_
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    AlgEquiv.coe_toAlgHom, localRingEquivOfAway_algebraMap]
  rw [IsLocalization.algEquivOfAlgEquiv_eq]
  simp

end PlaneCurves.AffineSpace

end
