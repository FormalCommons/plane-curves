/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.RingTheory.MvPolynomial.LocalOrder
public import PlaneCurves.RingTheory.Localization.Quotient

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

## Main results

* `PlaneCurves.AffineSpace.localRing.ker_evalAt`: the kernel of the value map is the maximal
  ideal.
* `PlaneCurves.AffineSpace.localRing.isUnit_algebraMap_iff`: a polynomial is a unit in `𝒪_P`
  iff it does not vanish at `P`.
* `PlaneCurves.AffineSpace.localRing.ringKrullDim_eq`: `𝒪_P(𝔸ⁿ)` is a regular local ring of
  dimension `n`.
* `PlaneCurves.AffineSpace.localRing.algebraMap_mem_maximalIdeal_pow_iff`: a polynomial lies in
  `𝔪 ^ r` iff its order at `P` is at least `r`.
* `PlaneCurves.AffineSpace.localRing.quotient_iso`: local rings of subvarieties are quotients
  of the local ring of affine space. For ideals `I ≤ J ≤ I_P` it gives
  `𝒪_P ⧸ J 𝒪_P ≅ 𝒪_P(k[X] ⧸ I) ⧸ J' 𝒪_P(k[X] ⧸ I)`, from
  `Localization.AtPrime.quotientMapAlgEquiv`.
* `PlaneCurves.AffineSpace.localRing.isDomain_quotient`: the local ring of a variety is a domain.

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
  have := isPrime_map_quotientMk (hIJ.trans hJ)
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
  have := isPrime_map_quotientMk hI
  MulEquiv.isDomain _ (Localization.AtPrime.quotientAlgEquiv k hI).symm.toRingEquiv.toMulEquiv

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
  mapEquiv (AlgEquiv.ofAlgHom (taylor P) (taylor (-P))
    (algHom_ext fun i => by simp [taylor_X]) (algHom_ext fun i => by simp [taylor_X]))
    fun g => by simp

@[simp]
theorem taylorEquiv_algebraMap (g : MvPolynomial σ k) :
    taylorEquiv P (algebraMap _ _ g) = algebraMap _ _ (taylor P g) :=
  mapEquiv_algebraMap _ _ g

/-- An invertible linear substitution `f ↦ f(M X)` identifies the local ring at `M P` with the
local ring at `P`. -/
noncomputable def linearSubstEquiv [Fintype σ] [DecidableEq σ] (M : Matrix.GeneralLinearGroup σ k) :
    localRing k (M.1 *ᵥ P) ≃ₐ[k] localRing k P :=
  mapEquiv (AlgEquiv.ofAlgHom (linearSubst M.1) (linearSubst M⁻¹.1)
    (by rw [← linearSubst_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, linearSubst_one])
    (by rw [← linearSubst_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, linearSubst_one]))
    fun g => eval_linearSubst _ _ g

@[simp]
theorem linearSubstEquiv_algebraMap [Fintype σ] [DecidableEq σ] (M : Matrix.GeneralLinearGroup σ k)
    (g : MvPolynomial σ k) :
    linearSubstEquiv (P := P) M (algebraMap _ _ g) = algebraMap _ _ (linearSubst M.1 g) :=
  mapEquiv_algebraMap _ _ g

end localRing

end PlaneCurves.AffineSpace

end
