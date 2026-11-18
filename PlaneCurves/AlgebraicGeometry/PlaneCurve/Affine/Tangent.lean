/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import PlaneCurves.Algebra.BigOperators.Multiset
public import PlaneCurves.Algebra.GroupWithZero.Associated
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Multiplicity
public import PlaneCurves.RingTheory.MvPolynomial.BinaryForm.Basic
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst
public import PlaneCurves.RingTheory.Multiplicity

/-!
# Tangent lines and ordinary multiple points of affine plane curves

The tangent lines of a plane curve `F` at a point `P` are the linear factors of its leading form
`F_m` at `P` (`MvPolynomial.leadingFormAt`), a form of degree `m = m_P(F)`. A tangent line is
represented by a nonzero linear form `L` up to a nonzero scalar; the line itself is `L(X - P)`.
Its multiplicity is the multiplicity of `L` as a factor of `F_m`. The point `P` is an
*ordinary* multiple point if it is multiple and its tangents are distinct, that is, `F_m` is
squarefree.

## Main definitions

* `PlaneCurves.Affine.IsTangentAt F P L`: `L` is a nonzero linear form dividing the leading form
  of `F` at `P`.
* `PlaneCurves.Affine.tangentMultiplicity F P L`: the multiplicity of `L` in the leading form.
* `PlaneCurves.Affine.IsOrdinaryMultiplePoint F P`: `P` is a multiple point with a squarefree
  leading form.

## Main results

* `PlaneCurves.Affine.tangentMultiplicity_mul`, `PlaneCurves.Affine.tangentMultiplicity_pow`,
  `PlaneCurves.Affine.tangentMultiplicity_prod`: tangent multiplicities are additive.
* `PlaneCurves.Affine.tangentMultiplicity_linearSubst`: an invertible linear change of
  coordinates preserves tangent multiplicities.
* `PlaneCurves.Affine.IsSimplePoint.isTangentAt_iff`: at a simple point the tangent is the
  differential `F_X(P) X + F_Y(P) Y`, of multiplicity one.
* `PlaneCurves.Affine.exists_finset_isTangentAt`, `PlaneCurves.Affine.sum_tangentMultiplicity`,
  `PlaneCurves.Affine.leadingFormAt_eq_C_mul_prod_pow`: over an algebraically closed field the
  leading form is `ε ∏ⱼ Lⱼ ^ rⱼ` over the distinct tangents `Lⱼ`, with `∑ⱼ rⱼ = m_P(F)`.
* `PlaneCurves.Affine.tangentMultiplicity_eq_countP`: in a factorization of the leading form
  into tangents, the multiplicity of a tangent counts the factors associated to it.
* `PlaneCurves.Affine.isOrdinaryMultiplePoint_iff`: a multiple point is ordinary exactly when
  it has `m_P(F)` distinct tangents.
* `PlaneCurves.Affine.multiplicity_tangent_mul`: multiplicity and tangent lines of a product of
  plane curves, as in §3.1 of Fulton.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1
-/

public section

namespace PlaneCurves.Affine

open MvPolynomial

section Defs

variable {R : Type*} [CommSemiring R] {F L : MvPolynomial (Fin 2) R} {P : Fin 2 → R}

/-- The nonzero linear form `L` is *tangent* to the plane curve `F` at `P` if it divides the
leading form of `F` at `P`; the tangent line is then `L(X - P) = 0`. -/
def IsTangentAt (F : MvPolynomial (Fin 2) R) (P : Fin 2 → R) (L : MvPolynomial (Fin 2) R) :
    Prop :=
  L.IsHomogeneous 1 ∧ L ≠ 0 ∧ L ∣ F.leadingFormAt P

theorem isTangentAt_def :
    IsTangentAt F P L ↔ L.IsHomogeneous 1 ∧ L ≠ 0 ∧ L ∣ F.leadingFormAt P :=
  Iff.rfl

/-- The multiplicity of the linear form `L` as a tangent of `F` at `P`: its multiplicity as a
factor of the leading form of `F` at `P`. It is `0` when `L` is not tangent. -/
noncomputable def tangentMultiplicity (F : MvPolynomial (Fin 2) R) (P : Fin 2 → R)
    (L : MvPolynomial (Fin 2) R) : ℕ :=
  multiplicity L (F.leadingFormAt P)

theorem tangentMultiplicity_def :
    tangentMultiplicity F P L = multiplicity L (F.leadingFormAt P) :=
  (rfl)

/-- A point `P` is an *ordinary multiple point* of `F` if it is a multiple point and the leading
form of `F` at `P` is squarefree, that is, the tangents at `P` are distinct. -/
def IsOrdinaryMultiplePoint (F : MvPolynomial (Fin 2) R) (P : Fin 2 → R) : Prop :=
  IsMultiplePoint F P ∧ Squarefree (F.leadingFormAt P)

theorem isOrdinaryMultiplePoint_def :
    IsOrdinaryMultiplePoint F P ↔ IsMultiplePoint F P ∧ Squarefree (F.leadingFormAt P) :=
  Iff.rfl

@[simp]
theorem tangentMultiplicity_taylor (a : Fin 2 → R) :
    tangentMultiplicity (taylor a F) P L = tangentMultiplicity F (P + a) L := by
  simp [tangentMultiplicity_def]

@[simp]
theorem isTangentAt_taylor_iff (a : Fin 2 → R) :
    IsTangentAt (taylor a F) P L ↔ IsTangentAt F (P + a) L := by
  simp [isTangentAt_def]

end Defs

section Field

variable {k : Type*} [Field k] {F G L : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

theorem IsTangentAt.isHomogeneous (h : IsTangentAt F P L) : L.IsHomogeneous 1 :=
  h.1

theorem IsTangentAt.ne_zero (h : IsTangentAt F P L) : L ≠ 0 :=
  h.2.1

theorem IsTangentAt.dvd (h : IsTangentAt F P L) : L ∣ F.leadingFormAt P :=
  h.2.2

/-- A tangent is a prime element of `k[X, Y]`. -/
theorem IsTangentAt.prime (h : IsTangentAt F P L) : Prime L :=
  (irreducible_of_isHomogeneous_one h.1 h.2.1).prime

/-- A tangent passes through the point: the curve vanishes there. -/
theorem IsTangentAt.eval_eq_zero (h : IsTangentAt F P L) : eval P F = 0 := by
  by_contra hP
  rw [isTangentAt_def, leadingFormAt_of_eval_ne_zero hP] at h
  exact (irreducible_of_isHomogeneous_one h.1 h.2.1).not_isUnit
    (isUnit_of_dvd_unit h.2.2 ((isUnit_iff_ne_zero.2 hP).map C))

/-- A nonzero linear form has positive tangent multiplicity exactly when it is tangent. -/
theorem tangentMultiplicity_pos_iff (hF : F ≠ 0) (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) :
    0 < tangentMultiplicity F P L ↔ IsTangentAt F P L := by
  have hfin : FiniteMultiplicity L (F.leadingFormAt P) :=
    .of_not_isUnit (irreducible_of_isHomogeneous_one hL hL₀).not_isUnit (leadingFormAt_ne_zero hF)
  rw [tangentMultiplicity_def, isTangentAt_def]
  exact ⟨fun h ↦ ⟨hL, hL₀, dvd_of_multiplicity_pos h⟩, fun h ↦ multiplicity_pos_of_dvd h.2.2 hfin⟩

/-- Associated linear forms have the same tangent multiplicity. -/
theorem tangentMultiplicity_eq_of_associated {L' : MvPolynomial (Fin 2) k} (h : Associated L L') :
    tangentMultiplicity F P L = tangentMultiplicity F P L' :=
  multiplicity_eq_of_associated_left h.symm

/-- Tangent multiplicities are additive over products of curves. -/
theorem tangentMultiplicity_mul (hF : F ≠ 0) (hG : G ≠ 0) (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) :
    tangentMultiplicity (F * G) P L = tangentMultiplicity F P L + tangentMultiplicity G P L := by
  have hp := (irreducible_of_isHomogeneous_one hL hL₀).prime
  rw [tangentMultiplicity_def, leadingFormAt_mul]
  exact multiplicity_mul hp
    (.of_prime_left hp (mul_ne_zero (leadingFormAt_ne_zero hF) (leadingFormAt_ne_zero hG)))

/-- The tangent multiplicities of `F ^ n` are `n` times those of `F`. -/
theorem tangentMultiplicity_pow (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) (n : ℕ) :
    tangentMultiplicity (F ^ n) P L = n * tangentMultiplicity F P L := by
  rw [tangentMultiplicity_def, leadingFormAt_pow,
    multiplicity_pow (irreducible_of_isHomogeneous_one hL hL₀).prime, tangentMultiplicity_def]

/-- Tangent multiplicities are additive over finite products of curves. -/
theorem tangentMultiplicity_prod {ι : Type*} (s : Finset ι) {F : ι → MvPolynomial (Fin 2) k}
    (hF : ∀ i ∈ s, F i ≠ 0) (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) :
    tangentMultiplicity (∏ i ∈ s, F i) P L = ∑ i ∈ s, tangentMultiplicity (F i) P L := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, tangentMultiplicity_def, leadingFormAt_one,
      multiplicity_of_isUnit_right isUnit_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      tangentMultiplicity_mul (hF i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.2 fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)) hL hL₀,
      ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)]

/-- Tangent multiplicities do not change when the curve is multiplied by a nonzero scalar. -/
@[simp]
theorem tangentMultiplicity_smul {c : k} (hc : c ≠ 0) :
    tangentMultiplicity (c • F) P L = tangentMultiplicity F P L := by
  rw [tangentMultiplicity_def, tangentMultiplicity_def, leadingFormAt_smul, smul_eq_C_mul]
  exact multiplicity_eq_of_associated_right
    (associated_unit_mul_left _ _ ((isUnit_iff_ne_zero.2 hc).map C))

/-- An invertible linear change of coordinates preserves tangent multiplicities: the
multiplicity of `L(M X)` as a tangent of `F(M X)` at `Q` is that of `L` as a tangent of `F` at
`M Q`. -/
theorem tangentMultiplicity_linearSubst {M : Matrix (Fin 2) (Fin 2) k} (hM : IsUnit M.det)
    (F L : MvPolynomial (Fin 2) k) (Q : Fin 2 → k) :
    tangentMultiplicity (linearSubst M F) Q (linearSubst M L) =
      tangentMultiplicity F (M.mulVec Q) L := by
  rw [tangentMultiplicity_def, leadingFormAt_linearSubst hM]
  have h := multiplicity_map_eq (linearSubstAlgEquiv (Matrix.nonsingInvUnit M hM)) (a := L)
    (b := F.leadingFormAt (M.mulVec Q))
  rwa [linearSubstAlgEquiv_apply, linearSubstAlgEquiv_apply] at h

/-- An invertible linear change of coordinates moves the tangents: `L(M X)` is tangent to
`F(M X)` at `Q` exactly when `L` is tangent to `F` at `M Q`. -/
theorem isTangentAt_linearSubst_iff {M : Matrix (Fin 2) (Fin 2) k} (hM : IsUnit M.det)
    (Q : Fin 2 → k) :
    IsTangentAt (linearSubst M F) Q (linearSubst M L) ↔ IsTangentAt F (M.mulVec Q) L := by
  have hd := map_dvd_iff (linearSubstAlgEquiv (Matrix.nonsingInvUnit M hM)) (a := L)
    (b := F.leadingFormAt (M.mulVec Q))
  rw [linearSubstAlgEquiv_apply, linearSubstAlgEquiv_apply] at hd
  change linearSubst M L ∣ linearSubst M _ ↔ _ at hd
  rw [isTangentAt_def, isTangentAt_def, leadingFormAt_linearSubst hM, hd,
    map_ne_zero_iff _ (linearSubst_injective hM)]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ h.linearSubst M⟩
  simpa [linearSubst_nonsing_inv_linearSubst hM] using h.linearSubst M⁻¹

/-- At a simple point, the leading form is a tangent. -/
theorem IsSimplePoint.isTangentAt_leadingFormAt (h : IsSimplePoint F P) :
    IsTangentAt F P (F.leadingFormAt P) := by
  refine ⟨?_, leadingFormAt_ne_zero h.ne_zero, dvd_rfl⟩
  simpa [isSimplePoint_iff_orderAt_eq_one.1 h] using isHomogeneous_leadingFormAt F P

/-- At a simple point there is a unique tangent: the tangents are the nonzero multiples of the
differential `F_X(P) X + F_Y(P) Y`, which is the leading form. -/
theorem IsSimplePoint.isTangentAt_iff (h : IsSimplePoint F P) :
    IsTangentAt F P L ↔ Associated L (F.leadingFormAt P) := by
  have hT := h.isTangentAt_leadingFormAt
  refine ⟨fun hL ↦ hL.prime.irreducible.associated_of_dvd hT.prime.irreducible hL.dvd,
    fun hL ↦ ⟨?_, ?_, hL.dvd⟩⟩
  · obtain ⟨u, hu⟩ := hL.symm
    obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    rw [← hu, hr]
    simpa using hT.isHomogeneous.mul (isHomogeneous_C (Fin 2) r)
  · rintro rfl
    exact hT.ne_zero (zero_dvd_iff.1 hL.dvd)

/-- At a simple point the tangent has multiplicity one. -/
theorem IsSimplePoint.tangentMultiplicity_leadingFormAt (h : IsSimplePoint F P) :
    tangentMultiplicity F P (F.leadingFormAt P) = 1 :=
  multiplicity_self (.of_prime_left h.isTangentAt_leadingFormAt.prime
    (leadingFormAt_ne_zero h.ne_zero))

/-- In a factorization of the leading form into tangents, the multiplicity of a prime is the
number of factors associated to it. -/
theorem tangentMultiplicity_eq_countP {ε : k} (hε : ε ≠ 0)
    {u : Multiset (MvPolynomial (Fin 2) k)} (hu : ∀ L ∈ u, IsTangentAt F P L)
    (heq : F.leadingFormAt P = C ε * u.prod) {p : MvPolynomial (Fin 2) k} (hp : Prime p)
    [DecidablePred (Associated p)] :
    tangentMultiplicity F P p = u.countP (Associated p) := by
  rw [tangentMultiplicity_def, heq, multiplicity_eq_of_associated_right
    (associated_unit_mul_left _ _ ((isUnit_iff_ne_zero.2 hε).map C))]
  exact Multiset.multiplicity_prod_eq_countP hp fun L hL ↦ (hu L hL).prime.irreducible

section IsAlgClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the leading form of a nonzero curve at `P` is a nonzero
constant times a product of `m_P(F)` tangents. -/
theorem exists_leadingFormAt_eq_C_mul_prod (hF : F ≠ 0) :
    ∃ ε : k, ε ≠ 0 ∧ ∃ u : Multiset (MvPolynomial (Fin 2) k),
      (Multiset.card u : ℕ∞) = F.orderAt P ∧ (∀ L ∈ u, IsTangentAt F P L) ∧
        F.leadingFormAt P = C ε * u.prod := by
  obtain ⟨ε, hε, s, hcard, hs, heq⟩ :=
    (isHomogeneous_leadingFormAt F P).exists_eq_C_mul_prod (leadingFormAt_ne_zero hF)
  refine ⟨ε, hε, s.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1, ?_, fun L hL ↦ ?_, heq⟩
  · rw [Multiset.card_map, hcard, ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hF)]
  · obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.1 hL
    exact ⟨(isHomogeneous_C_mul_X ℓ.1 0).add (isHomogeneous_C_mul_X ℓ.2 1),
      (irreducible_C_mul_X_add_C_mul_X (hs ℓ hℓ)).ne_zero,
      heq ▸ (Multiset.dvd_prod hL).mul_left _⟩

/-- Over an algebraically closed field, a nonzero curve has finitely many tangents at `P` up to
nonzero scalars: there is a finite set of pairwise non-associated tangents such that every
tangent is associated to one of them. -/
theorem exists_finset_isTangentAt (hF : F ≠ 0) :
    ∃ s : Finset (MvPolynomial (Fin 2) k), (∀ L ∈ s, IsTangentAt F P L) ∧
      (s : Set (MvPolynomial (Fin 2) k)).Pairwise (fun L L' ↦ ¬Associated L L') ∧
      ∀ L, IsTangentAt F P L → ∃ L' ∈ s, Associated L L' := by
  classical
  obtain ⟨ε, hε, u, -, hu, heq⟩ := exists_leadingFormAt_eq_C_mul_prod (P := P) hF
  obtain ⟨s, hsu, hs, hcov⟩ := u.exists_finset_pairwise_not_associated
  refine ⟨s, fun L hL ↦ hu L (hsu L hL), hs, fun L hL ↦ ?_⟩
  have hdvd : L ∣ u.prod := by
    have := hL.dvd
    rwa [heq, (associated_unit_mul_left _ _ ((isUnit_iff_ne_zero.2 hε).map C)).dvd_iff_dvd_right]
      at this
  obtain ⟨y, hy, hLy⟩ := hL.prime.exists_mem_multiset_dvd hdvd
  obtain ⟨L', hL', hyL'⟩ := hcov y hy
  exact ⟨L', hL', (hL.prime.irreducible.associated_of_dvd (hu y hy).prime.irreducible hLy).trans
    hyL'⟩

variable {s : Finset (MvPolynomial (Fin 2) k)} (hs : ∀ L ∈ s, IsTangentAt F P L)
  (hpair : (s : Set (MvPolynomial (Fin 2) k)).Pairwise (fun L L' ↦ ¬Associated L L'))
  (hcov : ∀ L, IsTangentAt F P L → ∃ L' ∈ s, Associated L L')
include hs hpair hcov

/-- Over an algebraically closed field, the multiplicities of the distinct tangents at `P` add
up to the multiplicity `m_P(F)`. -/
theorem sum_tangentMultiplicity (hF : F ≠ 0) :
    ((∑ L ∈ s, tangentMultiplicity F P L : ℕ) : ℕ∞) = F.orderAt P := by
  classical
  obtain ⟨ε, hε, u, hcard, hu, heq⟩ := exists_leadingFormAt_eq_C_mul_prod (P := P) hF
  rw [← hcard,
    Finset.sum_congr rfl fun L hL ↦ tangentMultiplicity_eq_countP hε hu heq (hs L hL).prime,
    Multiset.sum_countP_eq_card]
  intro x hx
  obtain ⟨L, hL, hxL⟩ := hcov x (hu x hx)
  refine ⟨L, ⟨hL, hxL.symm⟩, fun L' ⟨hL', hL'x⟩ ↦ ?_⟩
  by_contra hne
  exact hpair hL' hL hne (hL'x.trans hxL)

/-- Over an algebraically closed field, the leading form of `F` at `P` is `ε ∏ⱼ Lⱼ ^ rⱼ` for a
nonzero `ε`, over the distinct tangents `Lⱼ` with their multiplicities `rⱼ`. -/
theorem leadingFormAt_eq_C_mul_prod_pow (hF : F ≠ 0) :
    ∃ ε : k, ε ≠ 0 ∧
      F.leadingFormAt P = C ε * ∏ L ∈ s, L ^ tangentMultiplicity F P L := by
  set D := ∏ L ∈ s, L ^ tangentMultiplicity F P L
  have hG₀ := leadingFormAt_ne_zero (a := P) hF
  have hD : D ∣ F.leadingFormAt P := by
    refine Finset.prod_dvd_of_isRelPrime (fun L hL L' hL' hne ↦ ?_)
      fun L _ ↦ pow_multiplicity_dvd _ _
    refine IsRelPrime.pow ((hs L hL).prime.irreducible.isRelPrime_iff_not_dvd.2 fun hd ↦ ?_)
    exact hpair hL hL' hne
      ((hs L hL).prime.irreducible.associated_of_dvd (hs L' hL').prime.irreducible hd)
  obtain ⟨H, hH⟩ := hD
  have hD₀ : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun L hL ↦ pow_ne_zero _ (hs L hL).ne_zero
  have hH₀ : H ≠ 0 := by rintro rfl; exact hG₀ (by simpa using hH)
  have hdeg : D.totalDegree = (F.orderAt P).toNat := by
    have hDh : D.IsHomogeneous (∑ L ∈ s, tangentMultiplicity F P L) :=
      IsHomogeneous.prod _ _ _ fun L hL ↦ by simpa using (hs L hL).isHomogeneous.pow _
    rw [hDh.totalDegree hD₀, ← ENat.toNat_natCast (∑ L ∈ s, tangentMultiplicity F P L),
      sum_tangentMultiplicity hs hpair hcov hF]
  have hH0 : H.totalDegree = 0 := by
    have := congrArg totalDegree hH
    rw [(isHomogeneous_leadingFormAt F P).totalDegree hG₀, totalDegree_mul_of_isDomain hD₀ hH₀,
      hdeg] at this
    omega
  have hHC := totalDegree_eq_zero_iff_eq_C.1 hH0
  refine ⟨H.coeff 0, fun hc ↦ hH₀ (by rw [hHC, hc, map_zero]), ?_⟩
  rw [hH, mul_comm, ← hHC]

/-- Over an algebraically closed field, a multiple point is ordinary exactly when it has
`m_P(F)` distinct tangents. -/
theorem isOrdinaryMultiplePoint_iff (hF : F ≠ 0) :
    IsOrdinaryMultiplePoint F P ↔ IsMultiplePoint F P ∧ (s.card : ℕ∞) = F.orderAt P := by
  classical
  have hG₀ := leadingFormAt_ne_zero (a := P) hF
  have hpos : ∀ L ∈ s, 1 ≤ tangentMultiplicity F P L := fun L hL ↦
    (tangentMultiplicity_pos_iff hF (hs L hL).isHomogeneous (hs L hL).ne_zero).2 (hs L hL)
  have hsq : Squarefree (F.leadingFormAt P) ↔ ∀ L ∈ s, tangentMultiplicity F P L = 1 := by
    refine ⟨fun h L hL ↦ le_antisymm ?_ (hpos L hL), fun h ↦ ?_⟩
    · by_contra! h2
      refine (hs L hL).prime.not_isUnit (h L ?_)
      rw [← sq]
      exact (pow_dvd_pow L h2).trans (pow_multiplicity_dvd _ _)
    · obtain ⟨ε, hε, u, -, hu, heq⟩ := exists_leadingFormAt_eq_C_mul_prod (P := P) hF
      refine (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hG₀).2 fun x hx hxx ↦ ?_
      have hfin : FiniteMultiplicity x (F.leadingFormAt P) := .of_not_isUnit hx.not_isUnit hG₀
      have h2 : 2 ≤ tangentMultiplicity F P x := by
        rw [tangentMultiplicity_def, ← hfin.pow_dvd_iff_le_multiplicity, sq]
        exact hxx
      obtain ⟨y, hy, hxy⟩ := Multiset.countP_pos.1
        ((tangentMultiplicity_eq_countP hε hu heq hx.prime ▸ h2 :
          2 ≤ u.countP (Associated x)).trans_lt' zero_lt_two)
      obtain ⟨L, hL, hyL⟩ := hcov y (hu y hy)
      have := tangentMultiplicity_eq_of_associated (F := F) (P := P) (hxy.trans hyL)
      have := h L hL
      omega
  have hsum := sum_tangentMultiplicity hs hpair hcov hF
  rw [isOrdinaryMultiplePoint_def, hsq, ← hsum, Nat.cast_inj, Finset.card_eq_sum_ones,
    Finset.sum_eq_sum_iff_of_le hpos]
  simp only [eq_comm (a := 1)]

end IsAlgClosed

/-- **Multiplicity and tangent lines of a product of plane curves.** Let `k` be algebraically
closed, `F`, `G` nonzero plane curves and `P` a point. Then `m_P(FG) = m_P(F) + m_P(G)`, the
leading form of `FG` at `P` is the product of the leading forms, and the tangent multiplicities
add. For a product `∏ᵢ Hᵢ ^ eᵢ` of nonzero curves (such as the factorization of a curve into its
components), `m_P = ∑ᵢ eᵢ m_P(Hᵢ)`, a line tangent to `Hᵢ` with multiplicity `rᵢ` is tangent to
the product with multiplicity `∑ᵢ eᵢ rᵢ`, and `P` is a simple point of the product exactly when
it lies on just one factor `Hᵢ`, with `eᵢ = 1`, and is simple on it. Finally, the leading form of
`F` at `P` is `ε ∏ⱼ Lⱼ ^ rⱼ` over the distinct tangents `Lⱼ`, with `∑ⱼ rⱼ = m_P(F)`.

Milestone: *Multiplicity and tangent lines of a product of plane curves*. -/
theorem multiplicity_tangent_mul [IsAlgClosed k] (hF : F ≠ 0) (hG : G ≠ 0) {ι : Type*}
    (s : Finset ι) (H : ι → MvPolynomial (Fin 2) k) (e : ι → ℕ) (hH : ∀ i ∈ s, H i ≠ 0) :
    (F * G).orderAt P = F.orderAt P + G.orderAt P ∧
    (F * G).leadingFormAt P = F.leadingFormAt P * G.leadingFormAt P ∧
    (∀ L : MvPolynomial (Fin 2) k, L.IsHomogeneous 1 → L ≠ 0 →
      tangentMultiplicity (F * G) P L = tangentMultiplicity F P L + tangentMultiplicity G P L) ∧
    (∏ i ∈ s, H i ^ e i).orderAt P = ∑ i ∈ s, e i * (H i).orderAt P ∧
    (∀ L : MvPolynomial (Fin 2) k, L.IsHomogeneous 1 → L ≠ 0 →
      tangentMultiplicity (∏ i ∈ s, H i ^ e i) P L =
        ∑ i ∈ s, e i * tangentMultiplicity (H i) P L) ∧
    (IsSimplePoint (∏ i ∈ s, H i ^ e i) P ↔
      ∃ i ∈ s, e i = 1 ∧ IsSimplePoint (H i) P ∧ ∀ j ∈ s, j ≠ i → eval P (H j ^ e j) ≠ 0) ∧
    ∃ T : Finset (MvPolynomial (Fin 2) k), (∀ L ∈ T, IsTangentAt F P L) ∧
      (T : Set (MvPolynomial (Fin 2) k)).Pairwise (fun L L' ↦ ¬Associated L L') ∧
      (∀ L, IsTangentAt F P L → ∃ L' ∈ T, Associated L L') ∧
      (∃ ε : k, ε ≠ 0 ∧ F.leadingFormAt P = C ε * ∏ L ∈ T, L ^ tangentMultiplicity F P L) ∧
      ((∑ L ∈ T, tangentMultiplicity F P L : ℕ) : ℕ∞) = F.orderAt P := by
  refine ⟨orderAt_mul F G P, leadingFormAt_mul F G P,
    fun L hL hL₀ ↦ tangentMultiplicity_mul hF hG hL hL₀, ?_, fun L hL hL₀ ↦ ?_,
    isSimplePoint_prod_pow_iff s H e, ?_⟩
  · simp [orderAt_prod, orderAt_pow, nsmul_eq_mul]
  · rw [tangentMultiplicity_prod s (fun i hi ↦ pow_ne_zero _ (hH i hi)) hL hL₀]
    simp [tangentMultiplicity_pow hL hL₀]
  · obtain ⟨T, hT, hpair, hcov⟩ := exists_finset_isTangentAt (P := P) hF
    exact ⟨T, hT, hpair, hcov, leadingFormAt_eq_C_mul_prod_pow hT hpair hcov hF,
      sum_tangentMultiplicity hT hpair hcov hF⟩

end Field

end PlaneCurves.Affine

end
