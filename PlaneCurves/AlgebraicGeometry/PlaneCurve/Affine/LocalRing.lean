/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import PlaneCurves.AlgebraicGeometry.AffineSpace.LocalRing
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Tangent
public import PlaneCurves.RingTheory.DiscreteValuationRing.Colength
public import PlaneCurves.RingTheory.MvPolynomial.LinearForm

/-!
# The local ring of a plane curve at a point

The local ring of a plane curve `F` at a point `P` is `𝒪_P(𝔸²)/(F)`, the quotient of the local
ring `𝒪_P(𝔸²)` (`PlaneCurves.AffineSpace.localRing`) by the image of `F`; for irreducible `F` it
is Fulton's `𝒪_P(F)` (Problem 2.44). This file shows that it is a discrete valuation ring exactly
at the simple points of `F`, and computes the order of a curve `G` smooth at `P`, such as a line
through `P`: it is one when `G` is not tangent to `F` at `P` and at least two when it is.

The proof goes through regular local rings, for any `F`, possibly reducible or non-reduced:
`𝒪_P(𝔸²)` is regular of dimension two, so `𝒪_P(𝔸²)/(F)` has dimension one and is regular exactly
when `F ∉ 𝔪²`, that is, when `m_P(F) = 1`; a regular local ring of dimension one is a discrete
valuation ring.

## Main results

* `PlaneCurves.Affine.isRegularLocalRing_quotient_iff`, `PlaneCurves.Affine.ringKrullDim_quotient`:
  for `F ≠ 0` with `F(P) = 0`, `𝒪_P(𝔸²)/(F)` has dimension one, and is regular iff `P` is a
  simple point of `F`.
* `PlaneCurves.Affine.exists_isDiscreteValuationRing_quotient_iff`,
  `PlaneCurves.Affine.isDiscreteValuationRing_quotient_iff`: for `F(P) = 0`, `𝒪_P(𝔸²)/(F)` is a
  discrete valuation ring iff `P` is a simple point of `F`.
* `PlaneCurves.Affine.algebraMap_mem_maximalIdeal_sq_sup_span_iff`: `G ∈ 𝔪² + (F)` in
  `𝒪_P(𝔸²)` iff the differential of `G` at `P` is a multiple of that of `F`;
  `PlaneCurves.Affine.IsSimplePoint.isTangentAt_leadingFormAt_iff`: at a simple point, that is
  tangency for a curve `G` smooth at `P`.
* `PlaneCurves.Affine.IsSimplePoint.irreducible_mk_iff`,
  `PlaneCurves.Affine.IsSimplePoint.ord_mk_eq_one_iff`,
  `PlaneCurves.Affine.IsSimplePoint.two_le_ord_mk_iff`,
  `PlaneCurves.Affine.IsSimplePoint.ord_mk_eq_top_of_dvd`: at a simple point `P` of `F`, a curve
  `G` smooth at `P` is a uniformizing parameter of `𝒪_P(𝔸²)/(F)`, of order one, iff it is not
  tangent to `F` at `P`; it has order at least two iff it is tangent, and order `⊤` if it divides
  `F`.
* `PlaneCurves.Affine.isDiscreteValuationRing_quotient_iff_and_ord`: all of these together, in
  the form of Theorem 1 of §3.2 of Fulton.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.2, Theorem 1
-/

public section

open MvPolynomial IsLocalRing Ideal TauCeti

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- For `F ≠ 0` with `F(P) = 0`, the local ring `𝒪_P(𝔸²)/(F)` is regular iff `P` is a simple point
of `F`. -/
theorem isRegularLocalRing_quotient_iff (hF : eval P F = 0) (hF0 : F ≠ 0) :
    IsRegularLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ↔
      IsSimplePoint F P := by
  rw [IsRegularLocalRing.quotient_span_singleton_iff
      (localRing.algebraMap_mem_maximalIdeal_iff.2 hF)
      ((map_ne_zero_iff _ (localRing.algebraMap_injective k P)).2 hF0),
    localRing.algebraMap_mem_maximalIdeal_pow_iff, Nat.cast_ofNat, ← isMultiplePoint_def,
    isMultiplePoint_iff_not_isSimplePoint, not_and, not_not]
  exact ⟨fun h ↦ h hF, fun h _ ↦ h⟩

/-- For `F ≠ 0` with `F(P) = 0`, the local ring `𝒪_P(𝔸²)/(F)` has dimension one. -/
theorem ringKrullDim_quotient (hF : eval P F = 0) (hF0 : F ≠ 0) :
    ringKrullDim (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) = 1 :=
  ringKrullDim_quotient_span_singleton_eq_one (by simp [localRing.ringKrullDim_eq])
    (localRing.algebraMap_mem_maximalIdeal_iff.2 hF)
    (mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (localRing.algebraMap_injective k P)).2 hF0))

/-- At a simple point `P` of `F`, the local ring `𝒪_P(𝔸²)/(F)` is regular. -/
theorem IsSimplePoint.isRegularLocalRing_quotient (h : IsSimplePoint F P) :
    IsRegularLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) :=
  (isRegularLocalRing_quotient_iff h.eval_eq_zero h.ne_zero).2 h

/-- At a simple point `P` of `F`, the local ring `𝒪_P(𝔸²)/(F)` is a discrete valuation ring.
It is a domain by `TauCeti.IsRegularLocalRing.isDomain` and
`IsSimplePoint.isRegularLocalRing_quotient`. -/
theorem IsSimplePoint.isDiscreteValuationRing (h : IsSimplePoint F P)
    [IsDomain (localRing k P ⧸ span {algebraMap _ (localRing k P) F})] :
    IsDiscreteValuationRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) := by
  have := h.isRegularLocalRing_quotient
  exact IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.2
    (ringKrullDim_quotient h.eval_eq_zero h.ne_zero)

/-- **Simple points are those with a discrete valuation local ring**, for any plane curve `F`
through `P`: `𝒪_P(𝔸²)/(F)` is a discrete valuation ring iff `P` is a simple point of `F`. -/
theorem exists_isDiscreteValuationRing_quotient_iff (hF : eval P F = 0) :
    (∃ _ : IsDomain (localRing k P ⧸ span {algebraMap _ (localRing k P) F}),
      IsDiscreteValuationRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F})) ↔
      IsSimplePoint F P := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hF0 : F ≠ 0 := by
      rintro rfl
      have h1 := IsDiscreteValuationRing.ringKrullDim_eq_one
        (R := localRing k P ⧸ span {algebraMap (MvPolynomial (Fin 2) k) (localRing k P) 0})
      rw [map_zero, span_singleton_eq_bot.2 rfl,
        ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), localRing.ringKrullDim_eq] at h1
      simp at h1
    exact (isRegularLocalRing_quotient_iff hF hF0).1 inferInstance
  · have := h.isRegularLocalRing_quotient
    let _ : IsDomain (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) :=
      IsRegularLocalRing.isDomain (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
    exact ⟨inferInstance, h.isDiscreteValuationRing⟩

/-- When `𝒪_P(𝔸²)/(F)` is a domain, for instance when `F` is irreducible (so that it is Fulton's
`𝒪_P(F)`), it is a discrete valuation ring iff `P` is a simple point of `F`. -/
theorem isDiscreteValuationRing_quotient_iff (hF : eval P F = 0)
    [IsDomain (localRing k P ⧸ span {algebraMap _ (localRing k P) F})] :
    IsDiscreteValuationRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ↔
      IsSimplePoint F P :=
  ⟨fun h ↦ (exists_isDiscreteValuationRing_quotient_iff hF).1 ⟨inferInstance, h⟩,
    fun h ↦ h.isDiscreteValuationRing⟩

/-- For `F(P) = 0`, the image of `G` in `𝒪_P(𝔸²)` lies in `𝔪² + (F)` iff `G(P) = 0` and the
differential of `G` at `P` is a multiple of that of `F`. -/
theorem algebraMap_mem_maximalIdeal_sq_sup_span_iff (hF : eval P F = 0) :
    algebraMap _ (localRing k P) G ∈
        maximalIdeal (localRing k P) ^ 2 ⊔ span {algebraMap _ (localRing k P) F} ↔
      eval P G = 0 ∧ ∃ c : k, ∀ i, eval P (pderiv i G) = c * eval P (pderiv i F) := by
  constructor
  · intro h
    have hG : eval P G = 0 := localRing.algebraMap_mem_maximalIdeal_iff.1 <|
      sup_le (pow_le_self two_ne_zero)
        ((span_singleton_le_iff_mem _).2 (localRing.algebraMap_mem_maximalIdeal_iff.2 hF)) h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := mem_span_singleton'.1 hz
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (vanishingIdeal k {P} : Ideal (MvPolynomial (Fin 2) k)).primeCompl a
    have hmem : algebraMap _ (localRing k P) (s.1 * G - b * F) ∈
        maximalIdeal (localRing k P) ^ 2 := by
      have : algebraMap _ (localRing k P) (s.1 * G - b * F) = algebraMap _ _ s.1 * y := by
        dsimp only at hyz
        rw [map_sub, map_mul, map_mul, ← hyz]
        linear_combination (algebraMap _ (localRing k P) F) *
          IsLocalization.mk'_spec' (localRing k P) b s
      rw [this]
      exact Ideal.mul_mem_left _ _ hy
    rw [localRing.algebraMap_mem_maximalIdeal_pow_iff] at hmem
    have hs := localRing.eval_ne_zero s
    refine ⟨hG, eval P b / eval P s.1, fun i ↦ ?_⟩
    have := (isMultiplePoint_iff_eval_pderiv.1 (isMultiplePoint_def.2 (by exact_mod_cast hmem))).2 i
    simp only [map_sub, Derivation.leibniz, map_add, smul_eq_mul, map_mul, hG, hF] at this
    field_simp
    linear_combination this
  · rintro ⟨hG, c, hc⟩
    have h2 : 2 ≤ (G - C c * F).orderAt P :=
      isMultiplePoint_def.1 <| isMultiplePoint_iff_eval_pderiv.2
      ⟨by simp [hG, hF], fun i ↦ by simp [hc i]⟩
    have hmem := (localRing.algebraMap_mem_maximalIdeal_pow_iff (P := P) (f := G - C c * F)
      (r := 2)).2
      (by exact_mod_cast h2)
    have : algebraMap _ (localRing k P) G = algebraMap _ _ (G - C c * F) +
        algebraMap (MvPolynomial (Fin 2) k) (localRing k P) (C c) * algebraMap _ _ F := by simp
    rw [this]
    exact Submodule.add_mem_sup hmem (mem_span_singleton'.2 ⟨_, rfl⟩)

/-- At a simple point of `F`, a polynomial `G` smooth at `P` is tangent to `F` iff the
differential of `G` at `P` is a multiple of that of `F`. -/
theorem IsSimplePoint.isTangentAt_leadingFormAt_iff (hF : IsSimplePoint F P)
    (hG : IsSimplePoint G P) :
    IsTangentAt F P (G.leadingFormAt P) ↔
      ∃ c : k, ∀ i, eval P (pderiv i G) = c * eval P (pderiv i F) := by
  have hlin : ∀ {H : MvPolynomial (Fin 2) k}, IsSimplePoint H P →
      H.leadingFormAt P = ∑ i, C (eval P (pderiv i H)) * X i := fun hH ↦ by
    simp [hH.leadingFormAt_eq, smul_eq_C_mul]
  rw [hF.isTangentAt_iff, hlin hG, hlin hF, associated_sum_C_mul_X_iff]
  refine ⟨fun ⟨c, _, h⟩ ↦ ⟨c, h⟩, fun ⟨c, h⟩ ↦ ⟨c, ?_, h⟩⟩
  rintro rfl
  obtain ⟨i, hi⟩ := (isSimplePoint_def.1 hG).2
  exact hi (by simpa using h i)

/-! ### Orders at a simple point -/

section RegularDimOne

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

private theorem natCast_le_ord_iff (hR : ringKrullDim R = 1) (n : ℕ) (x : R) :
    (n : ℕ∞) ≤ Ring.ord R x ↔ x ∈ maximalIdeal R ^ n := by
  have := IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.2 hR
  rw [Ring.ord_eq_addVal, TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]

private theorem irreducible_iff_ord_eq_one (hR : ringKrullDim R = 1) (x : R) :
    Irreducible x ↔ Ring.ord R x = 1 := by
  have := IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.2 hR
  rw [Ring.ord_eq_addVal, TauCeti.IsDiscreteValuationRing.addVal_eq_one_iff_irreducible]

private theorem ord_zero_eq_top (hR : ringKrullDim R = 1) : Ring.ord R 0 = ⊤ := by
  have := IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.2 hR
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]

end RegularDimOne

private theorem ENat.eq_one_iff_one_le_and_not_two_le (v : ℕ∞) : v = 1 ↔ 1 ≤ v ∧ ¬ 2 ≤ v := by
  induction v using ENat.recTopCoe with
  | top => simp
  | coe n =>
    norm_cast
    omega

/-- At a simple point `P` of `F`, a curve `G` smooth at `P` has order at least two in
`𝒪_P(𝔸²)/(F)` iff it is tangent to `F` at `P`. Equivalently, its image lies in `𝔪²`. -/
theorem IsSimplePoint.two_le_ord_mk_iff (hF : IsSimplePoint F P) (hG : IsSimplePoint G P) :
    2 ≤ Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G)) ↔
      IsTangentAt F P (G.leadingFormAt P) := by
  have := hF.isRegularLocalRing_quotient
  rw [← Nat.cast_ofNat, natCast_le_ord_iff
      (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
      (ringKrullDim_quotient hF.eval_eq_zero hF.ne_zero),
    ← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
    mem_quotient_iff_mem_sup, algebraMap_mem_maximalIdeal_sq_sup_span_iff hF.eval_eq_zero,
    hF.isTangentAt_leadingFormAt_iff hG, and_iff_right hG.eval_eq_zero]

/-- At a simple point `P` of `F`, the image of a curve `G` vanishing at `P` lies in the maximal
ideal of `𝒪_P(𝔸²)/(F)`, so it has order at least one. -/
theorem IsSimplePoint.one_le_ord_mk (hF : IsSimplePoint F P) (hG : eval P G = 0) :
    1 ≤ Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G)) := by
  have := hF.isRegularLocalRing_quotient
  rw [← Nat.cast_one, natCast_le_ord_iff
      (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
      (ringKrullDim_quotient hF.eval_eq_zero hF.ne_zero),
    pow_one, ← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  exact mem_map_of_mem _ (localRing.algebraMap_mem_maximalIdeal_iff.2 hG)

/-- At a simple point `P` of `F`, a curve `G` smooth at `P` has order one in `𝒪_P(𝔸²)/(F)` iff it
is not tangent to `F` at `P`. -/
theorem IsSimplePoint.ord_mk_eq_one_iff (hF : IsSimplePoint F P) (hG : IsSimplePoint G P) :
    Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G)) = 1 ↔
      ¬ IsTangentAt F P (G.leadingFormAt P) := by
  rw [ENat.eq_one_iff_one_le_and_not_two_le, hF.two_le_ord_mk_iff hG,
    and_iff_right (hF.one_le_ord_mk hG.eval_eq_zero)]

/-- At a simple point `P` of `F`, a curve `G` smooth at `P`, such as a line through `P`, is a
uniformizing parameter of the discrete valuation ring `𝒪_P(𝔸²)/(F)` iff it is not tangent to `F`
at `P`. -/
theorem IsSimplePoint.irreducible_mk_iff (hF : IsSimplePoint F P) (hG : IsSimplePoint G P) :
    Irreducible (Ideal.Quotient.mk (span {algebraMap _ (localRing k P) F})
        (algebraMap _ (localRing k P) G)) ↔
      ¬ IsTangentAt F P (G.leadingFormAt P) := by
  have := hF.isRegularLocalRing_quotient
  rw [irreducible_iff_ord_eq_one
      (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
      (ringKrullDim_quotient hF.eval_eq_zero hF.ne_zero),
    hF.ord_mk_eq_one_iff hG]

/-- At a simple point `P` of `F`, a component `G` of `F` through `P` has order `⊤` in
`𝒪_P(𝔸²)/(F)`: its image is zero. -/
theorem IsSimplePoint.ord_mk_eq_top_of_dvd (hF : IsSimplePoint F P) (hG : eval P G = 0)
    (hGF : G ∣ F) :
    Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G)) = ⊤ := by
  have hzero : Ideal.Quotient.mk (span {algebraMap _ (localRing k P) F})
      (algebraMap _ (localRing k P) G) = 0 := by
    obtain ⟨H, rfl⟩ := hGF
    have hH : eval P H ≠ 0 := by
      intro hH0
      have h1 := isSimplePoint_iff_orderAt_eq_one.1 hF
      rw [orderAt_mul] at h1
      have := add_le_add (Order.one_le_iff_pos.2 (orderAt_pos_iff.2 hG))
        (Order.one_le_iff_pos.2 (orderAt_pos_iff.2 hH0))
      rw [h1] at this
      norm_num at this
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul,
      span_singleton_mul_right_unit (localRing.isUnit_algebraMap_iff.2 hH)]
    exact mem_span_singleton_self _
  have := hF.isRegularLocalRing_quotient
  rw [hzero, ord_zero_eq_top
      (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
      (ringKrullDim_quotient hF.eval_eq_zero hF.ne_zero)]

/-- **Simple points of a plane curve are those with a discrete valuation local ring.** Let `F` be
a plane curve over a field `k`, possibly reducible or non-reduced, and `P` a point of `F`. Write
`𝒪 = 𝒪_P(𝔸²)/(F)` for its local ring at `P`, which is `𝒪_P(F)` when `F` is irreducible, and
`ord_P^F = Ring.ord 𝒪` (the length of `𝒪/(z)`, which is the valuation when `𝒪` is a discrete
valuation ring, by `Ring.ord_eq_addVal`).

1. `𝒪` is a discrete valuation ring iff `P` is a simple point of `F`.
2. Let `P` be simple and `L` a curve smooth at `P`, such as a line `aX + bY + c` through `P`
   (`isSimplePoint_of_totalDegree_eq_one`). Then `L` is a uniformizing parameter of `𝒪` iff it is
   not tangent to `F` at `P`; `ord_P^F(L) = 1` iff `L` is not tangent to `F` at `P`, and
   `ord_P^F(L) ≥ 2` iff it is; and `ord_P^F(L) = ⊤` if `L` is a component of `F`.

Milestone: *Simple points of a plane curve are those with a discrete valuation local ring*. -/
theorem isDiscreteValuationRing_quotient_iff_and_ord (hF : eval P F = 0) :
    ((∃ _ : IsDomain (localRing k P ⧸ span {algebraMap _ (localRing k P) F}),
      IsDiscreteValuationRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F})) ↔
        IsSimplePoint F P) ∧
    (IsSimplePoint F P → ∀ L : MvPolynomial (Fin 2) k, IsSimplePoint L P →
      (Irreducible (Ideal.Quotient.mk (span {algebraMap _ (localRing k P) F})
          (algebraMap _ (localRing k P) L)) ↔ ¬ IsTangentAt F P (L.leadingFormAt P)) ∧
      (Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
          (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) L)) = 1 ↔
        ¬ IsTangentAt F P (L.leadingFormAt P)) ∧
      (2 ≤ Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
          (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) L)) ↔
        IsTangentAt F P (L.leadingFormAt P)) ∧
      (L ∣ F → Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
          (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) L)) = ⊤)) :=
  ⟨exists_isDiscreteValuationRing_quotient_iff hF, fun hP _ hL ↦
    ⟨hP.irreducible_mk_iff hL, hP.ord_mk_eq_one_iff hL, hP.two_le_ord_mk_iff hL,
      hP.ord_mk_eq_top_of_dvd hL.eval_eq_zero⟩⟩

end PlaneCurves.Affine

end
